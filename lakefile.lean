import Lake
open Lake DSL

package curtis where
  version := v!"0.1.0"

-- The library lives in several top-level directories (there is no single
-- root module), so it is described by globs: TVL.*, Engine.*, Opts.* and
-- Test.* submodules.
@[default_target]
lean_lib Curtis where
  globs := #[.submodules `TVL, .submodules `Engine, .submodules `Opts,
             .submodules `Test]

@[default_target]
lean_exe curtis where
  root := `Main

-- ============================================================================
-- Test driver (`lake test` is a built-in Lake command: it finds the script
-- marked with @[test_driver] and passes it the arguments after --)
--
--   lake test -- Unit   -- only the Unit tests
--   lake test -- E2E    -- only the E2E tests
--   lake test -- all    -- all tests
--   lake test           -- usage help
--
-- The same without `--`: lake run test Unit / E2E / all
--
-- Every test module is executed as follows:
--   1. lake build <module>  -- rebuilds stale dependencies;
--   2. lake env lean <file> -- re-runs every #eval and prints its output.
-- Step 2 is needed because lake build caches compiled modules and stays
-- silent on repeated runs -- while we want to see the test output every
-- time. A module counts as failed when either step exits with an error.
-- A failed CHECK (#assert!, expectVerify, pattern 3 of the cheat sheet in
-- Test/Harness.lean) is told apart from a compile error by the
-- "test failed:" prefix in the error message.
-- ============================================================================

-- Test suites: name -> module list. New tests are registered here.
-- How to write the checks themselves (three patterns) -- see the cheat
-- sheet at the top of Test/Harness.lean.
def testSuites : List (String × List String) :=
  [ ("Unit", ["Test.Unit.Opts.POR", "Test.Unit.TVIR", "Test.Unit.TVL",
              "Test.Unit.Fair"]),
    ("E2E",  ["Test.E2E.LTL.Simple",
              "Test.E2E.CTL.Simple",
              "Test.E2E.Fair.Simple"]) ]

-- Module name -> file path:
-- Test.Unit.Opts.POR -> Test/Unit/Opts/POR.lean
def moduleToFile (moduleName : String) : String :=
  String.intercalate "/" (moduleName.splitOn ".") ++ ".lean"

@[test_driver]
script test (args) do
  if args.isEmpty then
    IO.println ("Usage: lake test <suite>...\n" ++
      "Suites: " ++ String.intercalate ", " ((testSuites.map (·.1)) ++ ["all"]))
    return 1
  -- Arguments -> list of (suite, module). "all" = every suite in order.
  let mut selected : List (String × String) := []
  for arg in args do
    let a := arg.toLower
    if a == "all" then
      selected := selected ++ testSuites.flatMap (fun (suite, mods) => mods.map (suite, ·))
    else
      match testSuites.find? (fun (suite, _) => suite.toLower == a) with
      | some (suite, mods) => selected := selected ++ mods.map (suite, ·)
      | none =>
        IO.eprintln s!"Unknown test suite: '{arg}'"
        return 1
  let mut failed := 0
  for (suite, moduleName) in selected do
    IO.println s!"=== [{suite}] {moduleName} ==="
    let build ← IO.Process.output { cmd := "lake", args := #["build", moduleName] }
    if build.exitCode != 0 then
      IO.print build.stdout
      IO.eprintln build.stderr
      -- a failed check also fails the build, so look at the prefix
      let why :=
        if (build.stdout ++ build.stderr).contains "test failed:"
        then "test failed" else "compile error"
      IO.println s!"FAIL {moduleName} ({why}, see output above)"
      failed := failed + 1
      continue
    let run ← IO.Process.output
      { cmd := "lake", args := #["env", "lean", moduleToFile moduleName] }
    IO.print run.stdout
    if run.exitCode != 0 then
      IO.eprintln run.stderr
      let why :=
        if (run.stdout ++ run.stderr).contains "test failed:"
        then "test failed" else "compile error"
      IO.println s!"FAIL {moduleName} ({why}, see output above)"
      failed := failed + 1
    else
      IO.println s!"PASS {moduleName}"
  if failed == 0 then
    IO.println s!"Tests: {selected.length}/{selected.length} passed"
    return 0
  else
    IO.println s!"Tests: {selected.length - failed}/{selected.length} passed, failed: {failed}"
    return 1

-- ============================================================================
-- Installation (lake run install): expose the built curtis binary on the
-- PATH through a wrapper in ~/.local/bin, as the TVL docs describe:
--   #!/bin/bash
--   exec <repo>/.lake/build/bin/curtis "$@"
-- The wrapper points into .lake, so it follows every lake build and never
-- goes stale. lake run uninstall removes it again (only if it really is
-- our wrapper, not some other file named curtis).
-- ============================================================================

script install (_args) do
  let exe := ".lake/build/bin/curtis"
  unless ← System.FilePath.pathExists exe do
    IO.eprintln "install: curtis is not built yet -- run lake build first"
    return 1
  let some home ← IO.getEnv "HOME"
    | do IO.eprintln "install: HOME is not set"; return 1
  let binDir := s!"{home}/.local/bin"
  IO.FS.createDirAll binDir
  let root ← IO.currentDir
  let binTarget := s!"{root}/{exe}"
  let wrapper := s!"{binDir}/curtis"
  IO.FS.writeFile wrapper s!"#!/bin/bash\nexec {binTarget} \"$@\"\n"
  -- Lean IO cannot change the file mode, so go through chmod.
  let chmod ← IO.Process.output { cmd := "chmod", args := #["+x", wrapper] }
  if chmod.exitCode != 0 then
    IO.eprintln s!"install: chmod failed: {chmod.stderr}"
    return 1
  IO.println s!"installed: {wrapper} -> {binTarget}"
  if let some path ← IO.getEnv "PATH" then
    unless path.splitOn ":" |>.contains binDir do
      IO.println s!"note: {binDir} is not on your PATH -- add 'export PATH=\"{binDir}:$PATH\"' to ~/.profile"
  return 0

script uninstall (_args) do
  let some home ← IO.getEnv "HOME"
    | do IO.eprintln "uninstall: HOME is not set"; return 1
  let wrapper := s!"{home}/.local/bin/curtis"
  unless ← System.FilePath.pathExists wrapper do
    IO.println s!"uninstall: {wrapper} does not exist, nothing to do"
    return 0
  let contents ← IO.FS.readFile wrapper
  if contents.startsWith "#!/bin/bash" && contents.contains "/.lake/build/bin/curtis" then
    IO.FS.removeFile wrapper
    IO.println s!"uninstalled: {wrapper}"
    return 0
  else
    IO.eprintln s!"uninstall: {wrapper} is not a curtis wrapper, leaving it alone"
    return 1
