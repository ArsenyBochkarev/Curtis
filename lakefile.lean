import Lake
open Lake DSL

package tvl_checker where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib TVLChecker

@[default_target]
lean_exe tvl_checker where
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
-- TVLChecker/Test/Harness.lean) is told apart from a compile error by the
-- "test failed:" prefix in the error message.
-- ============================================================================

-- Test suites: name -> module list. New tests are registered here.
-- How to write the checks themselves (three patterns) -- see the cheat
-- sheet at the top of TVLChecker/Test/Harness.lean.
def testSuites : List (String × List String) :=
  [ ("Unit", ["TVLChecker.Test.Unit.Opts.POR"]),
    ("E2E",  ["TVLChecker.Test.E2E.LTL.Simple",
              "TVLChecker.Test.E2E.CTL.Simple"]) ]

-- Module name -> file path:
-- TVLChecker.Test.Unit.Opts.POR -> TVLChecker/Test/Unit/Opts/POR.lean
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
