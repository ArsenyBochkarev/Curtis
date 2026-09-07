import TVL.Sema

-- ============================================================================
-- HOW TO ADD YOUR OWN TESTS (cheat sheet)
--
-- A test is an ordinary command in a Lean file that produces a compile
-- error when the check fails. Three patterns, from simple to detailed:
--
-- 1. Boolean condition:
--        #assert! porTestsOk
--    Silent on success, throws "assertion failed" on failure.
--
-- 2. Verify a formula on a model (verdict; counterexample on failure):
--        #eval expectVerify initialStateGen propSafety false
--    (model, formula, expected verdict; expectVerify is defined below)
--
-- 3. Arbitrary function, with details shown on failure:
--        #eval show IO Unit from
--          unless (myFunc x) == expected do
--            throw (IO.userError s!"test failed: myFunc: expected {expected}, got {myFunc x}")
--
-- The "test failed:" prefix is a contract with the test driver
-- (lakefile.lean): it tells a failed check apart from a compile error.
-- Start the message of any custom throw with it.
--
-- Test files live in Test/... (module names Test.*)
-- and are registered in testSuites in lakefile.lean -- after that they run
-- via  lake test -- <suite>.
-- ============================================================================

-- Helper for building the initial state
def mkInitialState (graphs : List (String × ActorGraph)) (queueNames : List String) : State := {
  queues       := queueNames.map (fun q => (q, [])),
  guardVars    := [],
  actorThreads := graphs.map (fun (name, _) => (name, ([0], none))),
  actorGraphs  := graphs
}

class Verifyiable (logic : Type) where
  verifyAndExplain : State → logic → Bool × Option (List String)

-- E2E check of a formula: compare the verdict of verifyAndExplain with the
-- expected one. Silent when they match, an error with the verdict and the
-- counterexample otherwise (the test driver sees it and marks the module
-- FAIL). Usage: #eval expectVerify model formula expectedVerdict
def expectVerify {logic : Type} [Verifyiable logic]
    (startState : State) (phi : logic) (expected : Bool) : IO Unit := do
  let (got, output) := Verifyiable.verifyAndExplain startState phi
  if got != expected then
    let details := match output with
      | some actions => "Counterexample:\n  " ++ String.intercalate "\n  " actions
      | none => "No counterexample (the formula is true)"
    throw <| IO.userError s!"test failed: expected {expected}, got {got}. {details}"

-- Hard assert for tests: #assert! <expr>, where expr : Bool.
-- Behaves like #eval, but a false expr is a compile error, so the test
-- driver (lake test) sees a nonzero exit code and marks the module as
-- failed. A nearby #eval may still print details (counterexamples) for
-- humans. The "test failed:" prefix is required by the driver (see the
-- cheat sheet at the top of the file).
macro "#assert! " e:term : command =>
  `(command| #eval
    show IO Unit from
      if $e then pure ()
      else throw (IO.userError "test failed: assertion failed"))
