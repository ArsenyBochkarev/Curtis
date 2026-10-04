import Test.Harness
import Engine.LTL
import Engine.CTL

-- ============================================================================
-- Verdict helpers for the fairness E2E tests: (holds, counterexample
-- actions) of a spec without / with process fairness. Plain functions, not
-- Verifyiable instances -- Test.E2E.LTL.Harness and Test.E2E.CTL.Harness
-- already define those for the no-fairness engines, and importing both in
-- one file would declare the instances twice.
-- ============================================================================

-- LTL, no fairness (the checkLTL engine, with its automatic POR policy)
def ltlVerdict (startState : State) (phi : LTL) : Bool × Option (List String) :=
  match checkLTL startState phi with
  | some trace => (false, some (traceToActions trace))
  | none => (true, none)

-- LTL under process fairness (strong? = strong / weak)
def ltlFairVerdict (startState : State) (phi : LTL) (strong : Bool)
    : Bool × Option (List String) :=
  match checkLTLFair startState phi strong with
  | (some trace, _) => (false, some (traceToActions trace))
  | (none, _) => (true, none)

-- CTL, no fairness
def ctlVerdict (startState : State) (phi : CTL) : Bool × Option (List String) :=
  let g := generateGraph startState
  let marked := checkCTL g phi
  let holds := match marked.labels.lookup startState with
    | some ctls => ctls.contains phi
    | none => false
  if holds then (true, none)
  else (false, getCounterexample marked startState phi)

-- CTL under process fairness (strong? = strong / weak): the fair context
-- is exactly what Main.lean builds -- the spec read off the graph plus the
-- fair states, shared by the labeling and the witness search.
def ctlFairVerdict (startState : State) (phi : CTL) (strong : Bool)
    : Bool × Option (List String) :=
  let g := generateGraph startState
  let spec := fairSpecOfGraph g strong
  let fc : FairCtx := { spec := spec, fairStates := computeFairStates g spec }
  let marked := checkCTL g phi fc
  let holds := match marked.labels.lookup startState with
    | some ctls => ctls.contains phi
    | none => false
  if holds then (true, none)
  else (false, getCounterexample marked startState phi fc)

-- expectVerify, but over a precomputed verdict pair: silent when the
-- verdicts match, an error with the counterexample otherwise.
def expectVerdict (got : Bool × Option (List String)) (expected : Bool) : IO Unit := do
  if got.1 != expected then
    let details := match got.2 with
      | some actions => "Counterexample:\n  " ++ String.intercalate "\n  " actions
      | none => "No counterexample"
    throw <| IO.userError s!"test failed: expected {expected}, got {got.1}. {details}"
