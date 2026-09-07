import Opts.POR
import Engine.LTL
import Test.E2E.LTL.Simple

-- ============================================================================
-- Unit tests for partial order reduction (Opts/POR.lean)
--
-- Invariants of the optimization:
--   1. The verdict of the check (counterexample / none) does not depend on
--      the reduction;
--   2. With the reduction, no more states are expanded than without it.
--
-- The model and the formulas are taken from the LTL E2E test, to avoid
-- duplicating the IR program. The statistics (the number of expanded
-- states) come from checkLTLDebug -- it works when the optimization debug
-- mode is on (optsDebug = true in Opts/POR.lean).
-- All checks are silent: the report with the state counts is printed only
-- on failure.
-- ============================================================================

-- Formula verdict: true -- the property holds (no counterexample)
def verdict (res : Option Trace × Nat) : Bool :=
  res.1.isNone

-- Compare a check with POR and without it:
-- (do the verdicts match, states without POR, states with POR).
-- The porOpt for the "with POR" run is built the same way checkLTL itself
-- does it: the reduction is enabled only for formulas without X.
def comparePOR (startState : State) (phi : LTL) : Bool × Nat × Nat :=
  let withoutPOR := checkLTLDebug startState phi none
  let withPOR := checkLTLDebug startState phi
    (if formulaUsesNext phi then none else some (getVisibleAPs phi))
  (verdict withoutPOR == verdict withPOR, withoutPOR.2, withPOR.2)

-- ============================================================================
-- A model where the effect of the reduction is visible in the state count
--
-- Two independent actors, each endlessly sending messages to ITS OWN queue
-- (A to QA, B to QB). The queues are bounded (MAX_QUEUE_SIZE = 10), so
-- each actor eventually hits a full queue. The full graph consists of all
-- interleavings of the two fill "counters" (~11 x 11 queue states x
-- instruction counters). The reduction should move only one actor at a
-- time: while A is active, B's transitions are invisible and independent,
-- so they can be postponed -- the interleavings are not explored.
--
-- On the E2E model the counts coincide: for false properties the search
-- stops at the first counterexample (the count depends on the luck of the
-- ordering), and for true ones the formula automaton itself filters out
-- most of the graph.
-- ============================================================================

def aGraph : ActorGraph := [
  (0, { id := 0, lineNumber := 1, scheduler := none, instr := IRInstruction.push 1 "QA" "a" }),
  (1, { id := 1, lineNumber := 2, scheduler := none, instr := IRInstruction.jump 0 })
]

def bGraph : ActorGraph := [
  (0, { id := 0, lineNumber := 5, scheduler := none, instr := IRInstruction.push 1 "QB" "b" }),
  (1, { id := 1, lineNumber := 6, scheduler := none, instr := IRInstruction.jump 0 })
]

def porModelState : State := mkInitialState
  [("A", aGraph), ("B", bGraph)]
  ["QA", "QB"]

-- "Eventually there are more than 5 messages in queue QA".
-- The property is true: A does nothing but push, so on every execution QA
-- reaches MAX_QUEUE_SIZE = 10. The negation is still satisfiable in the
-- initial state (G "QA <= 5": the queue starts empty), so the check has to
-- explore the whole graph before it is convinced there is no accepting
-- cycle. B is invisible for this formula at all times, A -- until QA
-- exceeds 5. To see the state counts live:
--   #eval comparePOR porModelState propQAEventuallyBig
def propQAEventuallyBig : LTL :=
  F (LTL.ap (AtomicProposition.queueSizeGt "QA" 5))

-- All the checks at once: (name, verdicts match, states without POR, with POR)
def porChecks : List (String × (Bool × Nat × Nat)) :=
  [ ("E2E model: propF_R3_Finish",       comparePOR initialStateGen propF_R3_Finish),
    ("E2E model: propSafety",            comparePOR initialStateGen propSafety),
    ("E2E model: propEventuallyMsg",     comparePOR initialStateGen propEventuallyMsg),
    ("synthetic model: propQAEventuallyBig", comparePOR porModelState propQAEventuallyBig) ]

-- Silent on success; on failure, a report over the diverging checks
-- (pattern 3 of the cheat sheet in Test/Harness.lean)
#eval show IO Unit from
  let bad := porChecks.filter (fun (_, r) => !r.1)
  unless bad.isEmpty do
    throw (IO.userError ("test failed: POR: verdicts diverged:\n" ++ String.intercalate "\n"
      (bad.map (fun (name, r) =>
        s!"  {name}: match={r.1}, without POR={r.2.1}, with POR={r.2.2}"))))
