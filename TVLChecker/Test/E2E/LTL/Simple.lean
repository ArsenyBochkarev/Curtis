import TVLChecker.Test.E2E.LTL.Harness

-- 1. Building the IR program (ActorGraph).
-- The model is carried over from CTL/Simple.lean with one change: after
-- the first two sends R1 does not terminate but keeps sending Y to R3
-- forever (jump back). An LTL counterexample is always a lasso (an
-- infinite run), while every execution of the original model is finite
-- (each actor reaches endInstr), so no LTL property can be refuted there.
def r1Graph : ActorGraph := [
  (0, { id := 1, lineNumber := 5, scheduler := none, instr := IRInstruction.push 1 "Q[R2][R1]" "X" }),
  (1, { id := 0, lineNumber := 4, scheduler := none, instr := IRInstruction.push 2 "Q[R3][R1]" "Y" }),
  (2, { id := 2, lineNumber := 6, scheduler := none, instr := IRInstruction.jump 1 })
]

def r2Graph : ActorGraph := [
  (0, { id := 0, lineNumber := 9, scheduler := none, instr := IRInstruction.pop 1 "Q[R2][R1]" "X" }),
  -- choose { ... } or { ... }
  (1, { id := 1, lineNumber := 10, scheduler := none, instr := IRInstruction.choice [2, 4] }),
  -- Branch 1: fail_send: skip; start_send: send X to R3
  (2, { id := 2, lineNumber := 11, scheduler := none, instr := IRInstruction.skipInstr 3 }),
  (3, { id := 3, lineNumber := 12, scheduler := none, instr := IRInstruction.push 5 "Q[R3][R2]" "X" }),
  -- Branch 2: send X to R3
  (4, { id := 4, lineNumber := 14, scheduler := none, instr := IRInstruction.push 5 "Q[R3][R2]" "X" }),
  (5, { id := 5, lineNumber := 16, scheduler := none, instr := IRInstruction.endInstr })
]

def r3Graph : ActorGraph := [
  -- receive alts (start of the repeat loop)
  (0, { id := 0, lineNumber := 20, scheduler := none,
        instr := IRInstruction.branch
          [ { queueName := "Q[R3][R2]", msg := "X", bodyStart := 1 },
            { queueName := "Q[R3][R1]", msg := "Y", bodyStart := 2 } ]
          none -- otherwiseOpt
      }),
  -- Branch X: break (leave the loop for the end)
  (1, { id := 1, lineNumber := 21, scheduler := none, instr := IRInstruction.jump 3 }),
  -- Branch Y: skip (and return to the start of the repeat loop)
  (2, { id := 2, lineNumber := 22, scheduler := none, instr := IRInstruction.skipInstr 0 }),
  (3, { id := 3, lineNumber := 25, scheduler := none, instr := IRInstruction.endInstr })
]

-- 2. Building the initial state
def initialStateGen : State := mkInitialState
  [("R1", r1Graph), ("R2", r2Graph), ("R3", r3Graph)]
  ["Q[R3][R1]", "Q[R2][R1]", "Q[R3][R2]"]

-- 3. Properties to check

-- Property 1 (liveness): R3 eventually finishes (expected: false).
-- This is the same scenario as in the comment on propAF_R3_Finish from
-- CTL/Simple.lean ("if true, R3 cannot receive Y forever") -- except that
-- now receiving Y forever is actually possible, and the counterexample
-- shows it.
def propF_R3_Finish : LTL :=
  F (LTL.ap (AtomicProposition.actorFinished "R3"))

-- Property 2 (safety): "queue Q[R3][R1] is always empty" (expected: false).
-- R1 inevitably puts Y there.
def propSafety : LTL :=
  G (LTL.ap (AtomicProposition.queueEmpty "Q[R3][R1]"))

-- Property 3: eventually a message appears in Q[R3][R1] (expected: true)
def propEventuallyMsg : LTL :=
  F (LTL.ap (AtomicProposition.queueSizeGt "Q[R3][R1]" 0))

-- 5. Checks: silent on success, an error with the counterexample when the
-- verdict mismatches (expectations are in the property comments above)
#eval expectVerify initialStateGen propF_R3_Finish false
#eval expectVerify initialStateGen propSafety false
#eval expectVerify initialStateGen propEventuallyMsg true
