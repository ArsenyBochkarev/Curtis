import Test.E2E.CTL.Harness
import TVL.Output.CTL

-- 1. Building the IR program (ActorGraph).
-- Our actor sends a couple of messages and terminates
def r1Graph : ActorGraph := [
  (0, { id := 1, lineNumber := 5, scheduler := none, instr := IRInstruction.push 1 "Q[R2][R1]" "X" }),
  (1, { id := 0, lineNumber := 4, scheduler := none, instr := IRInstruction.push 2 "Q[R3][R1]" "Y" }),
  (2, { id := 2, lineNumber := 6, scheduler := none, instr := IRInstruction.endInstr })
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

-- 2. Building the initial state, filling in every list/map as Sema.lean
-- requires
def initialStateGen : State := mkInitialState
  [("R1", r1Graph), ("R2", r2Graph), ("R3", r3Graph)]
  ["Q[R3][R1]", "Q[R2][R1]", "Q[R3][R2]"]

-- 3. State-graph generation: run the DFS generator from the initial state
def testGraph : StateGraph := generateGraph initialStateGen

-- 4. Properties to check

-- Property 1: R3 may finish successfully (expected: true)
def propEF_R3_Finish : CTL :=
  EF (CTL.ap (AtomicProposition.actorFinished "R3"))

-- Property 2: R3 is GUARANTEED to finish on every execution (expected: true).
-- AF(phi) = not EG(not phi). If true, R3 cannot receive Y forever.
def propAF_R3_Finish : CTL :=
  CTL.not (CTL.eg (CTL.not (CTL.ap (AtomicProposition.actorFinished "R3"))))

-- Property 3: is it possible that R1 has already sent everything and
-- terminated while Y is still in the R3 queue? (expected: true)
def propEF_Concurrency : CTL :=
  EF (
    CTL.and
      (CTL.ap (AtomicProposition.actorFinished "R1"))
      (CTL.not (CTL.ap (AtomicProposition.queueEmpty "Q[R3][R1]")))
  )

-- Property 4: "queue Q[R3][R1] is always empty".
-- In the basis: not (EF (not queueEmpty)) = not (EU top (not queueEmpty))
def propSafety : CTL :=
  CTL.not (EF (CTL.not (CTL.ap (AtomicProposition.queueEmpty "Q[R3][R1]"))))


-- 5. Checks: silent on success, an error with the counterexample when the
-- verdict mismatches (expectations are in the property comments above).
-- The graph can still be exported manually: exportToDot testGraph ...
-- (Output/CTL.lean)
#eval expectVerify initialStateGen propEF_R3_Finish true
#eval expectVerify initialStateGen propAF_R3_Finish true
#eval expectVerify initialStateGen propEF_Concurrency true
#eval expectVerify initialStateGen propSafety false
