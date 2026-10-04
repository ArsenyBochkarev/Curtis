import Test.E2E.Fair.Harness

-- ============================================================================
-- The starvation model. S spins in a loop choosing between sending a
-- message to V and skipping; V loops receiving. The queue starts with one
-- message, so V is CONTINUOUSLY enabled from the very first state -- the
-- textbook fairness discriminator:
--   * without fairness S may skip forever and starve V (a run where V is
--     enabled all along yet never executes);
--   * under weak fairness such a run is excluded (WF_V demands that a
--     continuously enabled V executes), so V is guaranteed to receive --
--     and strong fairness subsumes weak (SF implies WF), same verdict.
-- ============================================================================

-- S: loop { choice { send m to V, skip } }
def sGraph : ActorGraph := [
  (0, { id := 0, lineNumber := 3, scheduler := none, instr := IRInstruction.choice [1, 2] }),
  (1, { id := 3, lineNumber := 4, scheduler := none, instr := IRInstruction.push 3 "Q[V][S]" "m" }),
  (2, { id := 3, lineNumber := 5, scheduler := none, instr := IRInstruction.skipInstr 3 }),
  (3, { id := 0, lineNumber := 6, scheduler := none, instr := IRInstruction.jump 0 })
]

-- V: loop { receive m }
def vGraph : ActorGraph := [
  (0, { id := 1, lineNumber := 9, scheduler := none, instr := IRInstruction.pop 1 "Q[V][S]" "m" }),
  (1, { id := 0, lineNumber := 10, scheduler := none, instr := IRInstruction.jump 0 })
]

-- The queue is pre-filled, so V is enabled from the start (mkInitialState
-- builds empty queues; the one queue of the model is overridden by hand).
def starvation : State :=
  { mkInitialState [("S", sGraph), ("V", vGraph)] ["Q[V][S]"] with
    queues := [("Q[V][S]", ["m"])] }

-- Liveness: V eventually receives (its loop-back PC after the first pop).
def ltlVMoves : LTL := F (LTL.ap (AtomicProposition.actorAt "V" 1))

-- The CTL twin of the same property: AF(phi) = not EG(not phi)
def ctlVMoves : CTL :=
  CTL.not (CTL.eg (CTL.not (CTL.ap (AtomicProposition.actorAt "V" 1))))

-- "V never receives": refuted on every fair run's complement... the spec
-- itself stays VIOLATED even under fairness (a fair run may pop V once and
-- then let S spin on an empty queue), but its fair counterexample lasso
-- must now contain the forced pop of V -- see the last check.
def ltlVNever : LTL := G (LTL.not (LTL.ap (AtomicProposition.actorAt "V" 1)))

-- 1. Without fairness the starving run exists: V is violated in both
--    logics (the zero-regression control -- the plain engines keep their
--    old verdicts on a model they have never seen).
#eval expectVerdict (ltlVerdict starvation ltlVMoves) false
#eval expectVerdict (ctlVerdict starvation ctlVMoves) false

-- 2. Weak fairness excludes the starving run: V is guaranteed to receive.
#eval expectVerdict (ltlFairVerdict starvation ltlVMoves false) true
#eval expectVerdict (ctlFairVerdict starvation ctlVMoves false) true

-- 3. Strong fairness gives the same verdict (SF implies WF, so every
--    strongly fair run is weakly fair too).
#eval expectVerdict (ltlFairVerdict starvation ltlVMoves true) true
#eval expectVerdict (ctlFairVerdict starvation ctlVMoves true) true

-- 4. The fair counterexample of "V never receives": still VIOLATED, but
--    the lasso is a FAIR run -- it contains the pop of V.
#eval expectVerdict (ltlFairVerdict starvation ltlVNever false) false
#eval show IO Unit from do
  let (_, some acts) := ltlFairVerdict starvation ltlVNever false
    | throw (IO.userError "test failed: no fair lasso where one was expected")
  unless acts.any (fun a => a.contains "pop") do
    throw (IO.userError
      s!"test failed: the fair lasso contains no step of the starved actor: {acts}")
