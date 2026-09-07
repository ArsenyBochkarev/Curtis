import TVLChecker.TVL.Sema
import TVLChecker.TVL.Logics.LTL

-- ============================================================================
-- Partial Order Reduction (POR)
--
-- Idea: when several independent transitions are enabled in a state s, the
-- property under check (LTL without X) does not care in which order they
-- execute. So at every DFS step we expand not all of enabled(s) but a
-- sufficient subset ample(s) ⊆ enabled(s) satisfying C0–C3:
--
--   C0: ample(s) = ∅  <=>  enabled(s) = ∅   (deadlocks are preserved)
--   C1: transitions outside ample(s) cannot "overtake" transitions that
--       are dependent with something inside ample(s)
--   C2: if the state is not fully expanded (ample(s) ≠ enabled(s)), every
--       transition in ample(s) is invisible for the formula
--   C3: along a cycle no enabled transition may be postponed forever
--       (practical SPIN approximation: if a successor of ample(s) already
--       sits on the DFS stack, give up the reduction and expand the state
--       fully)
--
-- Entry point for the engine: applyPOR, called by productStep from
-- Engine/LTL.lean with the blue DFS stack (for C3) and the visible APs of
-- the formula (for C2).
--
-- Representation note: a transition t is a pair (transition, state_after);
-- t.2 is the state the transition leads to, t.1.processId is the actor it
-- belongs to.
-- ============================================================================

-- Does the formula contain an X operator?
-- POR is only correct for LTL without X (LTL₋X): the reduction thins out
-- traces, while X is sensitive to the exact number of consecutive
-- stuttering steps. checkLTL uses this test to disable POR for formulas
-- with X.
def formulaUsesNext (phi : LTL) : Bool :=
  match phi with
  | .top | .ap _               => false
  | .next _                    => true
  | .not f                     => formulaUsesNext f
  | .and f1 f2 | .until_ f1 f2 => formulaUsesNext f1 || formulaUsesNext f2

-- All atomic predicates occurring in the formula (needed for C2): only they
-- make a transition "visible" for this formula.
-- Note: φ and ¬φ have the same set of APs, so either can be passed.
-- Returns AtomicProposition values (not Strings): the invisibility check
-- then reduces to evaluating evalAP on a pair of states.
def getVisibleAPs (phi : LTL) : List AtomicProposition :=
  match phi with
  | .ap ap                     => [ap]
  | .top                       => []
  | .not f                     => (getVisibleAPs f).eraseDups
  | .next f                    => (getVisibleAPs f).eraseDups
  | .and f1 f2 | .until_ f1 f2 => (getVisibleAPs f1 ++ getVisibleAPs f2).eraseDups

-- A transition s -> s' is invisible for the formula when it changes the
-- value of no visible AP, i.e. L(s) ∩ AP' = L(s') ∩ AP'.
def isInvisible (visibleAPs : List AtomicProposition) (s s' : State) : Bool :=
  visibleAPs.all (fun ap => evalAP s ap == evalAP s' ap)

-- Which queues an IR instruction touches:
-- push and pop work with a single queue, branch may read several
-- (receive alts); the remaining instructions are purely local.
def instrQueues (instr : IRInstruction) : List String :=
  match instr with
  | .push _ q _     => [q]
  | .pop _ q _      => [q]
  | .branch cases _ => cases.map fun c => c.queueName
  | _ => []

-- Which queues the actor MAY touch by its actions in state s.
-- The exact PC of the executed instruction is not stored in Transition
-- (only processId and actionName, and actionName does not name the queue),
-- so we look at ALL active PCs of the actor via getPCs + getInstruction.
-- This is an over-approximation: an actor whose threads hold instructions
-- over different queues yields their union. For POR this is safe: we can
-- only FALSELY consider independent transitions dependent and skip a
-- reduction -- counterexamples are never lost this way.
def actorTouchedQueues (s : State) (actor : String) : List String :=
  match getPCs s actor with
  | some pcs =>
      pcs.flatMap fun pc =>
        match getInstruction s actor pc with
        | some node => instrQueues node.instr
        | none => []
  | none => []

-- Independence of transitions a and b enabled in state s.
-- Formal definition from the lectures:
--   1) Enabledness: after executing a, transition b is still enabled;
--   2) Commutativity: the resulting state is the same.
-- The exact definition is not implemented; instead we use conservative
-- TVL IR criteria:
--   * transitions of the same actor are dependent;
--   * transitions of two different actors are dependent iff they act on
--     the same queue, independent otherwise.
def areIndependent (s : State) (a b : Transition × State) : Bool :=
  let actor1 := a.1.processId
  let actor2 := b.1.processId
  match actor1 == actor2 with
  | true => false -- transitions of the same actor are dependent
  | false =>
    let queuesFromActor1 := actorTouchedQueues s actor1
    let queuesFromActor2 := actorTouchedQueues s actor2
    queuesFromActor1.all (fun a1 => queuesFromActor2.all (fun a2 => a1 != a2))


-- C1 (conservative checkable version): every transition OUTSIDE cand is
-- independent of every transition INSIDE cand.
def checkC1 (s : State) (cand enabled : List (Transition × State)) : Bool :=
  let outerTrans := enabled.filter (fun ts => !cand.contains ts)
  outerTrans.all (fun outerTS => cand.all (fun candTS => areIndependent s candTS outerTS))

-- C2: every transition of the candidate is invisible.
-- (Only checked when cand ≠ enabled -- a full expansion needs no C2.)
def checkC2 (s : State) (cand : List (Transition × State))
            (visibleAPs : List AtomicProposition) : Bool :=
  cand.all (fun (_, candS) => isInvisible visibleAPs s candS)

-- C3 (SPIN approximation): no successor of the candidate lies on the DFS
-- stack. If one does, the reduction would close a cycle and postpone the
-- forgotten transition forever, so such a candidate is rejected.
def checkC3 (cand : List (Transition × State)) (stack : List State) : Bool :=
  cand.all (fun (_, candS) => !stack.contains candS)

-- The main function: pick ample(s) ⊆ enabled(s).
-- A candidate is the set of all enabled transitions of one actor.
def applyPOR (s : State) (enabled : List (Transition × State))
             (stack : List State) (visibleAPs : List AtomicProposition)
             : List (Transition × State) := Id.run do
  -- C0: a deadlock stays a deadlock
  if enabled.isEmpty then
    return enabled
  -- Group the transitions by actor (processId) in a stable order --
  -- the order of the actor's first appearance in enabled
  let mut groups : List (String × List (Transition × State)) := []
  for (tr, st) in enabled do
    let actor := tr.processId
    if groups.any fun (a, _) => a == actor then
      groups := groups.map fun (a, ts) =>
        if a == actor then (a, ts ++ [(tr, st)]) else (a, ts)
    else
      groups := groups ++ [(actor, [(tr, st)])]
  -- Exactly one actor is active => the only candidate coincides with all
  -- of enabled: this is a full expansion, no need to check C1-C3
  if groups.length == 1 then
    return enabled
  -- Try the candidates (all transitions of one actor) in the role of ample(s)
  for (_, cand) in groups do
    if checkC2 s cand visibleAPs && checkC3 cand stack && checkC1 s cand enabled then
      return cand
  -- Nobody fits: safe full expansion
  enabled

-- ============================================================================
-- TODO: move this to main
-- Debug mode for optimizations
def optsDebug : Bool := true
