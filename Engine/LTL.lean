import Init.Data.List.Basic

import TVL.Sema
import TVL.Logics.LTL
import Opts.POR
import Engine.Fair

-- 1. Closure generator

def getCompliment (phi : LTL) : LTL :=
  match phi with
  | .not f => f
  | _      => LTL.not phi

-- Takes a formula and returns all of its subformulas and their negations.
-- The Atoms are later combined out of these.
def closure (phi : LTL) : List LTL :=
  let initialList := match phi with
  | .ap _ | .top  => [phi, getCompliment phi]
  | .not f        => [phi] ++ closure f
  | .and f1 f2    => [phi, getCompliment phi] ++ closure f1 ++ closure f2
  | .next f       => [phi, getCompliment phi] ++ closure f
  | .until_ f1 f2 => [phi, getCompliment phi] ++ closure f1 ++ closure f2
  initialList.eraseDups

-- 2. Local consistency check:
-- make sure a single atom contains no mutually exclusive promises
-- (e.g. both A and not-A) and that Until is unfolded correctly.
def isLocallyConsistent (a : Atom) (closure : List LTL) : Bool :=
  let isSaturated := closure.all (fun phi =>
    if a.contains phi = a.contains (getCompliment phi) then false
    else true
  )
  if !isSaturated then false
  else
    let topInAtom := closure.contains .top && a.contains .top
     if !topInAtom then false
     else
      closure.all (fun phi =>
        -- LOCAL consistency:
        match phi with
        | .and f1 f2 =>
          let f1InAtom := a.contains f1
          let f2InAtom := a.contains f2
          let phiInAtom := a.contains phi
          phiInAtom == (f1InAtom && f2InAtom) -- (f1 and f2) is in the atom <=> f1 and f2 are in the atom
        | .until_ f1 f2 =>
          let f1InAtom := a.contains f1
          let f2InAtom := a.contains f2
          let phiInAtom := a.contains phi

          -- Rule 1: having promised Until, right now either f1 or f2 must hold
          let cond1 := if phiInAtom then (f1InAtom || f2InAtom) else true
          -- Rule 2: once f2 has arrived, Until is automatically fulfilled
          let cond2 := if f2InAtom then phiInAtom else true

          cond1 && cond2
        -- Don't check next since we only look at the current state
        | _ => true
      )

-- 3. Transition check (obligations).
-- Can the automaton move from atom `curr` to atom `next`? This checks the
-- Next (X) operator and the carry-over of unfulfilled Until (U) obligations.
def isValidBuchiTransition (curr : Atom) (next : Atom) (closure : List LTL) : Bool :=
  closure.all (fun phi =>
    -- LOCAL consistency:
    match phi with
    | .next f =>
      let phiNow := curr.contains phi
      let fNext := next.contains f
      phiNow == fNext -- X(psi) is true is current Atom <=> psi is true in next Atom
    | .until_ _ f2 =>
      let phiNow := curr.contains phi
      let phiNext := next.contains phi
      let f2Now := curr.contains f2
      -- if phiNow is true => true
      -- if phiNext is true && phiNow is false => f1Now
      if f2Now then true
      else
        phiNow == phiNext
    -- Don't check next since we only look at the next state
    | _ => true
  )

-- 4. Accepting state.
-- A state of the automaton is accepting when it is not "stuck waiting".
-- For every formula `f1 U f2` in the automaton, either `f2` is present in
-- the atom right now, or `f1 U f2` is not in the atom at all.
def isAccepting (a : Atom) (closure : List LTL) : Bool :=
  closure.all (fun phi =>
    match phi with
    | .until_ _ f2 =>
      let phiInAtom := a.contains phi
      let f2InAtom := a.contains f2
      if phiInAtom && !f2InAtom then false
      else true
    -- We already checked all other cases
    | _ => true
  )

-- ===========================================================================================
-- ===========================================================================================
-- ===========================================================================================

-- Node of the combined (product) graph
structure ProductState where
  progState : State
  buchiState : Atom
  deriving BEq, Hashable

-- Check that reality matches expectations (customs control):
-- if an Atom contains `ap "X"`, then `evalAP` must return true for it.
def isProductStateValid (ps : ProductState) : Bool :=
  ps.buchiState.all (fun phi =>
    match phi with
    | .ap p =>
      evalAP ps.progState p
    | .not f =>
      match f with
      | .ap p =>
        !(evalAP ps.progState p)
      | _ => true
    | _ => true
  )

-- Generate successor states on the fly:
-- cross the `step` function with the transitions of the automaton.
-- por? = some visibleAPs -- partial order reduction is on (Opts/POR.lean):
--   instead of all step transitions we take a sufficient subset ample(s);
--   dfsStack is the current blue-DFS stack (ample needs it for C3).
-- por? = none -- full expansion without the reduction.
def productStep (ps : ProductState) (allValidAtoms : List Atom) (closure : List LTL)
                (por? : Option (List AtomicProposition))
                (dfsStack : List ProductState) : List ProductState := Id.run do
  let progSteps := step ps.progState
  let progSuccs := match por? with
    | some visibleAPs => applyPOR ps.progState progSteps (dfsStack.map ProductState.progState) visibleAPs
    | none => progSteps
  let nextStates := progSuccs.map (fun ts => ts.2)
  let mut validNextProductStates := []
  for next_s in nextStates do
    for next_a in allValidAtoms do
      if isValidBuchiTransition ps.buchiState next_a closure then
        let nextPS := ProductState.mk next_s next_a
        if isProductStateValid nextPS then
          validNextProductStates := nextPS :: validNextProductStates
  validNextProductStates.reverse

-- ===========================================================================================
-- ===========================================================================================
-- ===========================================================================================

abbrev Trace := List ProductState × List ProductState -- (prefix, loop)

-- DFS 2: looks for a path from an accepting state back to itself.
-- Returns true when a cycle is found, together with the updated visited list.
partial def redDFS (curr : ProductState)
                   (seed : ProductState)
                   (redVisited : List ProductState)
                   (currentPath : List ProductState)
                   (allAtoms : List Atom)
                   (closure : List LTL) : Option (List ProductState) × List ProductState := Id.run do
  let mut redVisited := (curr :: redVisited)
  -- The red (nested) search does NOT apply the reduction (porOpt = none):
  -- ample(s) depends on the DFS stack, and the red search has a different
  -- stack, so its ample sets would diverge from the blue ones. Full
  -- expansion guarantees that the closing cycle is searched over all real
  -- transitions, and no counterexample is lost.
  let nextStates := productStep curr allAtoms closure none []
  for next_s in nextStates do
    if next_s == seed then
      return (some (next_s :: currentPath).reverse, redVisited)
    if !(redVisited.contains next_s) then
      let (loop?, newRedVisited) := (redDFS next_s seed redVisited (next_s :: currentPath) allAtoms closure)
      redVisited := newRedVisited
      match loop? with
      | some loop => return (some loop, newRedVisited)
      | none => continue

  return (none, redVisited)

-- DFS 1: the main traversal of the graph.
-- When the recursion returns from a state (post-order) and the state is
-- accepting, it starts the redDFS.
-- Partial order reduction (porOpt) is applied here: currentPath plays the
-- role of the DFS stack for checking condition C3.
partial def blueDFS (curr : ProductState)
                    (visited1 : List ProductState)
                    (visited2 : List ProductState)
                    (currentPath : List ProductState)
                    (allAtoms : List Atom)
                    (closure : List LTL)
                    (porOpt : Option (List AtomicProposition)) : (Option Trace × List ProductState × List ProductState) := Id.run do
  let mut blueVisited := (curr :: visited1)
  let mut redVisited := visited2
  let nextStates := productStep curr allAtoms closure porOpt currentPath
  for next_s in nextStates do
    if !(blueVisited.contains next_s) then
      let (trace?, newBlueVisited, newRedVisited) := (blueDFS next_s blueVisited redVisited (next_s :: currentPath) allAtoms closure porOpt)
      blueVisited := newBlueVisited
      redVisited := newRedVisited
      match trace? with
      | some trace => return (some trace, blueVisited, redVisited)
      | none => continue

  let seed := curr -- This one just for the sake of readability
  if isAccepting curr.buchiState closure then
    let (loop?, newRedVisited) := (redDFS curr seed redVisited [curr] allAtoms closure)
    redVisited := newRedVisited
    let pref := currentPath.reverse
    match loop? with
    | some loop =>
      (some (pref, loop), blueVisited, redVisited)
    | none => (none, blueVisited, redVisited)
  else (none, blueVisited, redVisited)

-- The powerset of list: every subset, each represented as a list.
private def powerset {α : Type} (l : List α) : List (List α) :=
  match l with
  | [] => [[]]
  | a :: as =>
    let rest := powerset as
    rest ++ rest.map (a :: ·)

-- Shared core of checkLTL / checkLTLDebug:
-- 1. Negate the formula.
-- 2. Generate the atoms.
-- 3. Start the NDFS from the initial product states.
-- Returns (counterexample lasso or none, the number of product states the
-- blue DFS had visited by the moment of the verdict) -- the counter comes
-- for free (blueVisited is accumulated by the search anyway).
def checkLTLCore (startState : State) (phi : LTL)
                 (porOpt : Option (List AtomicProposition)) : Option Trace × Nat :=
  let negPhi := LTL.not phi
  let closureList := closure negPhi
  let allSubsets := powerset closureList
  let allValidAtoms := allSubsets.filter (fun s => isLocallyConsistent s closureList)
  let initialAtoms := allValidAtoms.filter (fun s => s.contains negPhi)
  let initialProductStates := initialAtoms.foldl (fun acc atom =>
    let ps := ProductState.mk startState atom
    if isProductStateValid ps then ps :: acc
    else acc
  ) []
  let initBlueVisited := []
  let initRedVisited := []
  let rec runNDFS (states : List ProductState)
                  (blueVisited : List ProductState)
                  (redVisited : List ProductState) : Option Trace × Nat :=
    match states with
    | [] => (none, blueVisited.length)
    | startPs :: tail =>
      if blueVisited.contains startPs then
        -- This start node was already visited; move on to the next one
        runNDFS tail blueVisited redVisited
      else
        -- Run the NDFS
        let (loop?, newBlue, newRed) := blueDFS startPs blueVisited redVisited [startPs] allValidAtoms closureList porOpt
        match loop? with
        | some _ => (loop?, newBlue.length)
        | none =>
          -- No cycles in this branch; pass the updated lists on
          runNDFS tail newBlue newRed
  runNDFS initialProductStates initBlueVisited initRedVisited

-- The main LTL checking function
def checkLTL (startState : State) (phi : LTL) : Option Trace :=
  -- Partial order reduction is only correct for LTL without X (LTL₋X):
  -- for formulas with the next operator it is disabled (full expansion).
  let porOpt := if formulaUsesNext phi then none else some (getVisibleAPs phi)
  (checkLTLCore startState phi porOpt).1

-- The same as checkLTL, but the reduction is controlled explicitly
-- (porOpt = none means full expansion, no reduction), and the result comes
-- with statistics -- the number of expanded states.
def checkLTLDebug (startState : State) (phi : LTL)
                  (porOpt : Option (List AtomicProposition)) : Option Trace × Nat :=
  checkLTLCore startState phi porOpt

-- ===========================================================================================
-- Fair LTL checking
-- ===========================================================================================

-- The product successors of `ps` with the transition KEPT: (actor, target)
-- pairs, so that the product edges can carry the executing actor (productStep
-- drops the transition, and looking it back up from the target state is
-- ambiguous -- two different actors may step between the same states).
-- Sibling of productStep; POR is never applied here (see checkLTLFair).
def productStepTagged (ps : ProductState) (allValidAtoms : List Atom) (closure : List LTL)
                      : List (String × ProductState) := Id.run do
  let progSteps := step ps.progState
  let mut validNextProductStates := []
  for (tr, next_s) in progSteps do
    for next_a in allValidAtoms do
      if isValidBuchiTransition ps.buchiState next_a closure then
        let nextPS := ProductState.mk next_s next_a
        if isProductStateValid nextPS then
          validNextProductStates := (tr.processId, nextPS) :: validNextProductStates
  validNextProductStates.reverse

-- Fairness-aware LTL checking (Engine/Fair.lean has the definitions).
-- The tableau is built exactly as in checkLTLCore: the fairness constraints
-- are NOT folded into the formula (powerset materializes 2^|closure|, and
-- every GF constraint would multiply that). Instead the whole reachable
-- product graph is explored eagerly, its edges tagged with the executing
-- actor, and the verdict is the existence of a FAIR accepting cycle:
--   * accept of the FairSpec is the Buchi acceptance of the tableau atom
--     (a fair run must still satisfy the tableau infinitely often);
--   * enabled A ps  :=  A has an executable step in ps.progState.
-- Partial order reduction is disabled (full expansion): the ample-set
-- conditions are proved for the plain accepting-cycle search, not for the
-- fair-region decomposition -- the red DFS above expands fully for the
-- same reason. The counterexample lasso satisfies the NDFS invariant
-- (the prefix ends with the seed, the loop is [seed, ..., seed]), so
-- traceToActions / traceToActionsMarked work on it unchanged.
partial def checkLTLFair (startState : State) (phi : LTL) (strong : Bool)
                         : Option Trace × Nat :=
  let negPhi := LTL.not phi
  let closureList := closure negPhi
  let allValidAtoms := (powerset closureList).filter (fun s => isLocallyConsistent s closureList)
  let initialAtoms := allValidAtoms.filter (fun s => s.contains negPhi)
  let initialProductStates := initialAtoms.foldl (fun acc atom =>
    let ps := ProductState.mk startState atom
    if isProductStateValid ps then ps :: acc
    else acc
  ) []
  -- Eager DFS over the product (the generateGraph pattern): collect every
  -- reachable node and every product edge, tagged with the actor.
  let rec explore (stack : List ProductState) (visited : List ProductState)
                  (edges : List (ProductState × String × ProductState))
      : List ProductState × List (ProductState × String × ProductState) :=
    match stack with
    | [] => (visited, edges)
    | h :: t =>
        if visited.contains h then explore t visited edges
        else
          let succs := productStepTagged h allValidAtoms closureList
          let newEdges := succs.map fun (actor, ps) => (h, actor, ps)
          explore (succs.map Prod.snd ++ t) (h :: visited) (newEdges ++ edges)
  let (visited, edges) := explore initialProductStates [] []
  let spec : FairSpec ProductState := {
    actors  := startState.actorGraphs.map Prod.fst
    accept  := some (fun ps => isAccepting ps.buchiState closureList)
    strong  := strong
    enabled := fun a ps => (step ps.progState).any fun (tr, _) => tr.processId == a
  }
  let regions := fairRegions visited edges spec
  -- No fair accepting cycle anywhere: every fair run satisfies phi -- HOLDS.
  -- Otherwise exhibit a lasso from the first initial state that reaches a
  -- fair region (some initial state must: a region is reachable from one).
  let lasso? :=
    (initialProductStates.filterMap fun s =>
      (regions.filterMap fun r => fairLasso visited edges r spec s).head?).head?
  (lasso?, visited.length)

-- ===========================================================================================
-- Counterexample presentation
-- ===========================================================================================

-- The action leading from one state of the trace to the next.
-- Neighboring states of a lasso are always connected by a transition
-- (productStep is built on top of step), so we simply look it up among the
-- transitions of the source state. The action description
-- ("push X to Q[R2][R1]") already says everything: in TVL IR it is clear
-- which actor did what.
def transitionAction (src dst : ProductState) : String :=
  match (step src.progState).find? fun (_, s') => s' == dst.progState with
  | some (tr, _) => tr.actionName
  | none => "?"

-- The counterexample for an LTL formula is a lasso (prefix, loop) unfolded
-- into a linear sequence of actions, as in the CTL harness.
-- NDFS invariant: the prefix ends with the seed, and the loop is
-- [seed, n1, ..., nk, seed] (the last element closes the cycle). We drop
-- the duplicate seed from the prefix and glue the parts together:
-- s0 -> ... -> seed -> n1 -> ... -> nk -> seed. The closing transition
-- (nk -> seed) gets into the sequence automatically, from the loop.
def traceToActions (t : Trace) : List String :=
  let (pref, loop) := t
  let path := pref.dropLast ++ loop
  (path.zip (path.drop 1)).map fun (a, b) => transitionAction a b

-- The same lasso, but with explicit textual markers where the loop starts
-- (and where it closes). The markers start with "---", so the DOT exporter
-- (TVL/Output/CTL.lean, reconstructPath) skips them while highlighting the
-- counterexample path -- both consumers share one action list.
def traceToActionsMarked (t : Trace) : List String :=
  let (pref, loop) := t
  let prefPath := pref.dropLast ++ loop.take 1 -- s0 -> ... -> seed
  let prefActs := (prefPath.zip (prefPath.drop 1)).map fun (a, b) => transitionAction a b
  let loopActs := (loop.zip (loop.drop 1)).map fun (a, b) => transitionAction a b
  prefActs ++ ["--- LOOP STARTS HERE ---"] ++ loopActs ++ ["--- LOOP CLOSES HERE ---"]
