import TVL.Sema
import TVL.AtomicProposition
import TVL.Logics.CTL
import Engine.Fair

-- Explicit state graph built in memory
structure StateGraph where
  states : List State
  forwardEdges : List (State × Transition × State)
  backwardEdges : List (State × Transition × State)
  -- Labeling: for every state, the list of CTL subformulas that hold in it
  labels : List (State × List CTL)
  deriving Nonempty

-- 1. Graph generation phase (DFS)
partial def generateGraph (initial : State) : StateGraph :=
  let rec dfs (stack : List State) (visited : List State)
              (edges : List (State × Transition × State)) : StateGraph :=
    match stack with
    | [] =>
      let backEdges := edges.map fun (src, t, dst) => (dst, t, src)
      { states := visited,
        forwardEdges := edges,
        backwardEdges := backEdges,
        labels := visited.map fun s => (s, []) }
    | h :: t =>
      if visited.contains h then
        dfs t visited edges
      else
        let newVisited := h :: visited
        let nextSteps := step h
        let newEdges := nextSteps.map fun (t, sNext) => (h, t, sNext)
        let nextStates := nextSteps.map Prod.snd
        dfs (nextStates ++ t) newVisited (newEdges ++ edges)

  dfs [initial] [] []

def addLabel (graph : StateGraph) (s : State) (phi : CTL) : StateGraph :=
  -- Find state s in graph.labels and append phi to its list
  match graph.labels.lookup s with
  | some _ =>
    let newLabels := graph.labels.map (fun (s', ctls) =>
      if s == s' then (s', ctls ++ [phi]) else (s', ctls))
    { graph with labels := newLabels }
  | none => graph

-- ============================================================================
-- Fairness: with fair? = some ctx every path quantifier ranges
-- over fair paths only. The scheme needs one precomputed set --
-- fairStates, the states that start SOME fair path (the `fair` atom,
-- EG_fair true = the backward reachability of the fair regions) -- and
-- then threads it through the labeling:
--   ap p   -> Sat(p) ∩ fair
--   ex f   -> predecessors of (Sat(f) ∩ fair)      [the TARGET is filtered]
--   eu f1 f2 -> backward BFS seeded from Sat(f2) ∩ fair
--   eg f   -> the fair regions of the Sat(f)-restricted graph
-- not/and stay boolean: the fair semantics of a negation IS the complement
-- of the label, and the parser encodes the A-operators through E-operators
-- and negation, so they need no separate treatment. fair? = none keeps the
-- behaviour below byte-for-byte identical to the no-fairness code.
-- ============================================================================

structure FairCtx where
  spec       : FairSpec State
  fairStates : List State

-- The FairSpec of a whole state graph: the actors and their enabledness
-- are read off the edges (the graph is closed -- it holds every transition
-- of every reachable state, so `enabled` over the edges equals `step`).
-- An actor without a single edge anywhere is disabled everywhere: vacuous,
-- no constraint -- dropping it from the list changes nothing.
def fairSpecOfGraph (graph : StateGraph) (strong : Bool) : FairSpec State := {
  actors  := (graph.forwardEdges.map fun (_, tr, _) => tr.processId).eraseDups
  accept  := none
  strong  := strong
  enabled := fun a s =>
    graph.forwardEdges.any fun (u, tr, _) => u == s && tr.processId == a
}

-- The `fair` atom of the scheme above: the states starting a fair path,
-- computed once per run in Main and shared by every spec.
def computeFairStates (graph : StateGraph) (spec : FairSpec State) : List State :=
  let tagged := graph.forwardEdges.map fun (s, tr, t) => (s, tr.processId, t)
  reachingBackward graph.states tagged (fairRegions graph.states tagged spec).flatten

-- The action names along a concrete path of states (each consecutive pair
-- is connected by a transition of the graph; "?" would mean a bug).
def statePathActions (g : StateGraph) (path : List State) : List String :=
  (path.zip (path.drop 1)).map fun (a, b) =>
    match g.forwardEdges.find? fun (s, _, t) => s == a && t == b with
    | some (_, tr, _) => tr.actionName
    | none => "?"

-- 2. Procedure for E[phi1 U phi2]:
-- starts from the states where phi2 holds and walks the backwardEdges
partial def checkEU (graph : StateGraph) (phi1 phi2 : CTL)
                   (fair? : Option FairCtx := none) : StateGraph :=
  -- Under fairness the seed must be a FAIR phi2-state: the label of a
  -- negative-shape phi2 (e.g. `!q`) reaches outside the fair set through
  -- the complement, while E[phi1 U phi2] needs a fair PATH whose last
  -- phi2-state continues fairly. The intermediate phi1-states stay
  -- unfiltered: every state the backward BFS marks reaches a fair seed and
  -- is therefore fair itself (backward closure), and its phi1-label
  -- already carries the fair semantics of the recursion.
  let statesWithPhi2 := graph.labels.filter (fun (s, ctls) =>
    ctls.contains phi2 && fair?.all fun fc => fc.fairStates.contains s)
  let initialMarkedStates := statesWithPhi2.map Prod.fst
  let initialMarkedGraph := graph.labels.map (fun (s, ctls) =>
    if initialMarkedStates.contains s then
      if !ctls.contains (CTL.eu phi1 phi2) then
        (s, ctls ++ [CTL.eu phi1 phi2])
      else (s, ctls)
    else (s, ctls)
  )
  let initialGraph := { graph with labels := initialMarkedGraph}

  let rec whileLoop (g : StateGraph) (marked : List State) : StateGraph :=
    match marked with
    | [] => g
    | h :: t =>
      let edgesToMark := g.backwardEdges.filter (fun (s, _, _) => s == h)
      let statesToMark := edgesToMark.map (fun (_, _, predS) => predS)
      let validPreds := statesToMark.filter (fun pred =>
        match g.labels.lookup pred with
        | some ctls => ¬ctls.contains (CTL.eu phi1 phi2) ∧ ctls.contains phi1
        | none => false
      )
      let updatedLabels := g.labels.map (fun (s, ctls) =>
        if validPreds.contains s then (s, ctls ++ [CTL.eu phi1 phi2])
        else (s, ctls)
      )
      let markedGraph := { g with labels := updatedLabels }
      let newMarked := validPreds ++ t
      whileLoop markedGraph newMarked
  whileLoop initialGraph initialMarkedStates


-- Returns the pair: (updated visited list, exit-time stack)
partial def dfs1 (g : StateGraph) (validStates : List State) (s : State)
                 (accPair : List State × List State) : List State × List State :=
  let (visited, postOrder) := accPair
  if visited.contains s then accPair
  else
    let newVisited := visited ++ [s]
    let edgesToVisit := g.forwardEdges.filter (fun (s', _, t') => s' == s && validStates.contains t')
    let neighbours := edgesToVisit.map (fun (_, _, predS) => predS)

    let (newVisited', postOrder') := neighbours.foldl (fun acc s' => dfs1 g validStates s' acc) (newVisited, postOrder)

    let newPostOrder := postOrder' ++ [s]
    (newVisited', newPostOrder)


-- Returns the pair: (updated visited list, the SCC being collected)
partial def dfs2 (g : StateGraph) (validStates : List State) (s : State)
                 (accPair : List State × List State) : List State × List State :=
  let (visited, currentSCC) := accPair
  if visited.contains s then accPair
  else
    let newVisited := visited ++ [s]
    let updatedSCC := currentSCC ++ [s]
    let edgesToVisit := g.backwardEdges.filter (fun (s', _, predS) => s' == s && validStates.contains predS)
    let neighbours := edgesToVisit.map (fun (_, _, predS) => predS)

    let (newVisited', updatedSCC') := neighbours.foldl (fun acc s' => dfs2 g validStates s' acc) (newVisited, updatedSCC)
    (newVisited', updatedSCC')

-- 3. Kosaraju's algorithm for finding SCCs (needed by checkEG)
def findSCC (g : StateGraph) (validStates : List State) : List (List State) :=
  let (_, postOrder) := validStates.foldl (fun acc s => dfs1 g validStates s acc) ([], [])
  let (_, SCCs) := postOrder.reverse.foldl (fun accPair s =>
    let (visited, SCCs) := accPair
    if visited.contains s then accPair
    else
      let (newVisited, currentSCC) := dfs2 g validStates s (visited, [])
      (newVisited, currentSCC :: SCCs)
  ) ([], [])
  SCCs

-- 4. Procedure for EG phi:
-- keep only the vertices where phi holds, run findSCC, then walk the
-- backwardEdges
partial def checkEG (g : StateGraph) (phi : CTL) (fair? : Option FairCtx := none) : StateGraph :=
  let statesWithPhi := g.labels.filter (fun (_, ctls) => ctls.contains phi)
  let markedStates := statesWithPhi.map Prod.fst
  let cutGraph := { g with states := markedStates}
  let SCCStates :=
    match fair? with
    | none =>
        -- Without fairness: Kosaraju + the nontrivial-SCC filter, as before.
        let listOfSCC := findSCC cutGraph markedStates
        let nontrivialSCCStates := listOfSCC.filter (fun comp =>
          if comp.length > 1 then true
          else
            -- Size 1: check whether the node has a self-loop
            match comp with
            | [s] => cutGraph.forwardEdges.any (fun (src, _, dst) => src == s && dst == s) -- g or cutGraph works the same here
            | _ => false
          )
        nontrivialSCCStates.flatten
    | some fc =>
        -- Fair EG: the seed set is the union of the fair regions of the
        -- Sat(phi)-restricted graph (every node of a terminal fair region
        -- lies ON a fair cycle -- the witness chaining of Engine/Fair.lean
        -- can route through any of them); the backward walk below is then
        -- the same as without fairness.
        let edges := g.forwardEdges.filter fun (s, _, t) =>
          markedStates.contains s && markedStates.contains t
        let tagged := edges.map fun (s, tr, t) => (s, tr.processId, t)
        (fairRegions markedStates tagged fc.spec).flatten

  -- Not strictly necessary, but it speeds up the whileLoop a little
  let initialLabels := g.labels.map (fun (s, ctls) =>
    if SCCStates.contains s && !ctls.contains (CTL.eg phi) then
      (s, ctls ++ [CTL.eg phi])
    else (s, ctls)
  )
  let initialGraph := { g with labels := initialLabels }

  let rec whileLoop (acc : StateGraph) (marked : List State) : StateGraph :=
    match marked with
    | [] => acc
    | h :: t =>
      let edgesToMark := acc.backwardEdges.filter (fun (s, _, _) => s == h)
      let statesToMark := edgesToMark.map (fun (_, _, predS) => predS)
      let notMarkedPreds := statesToMark.filter (fun pred =>
        markedStates.contains pred && -- otherwise backwardEdges may lead to a state
                                      -- that does not satisfy phi
        match acc.labels.lookup pred with
        | some ctls => ¬ctls.contains (CTL.eg phi)
        | none => false
      )
      let updatedLabels := acc.labels.map (fun (s, ctls) =>
        if notMarkedPreds.contains s then (s, ctls ++ [CTL.eg phi])
        else (s, ctls)
      )
      let markedGraph := { acc with labels := updatedLabels }
      let newMarked := notMarkedPreds ++ t
      whileLoop markedGraph newMarked
  whileLoop initialGraph SCCStates

-- The main labeling algorithm
partial def checkCTL (graph : StateGraph) (phi : CTL)
                    (fair? : Option FairCtx := none) : StateGraph :=
  match phi with
  | .top =>
      -- 1. True holds everywhere: label every state with `top`. (Under
      -- fairness the label stays on all states as well: a literal
      -- true/false spec gets the same verdict either way, and `top`
      -- reaches the engine only as the f1 of an EU, where the fair seed
      -- filter neutralizes it.)
      let marked := graph.labels.map (fun (s, ctls) => (s, ctls ++ [CTL.top]))
      { graph with labels := marked }

  | .ap p =>
      -- 2. Atomic predicate: go over all states, evaluate evalAP s p,
      -- and label every state where it holds. Under fairness an atom is
      -- conjoined with `fair`: M,s |=_F p iff p holds AND a fair path
      -- starts at s.
      let validStates := graph.states.filter (fun s =>
        evalAP s p && fair?.all fun fc => fc.fairStates.contains s)
      validStates.foldl (fun g s => addLabel g s phi) graph

  | .not f =>
      -- 3. Recursively label the graph for the subformula `f`, then label
      -- every state WITHOUT the `f` label with `not f`. (The fair
      -- semantics of a negation is exactly the complement of the label:
      -- satisfaction quantifies over fair paths on both sides.)
      let graphWithF := checkCTL graph f fair?
      let newLabels := graphWithF.labels.map (fun (s, ctls) =>
        match ctls.contains f with
        | true => (s, ctls)
        | false => (s, ctls ++ [CTL.not f])
      )
      { graphWithF with labels := newLabels }

  | .and f1 f2 =>
      -- 4. Recursively label f1 and f2, then label the states that have
      -- BOTH labels with `and f1 f2`.
      let g1 := checkCTL graph f1 fair?
      let g2 := checkCTL g1 f2 fair?
      let newLabels := g2.labels.map (fun (s, ctls) =>
        match ctls.contains f1 with
        | true => match ctls.contains f2 with
          | true => (s, ctls ++ [CTL.and f1 f2])
          | false => (s, ctls)
        | false => (s, ctls)
      )
      { g2 with labels := newLabels }

  | .ex f =>
      -- 5. Use the backwardEdges of the graph. Under fairness the TARGET
      -- states are filtered (not the predecessors): EX_F f needs a fair
      -- path whose first step lands in a state that both satisfies f and
      -- continues fairly; the predecessor inherits fairness backwards for
      -- free (any predecessor of a fair state is fair).
      let graphWithF := checkCTL graph f fair?
      let targetStates := graphWithF.labels.filter (fun (s, ctls) =>
        ctls.contains f && fair?.all fun fc => fc.fairStates.contains s)
      let targetStatesBackedges := graphWithF.backwardEdges.filter (fun (s, _, _) =>
        match targetStates.lookup s with
        | some _ => true
        | none => false)
      let targetStatesPreds := targetStatesBackedges.map (fun (_, _, pred) => pred)
      let newLabels := graphWithF.labels.map (fun (s, ctls) =>
        match targetStatesPreds.contains s with
        | true => (s, ctls ++ [CTL.ex f])
        | false => (s, ctls))
      { graphWithF with labels := newLabels }

  | .eu f1 f2 =>
    -- Label BOTH subformulas first (bottom up!), then run the separate
    -- backward BFS
    let g1 := checkCTL graph f1 fair?
    let g2 := checkCTL g1 f2 fair?
    checkEU g2 f1 f2 fair?

  | .eg f =>
    -- 7. Use SCCs (Kosaraju's algorithm): checkEG
    let g1 := checkCTL graph f fair?
    checkEG g1 f fair?

-- ===========================================================================================
-- ===========================================================================================
-- ===========================================================================================

-- Search for a linear trace (for the EU operator and Safety / AG violations)
partial def findTraceEU (g : StateGraph) (startState : State) (phi1 phi2 : CTL) : Option (List String) :=
  let rec bfs (queue : List (State × List String)) (visited : List State) : Option (List String) :=
    match queue with
    | [] => none
    | (curr, path) :: rest =>
        match g.labels.lookup curr with
        | none => bfs rest visited
        | some ctls =>
            -- Reached the finish (phi2): return the accumulated path
            if ctls.contains phi2 then
              some path
            -- Still on a valid path (phi1): go on
            else if ctls.contains phi1 then
              let outgoingEdges := g.forwardEdges.filter (fun (src, _, dst) => src == curr && !visited.contains dst)
              let newVisited := visited ++ outgoingEdges.map (fun (_, _, dst) => dst)
              let newQueueItems := outgoingEdges.map fun (_, trans, dst) =>
                (dst, path ++ [trans.actionName])
              bfs (rest ++ newQueueItems) newVisited
            -- Neither phi2 nor phi1: a dead end, this branch does not fit
            else
              bfs rest visited

  bfs [(startState, [])] [startState]

-- Search for a lasso (for the EG operator and Liveness / AF violations).
-- Without fairness the labeling algorithm has ALREADY proved the existence
-- of a cycle and attached the `EG phi` label, so a "greedy" DFS walk over
-- the states with this label until we hit an already visited state is
-- enough. Under fairness the greedy walk is unsound -- it may close its
-- cycle on a shortcut that avoids the fairness witnesses -- so the lasso
-- is built explicitly: witness chaining inside a fair region of the
-- Sat(phi)-restricted graph (fairLasso), with a BFS prefix from the start.
-- The start-state guard of the greedy branch is implicit here: fairLasso
-- BFSes from startState, and a start without the EG label reaches no fair
-- region.
partial def findLassoEG (g : StateGraph) (startState : State) (targetEGPhi : CTL)
                        (fair? : Option FairCtx := none) : Option (List String) :=
  match fair? with
  | some fc =>
      match targetEGPhi with
      | .eg f =>
          let phiStates := (g.labels.filter fun (_, ctls) => ctls.contains f).map Prod.fst
          let edges := g.forwardEdges.filter fun (s, _, t) =>
            phiStates.contains s && phiStates.contains t
          let tagged := edges.map fun (s, tr, t) => (s, tr.processId, t)
          let regions := fairRegions phiStates tagged fc.spec
          let lassos := regions.filterMap fun r =>
            fairLasso phiStates tagged r fc.spec startState
          match lassos.head? with
          | some (pref, loop) =>
              some (statePathActions g pref
                    ++ ["--- LOOP STARTS HERE ---"]
                    ++ statePathActions g loop
                    ++ ["--- LOOP REPEATS ---"])
          | none => none
      | _ => none
  | none =>
    let rec walk (curr : State) (visited : List State) (path : List (State × String)) : Option (List String) :=
      -- Keep only the transitions whose target node ALSO carries the EG label
      let validEdges := g.forwardEdges.filter fun (src, _, dst) =>
        src == curr && (match g.labels.lookup dst with | some ctls => ctls.contains targetEGPhi | none => false)

      match validEdges with
      | [] => none -- should not happen when the labeling is correct
      | (_, trans, nextState) :: _ => -- take the first suitable path (greedy search)
          match visited.findIdx? (fun x => x == nextState) with
          | some idx =>
              -- Found a state we have already seen: the cycle is closed.
              -- idx is the distance from the end of the visited list (we consed)
              let fullPath := (path.reverse.map Prod.snd) ++ [trans.actionName]
              let prefixLen := fullPath.length - (idx + 1)
              let pref := fullPath.take prefixLen
              let cycle := fullPath.drop prefixLen

              some (pref ++ ["--- LOOP STARTS HERE ---"] ++ cycle ++ ["--- LOOP REPEATS ---"])
          | none =>
              -- Go deeper, remembering the current node and action
              walk nextState (curr :: visited) ((curr, trans.actionName) :: path)

    -- Check that the start state belongs to the EG at all
    match g.labels.lookup startState with
    | some ctls => if ctls.contains targetEGPhi then walk startState [startState] [] else none
    | none => none

-- Witness search for a TRUE formula. findTraceEU and the EX case work off
-- the labels as-is: the labeling already carries the fair semantics, and a
-- trace ending in a fair state extends to a fair path, so the witnesses
-- stay sound under fair? = some _.
def findWitness (g : StateGraph) (currState : State) (phi : CTL)
                (fair? : Option FairCtx := none) : Option (List String) :=
  match phi with
  | .eu f1 f2 => findTraceEU g currState f1 f2
  | .eg _ => findLassoEG g currState phi fair? -- pass the whole EG formula
  | .ex f =>
      -- EX needs a single step
      let validEdges := g.forwardEdges.filter fun (src, _, dst) =>
        src == currState && (match g.labels.lookup dst with | some ctls => ctls.contains f | none => false)
      match validEdges with
      | (_, trans, _) :: _ => some [trans.actionName]
      | [] => none
  | _ => none

-- Main entry point of counterexample analysis
def getCounterexample (g : StateGraph) (startState : State) (failedPhi : CTL)
                      (fair? : Option FairCtx := none) : Option (List String) :=
  match failedPhi with
  -- A failed formula starting with a negation means its inner part is TRUE:
  -- look for a witness of that inner part!
  | .not f => findWitness g startState f fair?
  -- In the other cases (e.g. a failed EF, meaning "no path exists at all")
  -- no linear trace can be built; the answer is the whole graph.
  | _ => none
