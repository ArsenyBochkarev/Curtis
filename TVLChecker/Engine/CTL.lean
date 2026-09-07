import TVLChecker.TVL.Sema
import TVLChecker.TVL.AtomicProposition
import TVLChecker.TVL.Logics.CTL

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

-- 2. Procedure for E[phi1 U phi2]:
-- starts from the states where phi2 holds and walks the backwardEdges
partial def checkEU (graph : StateGraph) (phi1 phi2 : CTL) : StateGraph :=
  let statesWithPhi2 := graph.labels.filter (fun (_, ctls) => ctls.contains phi2)
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
    let edgesToVisit := g.forwardEdges.filter (fun (s', _, _) => s' == s && validStates.contains s')
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
partial def checkEG (g : StateGraph) (phi : CTL) : StateGraph :=
  let statesWithPhi := g.labels.filter (fun (_, ctls) => ctls.contains phi)
  let markedStates := statesWithPhi.map Prod.fst
  let cutGraph := { g with states := markedStates}
  let listOfSCC := findSCC cutGraph markedStates

  let nontrivialSCCStates := listOfSCC.filter (fun comp =>
    if comp.length > 1 then true
    else
      -- Size 1: check whether the node has a self-loop
      match comp with
      | [s] => cutGraph.forwardEdges.any (fun (src, _, dst) => src == s && dst == s) -- g or cutGraph works the same here
      | _ => false
    )
  let SCCStates := nontrivialSCCStates.flatten

  -- Not strictly necessary, but it speeds up the whileLoop a little
  let initialLabels := g.labels.map (fun (s, ctls) =>
    if SCCStates.contains s && !ctls.contains (CTL.eg phi) then
      (s, ctls ++ [CTL.eg phi])
    else (s, ctls)
  )
  let initialGraph := { g with labels := initialLabels }

  let rec whileLoop (initialGraph : StateGraph) (cutGraph : StateGraph) (marked : List State) : StateGraph :=
    match marked with
    | [] => initialGraph
    | h :: t =>
      let edgesToMark := cutGraph.backwardEdges.filter (fun (s, _, _) => s == h)
      let statesToMark := edgesToMark.map (fun (_, _, predS) => predS)
      let notMarkedPreds := statesToMark.filter (fun pred =>
        markedStates.contains pred && -- otherwise backwardEdges may lead to a state
                                      -- that does not exist in cutGraph
        match cutGraph.labels.lookup pred with
        | some ctls => ¬ctls.contains (CTL.eg phi)
        | none => false
      )
      let updatedLabels := initialGraph.labels.map (fun (s, ctls) =>
        if notMarkedPreds.contains s then (s, ctls ++ [CTL.eg phi])
        else (s, ctls)
      )
      let markedGraph := { initialGraph with labels := updatedLabels }
      let newMarked := notMarkedPreds ++ t
      whileLoop initialGraph markedGraph newMarked
  whileLoop initialGraph cutGraph SCCStates -- cutGraph is needed to keep the globality property

-- The main labeling algorithm
partial def checkCTL (graph : StateGraph) (phi : CTL) : StateGraph :=
  match phi with
  | .top =>
      -- 1. True holds everywhere: label every state with `top`.
      let marked := graph.labels.map (fun (s, ctls) => (s, ctls ++ [CTL.top]))
      { graph with labels := marked }

  | .ap p =>
      -- 2. Atomic predicate: go over all states, evaluate evalAP s p,
      -- and label every state where it holds.
      let validStates := graph.states.filter (fun s => evalAP s p)
      validStates.foldl (fun g s => addLabel g s phi) graph

  | .not f =>
      -- 3. Recursively label the graph for the subformula `f`, then label
      -- every state WITHOUT the `f` label with `not f`.
      let graphWithF := checkCTL graph f
      let newLabels := graphWithF.labels.map (fun (s, ctls) =>
        match ctls.contains f with
        | true => (s, ctls)
        | false => (s, ctls ++ [CTL.not f])
      )
      { graphWithF with labels := newLabels }

  | .and f1 f2 =>
      -- 4. Recursively label f1 and f2, then label the states that have
      -- BOTH labels with `and f1 f2`.
      let g1 := checkCTL graph f1
      let g2 := checkCTL g1 f2
      let newLabels := g2.labels.map (fun (s, ctls) =>
        match ctls.contains f1 with
        | true => match ctls.contains f2 with
          | true => (s, ctls ++ [CTL.and f1 f2])
          | false => (s, ctls)
        | false => (s, ctls)
      )
      { g2 with labels := newLabels }

  | .ex f =>
      -- 5. Use the backwardEdges of the graph
      let graphWithF := checkCTL graph f
      let targetStates := graphWithF.labels.filter (fun (_, ctls) => ctls.contains f)
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
    let g1 := checkCTL graph f1
    let g2 := checkCTL g1 f2
    checkEU g2 f1 f2

  | .eg f =>
    -- 7. Use SCCs (Kosaraju's algorithm): checkEG
    let g1 := checkCTL graph f
    checkEG g1 f

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
-- The labeling algorithm has ALREADY proved the existence of a cycle and
-- attached the `EG phi` label, so a "greedy" DFS walk over the states with
-- this label until we hit an already visited state is enough.
partial def findLassoEG (g : StateGraph) (startState : State) (targetEGPhi : CTL) : Option (List String) :=
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

-- Witness search for a TRUE formula
def findWitness (g : StateGraph) (currState : State) (phi : CTL) : Option (List String) :=
  match phi with
  | .eu f1 f2 => findTraceEU g currState f1 f2
  | .eg _ => findLassoEG g currState phi -- pass the whole EG formula
  | .ex f =>
      -- EX needs a single step
      let validEdges := g.forwardEdges.filter fun (src, _, dst) =>
        src == currState && (match g.labels.lookup dst with | some ctls => ctls.contains f | none => false)
      match validEdges with
      | (_, trans, _) :: _ => some [trans.actionName]
      | [] => none
  | _ => none

-- Main entry point of counterexample analysis
def getCounterexample (g : StateGraph) (startState : State) (failedPhi : CTL) : Option (List String) :=
  match failedPhi with
  -- A failed formula starting with a negation means its inner part is TRUE:
  -- look for a witness of that inner part!
  | .not f => findWitness g startState f
  -- In the other cases (e.g. a failed EF, meaning "no path exists at all")
  -- no linear trace can be built; the answer is the whole graph.
  | _ => none
