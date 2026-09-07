import TVLChecker.Engine.CTL

-- Map a state to its node id in the exported graph
def stateToId (g : StateGraph) (s : State) : String :=
  match g.states.findIdx? (fun x => x == s) with
  | some idx => s!"S{idx}"
  | none => "S_unknown"

-- Pretty-printing of CTL formulas
partial def ctlToString (phi : CTL) : String :=
  match phi with
  | .top => "True"
  | .ap p => s!"{reprStr p}" -- requires `deriving Repr` on AtomicProposition
  | .not f => s!"¬({ctlToString f})"
  | .and f1 f2 => s!"({ctlToString f1} ∧ {ctlToString f2})"
  | .ex f => s!"EX({ctlToString f})"
  | .eg f => s!"EG({ctlToString f})"
  | .eu f1 f2 => s!"E[{ctlToString f1} U {ctlToString f2}]"

-- Walk the graph along a counterexample trace and collect the exact nodes
-- and edges it visits
def reconstructPath (g : StateGraph) (curr : State) (trace : List String) : List State × List (State × String × State) :=
  match trace with
  | [] => ([curr], [])
  | action :: rest =>
      if action.startsWith "---" then
        -- Skip the textual loop markers emitted by findLassoEG
        reconstructPath g curr rest
      else
        -- Find an edge from the current node whose action name matches
        match g.forwardEdges.find? (fun (src, trans, _) => src == curr && trans.actionName == action) with
        | some (_, trans, dst) =>
            let (restStates, restEdges) := reconstructPath g dst rest
            (curr :: restStates, (curr, trans.actionName, dst) :: restEdges)
        | none =>
            ([curr], []) -- safety net: if the path breaks, return what we have

-- DOT export with state labels and counterexample highlighting
def exportToDot (g : StateGraph) (startState : State) (cxOpt : Option (List String)) : String :=
  -- Reconstruct the exact node/edge path when a counterexample is given
  let (cxStates, cxEdges) := match cxOpt with
    | some trace => reconstructPath g startState trace
    | none => ([], [])

  let header := "digraph G {\n  node [shape=box, style=rounded];\n"

  -- Nodes
  let nodes := g.states.map fun s =>
    let id := stateToId g s
    let labelsList := match g.labels.lookup s with
    | some ctls => ctls.map ctlToString
    | none => []

    let labelsStr := if labelsList.isEmpty then "∅" else String.intercalate "\\n" labelsList
    let labelText := s!"{id}\\n---\\n{labelsStr}"

    -- Nodes on the counterexample get a red border
    let style := if cxStates.contains s then
      s!"[label=\"{labelText}\", color=\"#e74c3c\", penwidth=3]"
    else
      s!"[label=\"{labelText}\"]"

    s!"  {id} {style};\n"

  -- Edges
  let edges := g.forwardEdges.map fun (src, trans, dst) =>
    let srcId := stateToId g src
    let dstId := stateToId g dst

    -- Edges of the counterexample get a red border
    let edgeTuple := (src, trans.actionName, dst)
    let style := if cxEdges.contains edgeTuple then
      s!"[label=\"{trans.actionName}\", color=\"#e74c3c\", fontcolor=\"#e74c3c\", penwidth=2]"
    else
      s!"[label=\"{trans.actionName}\"]"

    s!"  {srcId} -> {dstId} {style};\n"

  header ++ String.join nodes ++ String.join edges ++ "}\n"

-- Usage:
-- #eval IO.println (exportToDot testGraph initialState none)
-- #eval IO.println (exportToDot testGraph initialState safetyResult.2)
