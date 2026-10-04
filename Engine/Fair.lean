import Init.Data.List.Basic

-- ============================================================================
-- Fair-cycle machinery shared by both engines
--
-- For an actor A of the model:
--   enabled A s  -- A has an executable step in state s (a transition with
--                  processId == A leaves s; a finished actor is never
--                  enabled, so its constraint is vacuous)
--   executes A   -- a step of the run crosses a transition of A
--   weak fairness   WF_A : (FG enabled A) -> (GF executes A)
--   strong fairness SF_A : (GF enabled A) -> (GF executes A)
-- A path is fair when every actor's constraint holds; specs are then
-- checked over fair paths only.
--
-- Everything is computed over an explicit graph given as a node list plus
-- edges tagged with the executing actor: List (v x String x v). The CTL
-- engine maps its StateGraph edges (s, tr, t) |-> (s, tr.processId, t);
-- the LTL engine tags every product edge with the processId of the program
-- transition it crosses. Nodes are arbitrary (State / ProductState) -- the
-- module only needs BEq, and performance is explicitly not a concern.
--
-- The lasso/cycle semantics of the constraints (a path is eventually
-- periodic, and on a periodic path "infinitely often" means "at some
-- position of the cycle" while "always from some point on" means "at every
-- position of the cycle"):
--   WF_A: the cycle contains a state where A is disabled, or an A-edge;
--   SF_A: the cycle consists ENTIRELY of A-disabled states, or an A-edge;
--   Buchi acceptance (LTL only): the cycle contains an accepting node.
--
-- The fair-region search below turns these into conditions on strongly
-- connected regions; the key facts are proved in the comments of fairRegion.
-- ============================================================================

-- An edge of an explicit graph: (source, executing actor, target).
abbrev FairEdge (ν : Type) := ν × String × ν

-- The fairness setup of a run. `accept` is the extra Buchi condition of
-- the LTL engine (a cycle must contain an accepting tableau atom); the CTL
-- engine passes none. `enabled` is a state predicate, `actors` the full
-- actor list of the model (an actor with no edges anywhere is disabled
-- everywhere, hence vacuous -- it may as well be skipped, but passing the
-- full list keeps both engines uniform).
structure FairSpec (ν : Type) where
  actors  : List String
  accept  : Option (ν → Bool) := none
  strong  : Bool
  enabled : String → ν → Bool

-- ============================================================================
-- Kosaraju's algorithm over an explicit edge list (self-contained on
-- purpose: Engine/CTL.lean keeps its own findSCC, so the fairness additions
-- cannot disturb the no-fairness code path in any way). Both endpoints of
-- every used edge lie in the node list handed to sccsOf.
-- ============================================================================

-- dfs1: forward DFS, accumulating the exit-time (postorder) stack. Only
-- nodes of `nodes` are ever entered -- the edge list may reach further (the
-- fairRegion recursion hands in the edges of a bigger region).
private partial def dfsPost {ν : Type} [BEq ν]
    (nodes : List ν) (edges : List (ν × String × ν)) (s : ν) (acc : List ν × List ν)
    : List ν × List ν :=
  let (visited, post) := acc
  if visited.contains s then acc
  else
    let succs := (edges.filterMap fun (u, _, v) =>
      if u == s && nodes.contains v then some v else none).eraseDups
    let (visited', post') :=
      succs.foldl (fun acc' v => dfsPost nodes edges v acc') (visited ++ [s], post)
    (visited', post' ++ [s])

-- dfs2: backward DFS, collecting one SCC (same node restriction).
private partial def dfsCollect {ν : Type} [BEq ν]
    (nodes : List ν) (edges : List (ν × String × ν)) (s : ν) (acc : List ν × List ν)
    : List ν × List ν :=
  let (visited, comp) := acc
  if visited.contains s then acc
  else
    let preds := (edges.filterMap fun (u, _, v) =>
      if v == s && nodes.contains u then some u else none).eraseDups
    let (visited', comp') :=
      preds.foldl (fun acc' u => dfsCollect nodes edges u acc') (visited ++ [s], comp ++ [s])
    (visited', comp')

-- The maximal SCCs of `nodes` under `edges`, in arbitrary order. Every
-- returned component is a subset of `nodes`, whatever `edges` contains.
def sccsOf {ν : Type} [BEq ν] (nodes : List ν) (edges : List (ν × String × ν))
    : List (List ν) :=
  let (_, post) := nodes.foldl (fun acc s => dfsPost nodes edges s acc) ([], [])
  let (_, comps) :=
    post.reverse.foldl (fun accPair s =>
      let (visited, comps) := accPair
      if visited.contains s then accPair
      else
        -- dfsCollect walks the PREDECESSORS of its edge list, so handing it
        -- the original edges IS the reversed-graph pass of Kosaraju.
        let (visited', comp) := dfsCollect nodes edges s (visited, [])
        (visited', comp :: comps)
    ) ([], [])
  comps

-- An SCC can host an infinite path only when it has a cycle: more than one
-- node, or a single node with a self-loop.
def isCyclicComp {ν : Type} [BEq ν] (edges : List (ν × String × ν)) (comp : List ν) : Bool :=
  match comp with
  | [s] => edges.any fun (u, _, v) => u == s && v == s
  | _ => comp.length > 1

-- Does `actor` have an edge with BOTH endpoints inside `region`? Such an
-- edge is a witness a fair cycle can cross.
def actorEdgeIn {ν : Type} [BEq ν] (edges : List (ν × String × ν))
    (actor : String) (region : List ν) : Bool :=
  edges.any fun (u, a, v) => a == actor && region.contains u && region.contains v

-- ============================================================================
-- Fair regions
--
-- A region is a strongly connected node set that hosts at least one fair
-- cycle. fairRegions returns the terminal fair regions of a graph; every
-- node of such a region lies ON a fair cycle (the witness chain of fairLasso
-- can be routed through any extra node), so "EG under fairness" is simply
-- the backward reachability from their union.
--
-- The conditions, checked per region R:
--   * Buchi (accept = some acc): R must contain an accepting node -- a
--     state witness; no subset can gain one, so a region without it is dead.
--   * weak:   every actor A needs a witness in R: a state where A is
--     disabled (the cycle passes through it) OR an A-edge in R (the cycle
--     crosses it). No recursion is needed: if an actor is enabled at EVERY
--     state of the maximal SCC S and has no edge inside S, then EVERY S-cycle
--     is unfair (enabled all along, no own step) -- S is dead for good,
--     no sub-region can help. Conversely, when every actor has a witness,
--     chaining the witnesses along strong connectivity builds a fair cycle
--     through any node of R (fairLasso does exactly that).
--   * strong: let X = {A : R has an A-enabled node and no A-edge in R}.
--     X = {} -> R is fair (chain the witnesses). Otherwise a fair cycle
--     cannot use an A-edge for A in X (there is none), so its SF_A must be
--     satisfied vacuously: the cycle visits A-enabled states only finitely
--     often, i.e. from some point on it stays in the A-disabled states --
--     for every A in X at once. Hence recurse on the SCCs of
--     R minus (all X-enabled states). An actor disabled EVERYWHERE in R
--     imposes no constraint (its premise GF enabled is false on any R-cycle)
--     and never enters X. The recursion terminates: X nonempty means at
--     least one node (an enabled one) is removed at every level.
--     [This recursion is what a maximal-SCC-only check would miss: a fair
--     sub-cycle avoiding the enabled nodes of a failing actor lives in a
--     strictly smaller SCC -- see the "sub-cycle" regression in
--     Test/Unit/Fair.lean.]
-- ============================================================================

-- Fair sub-regions of one strongly connected region (or of a whole graph's
-- node set -- sccsOf inside fairRegions starts the recursion).
partial def fairRegion {ν : Type} [BEq ν]
    (edges : List (ν × String × ν)) (spec : FairSpec ν) (comp : List ν) : List (List ν) :=
  if !spec.accept.all (fun acc => comp.any acc) then []
    -- no accepting node: dead (see above)
  else if !spec.strong then
    -- weak: one-level witness check, no recursion
    if spec.actors.all fun a =>
        comp.any (fun s => !spec.enabled a s) || actorEdgeIn edges a comp then
      [comp]
    else []
  else
    -- strong: drop the enabled states of every actor without an own edge
    let failing := spec.actors.filter fun a =>
      comp.any (spec.enabled a) && !actorEdgeIn edges a comp
    if failing.isEmpty then [comp]
    else
      let kept := comp.filter fun s => !failing.any fun a => spec.enabled a s
      ((sccsOf kept edges).filter (isCyclicComp edges)).flatMap (fairRegion edges spec)

-- All terminal fair regions of the graph (nodes, edges): the cyclic SCCs
-- that satisfy the constraints, decomposed as described above.
partial def fairRegions {ν : Type} [BEq ν]
    (nodes : List ν) (edges : List (ν × String × ν)) (spec : FairSpec ν) : List (List ν) :=
  ((sccsOf nodes edges).filter (isCyclicComp edges)).flatMap (fairRegion edges spec)

-- The nodes of `nodes` that can reach some node of `targets` (a backward BFS:
-- the queue holds targets, and every step collects the SOURCES of edges into
-- the queue head). Finite prefixes do not affect GF/FG, so
-- "starts a fair path" = "reaches a fair region" = reachingBackward of the
-- fair regions -- this is the `fair` atom of the fair-CTL scheme.
partial def reachingBackward {ν : Type} [BEq ν]
    (nodes : List ν) (edges : List (ν × String × ν)) (targets : List ν) : List ν :=
  let init := targets.filter fun s => nodes.contains s
  let rec walk (marked : List ν) (queue : List ν) : List ν :=
    match queue with
    | [] => marked
    | h :: t =>
        let preds :=
          (edges.filterMap fun (u, _, v) =>
            if v == h && nodes.contains u && !marked.contains u then some u else none).eraseDups
        walk (marked ++ preds) (t ++ preds)
  walk init init

-- Shortest path from start to target through nodes/edges, as the full node
-- list [start, ..., target] (start = target gives [start]).
partial def bfsPath {ν : Type} [BEq ν]
    (nodes : List ν) (edges : List (ν × String × ν)) (start target : ν) : Option (List ν) :=
  let rec bfs (queue : List (ν × List ν)) (visited : List ν) : Option (List ν) :=
    match queue with
    | [] => none
    | (curr, path) :: rest =>
        if curr == target then some path
        else
          let succs :=
            (edges.filterMap fun (u, _, v) =>
              if u == curr && nodes.contains v then some v else none).eraseDups
          let fresh := succs.filter fun v => !visited.contains v
          bfs (rest ++ fresh.map fun v => (v, path ++ [v])) (visited ++ fresh)
  bfs [(start, [start])] [start]

-- Shortest non-trivial closed walk [start, ..., start] with at least one
-- edge (the loop of a lasso that has no witnesses to chain: any cycle of
-- the region is fair). A self-loop start yields [start, start].
partial def bfsCycle {ν : Type} [BEq ν]
    (nodes : List ν) (edges : List (ν × String × ν)) (start : ν) : Option (List ν) :=
  let succs :=
    (edges.filterMap fun (u, _, v) =>
      if u == start && nodes.contains v then some v else none).eraseDups
  succs.foldl (fun best s =>
    match bfsPath nodes edges s start with
    | some path => match best with
      | some b => if path.length < b.length then some (start :: path) else best
      | none => some (start :: path)
    | none => best
  ) none

-- ============================================================================
-- The fair lasso (witness chaining)
--
-- The witnesses a fair cycle must visit / cross inside a fair region:
--   * the accepting node (LTL only),
--   * per actor: an own edge in the region (weak and strong alike), or --
--     weak fairness only -- a state where the actor is disabled. A strong-
--     fairness actor without an edge is disabled everywhere in the terminal
--     region (vacuous) and needs no witness.
-- Chaining = BFS segments between the witnesses through the region (strong
-- connectivity guarantees they exist), with edge witnesses crossed by their
-- own transition. Repeating the resulting closed walk forever satisfies
-- every constraint: each round it passes every state witness and crosses
-- every edge witness.
-- ============================================================================

inductive FairWit (ν : Type) where
  | node : ν → FairWit ν
  | edge : ν → ν → FairWit ν

def fairWitnesses {ν : Type} [BEq ν]
    (edges : List (ν × String × ν)) (spec : FairSpec ν) (region : List ν) : List (FairWit ν) :=
  let accepting := match spec.accept with
    | some acc => match region.find? acc with
      | some w => [FairWit.node w]
      | none => []   -- cannot happen: fairRegion rejected such regions
    | none => []
  let actorWits := spec.actors.flatMap fun a =>
    if actorEdgeIn edges a region then
      match edges.find? fun (u, act, v) => act == a && region.contains u && region.contains v with
      | some (u, _, v) => [FairWit.edge u v]
      | none => []    -- cannot happen (actorEdgeIn just held)
    else if !spec.strong then
      match region.find? fun s => !spec.enabled a s with
      | some w => [FairWit.node w]   -- a state where the actor is disabled
      | none => []   -- cannot happen: the weak level check demanded a witness
    else
      []   -- strong + no edge: the actor is vacuous in this region
  accepting ++ actorWits

-- Glue a BFS segment [curr, ..., next] onto the walk so far (which ends at
-- curr), without duplicating curr.
private def glue (acc : List ν) (seg : List ν) : List ν :=
  if acc.isEmpty then seg else acc.dropLast ++ seg

-- The closed walk through all witnesses, starting and ending at `first`.
-- Consecutive equal witnesses are no-ops: the BFS between equal endpoints
-- is the single-node path, and glue keeps the walk unchanged.
private partial def witLoop {ν : Type} [BEq ν]
    (edges : List (ν × String × ν)) (region : List ν)
    (first : ν) (wits : List (FairWit ν)) (curr : ν) (acc : List ν) : Option (List ν) :=
  match wits with
  | [] =>
      -- Close the walk back to the first witness. When curr = first the
      -- trivial bfsPath [first] would close with ZERO edges -- a "loop" that
      -- stands still; a genuine cycle of the region is needed instead.
      let closing? :=
        if curr == first then bfsCycle region edges curr
        else bfsPath region edges curr first
      closing?.map fun seg => glue acc seg
  | .node w :: rest =>
      match bfsPath region edges curr w with
      | some seg => witLoop edges region first rest w (glue acc seg)
      | none => none
  | .edge u v :: rest =>
      match bfsPath region edges curr u with
      | some seg => witLoop edges region first rest v ((glue acc seg) ++ [v])
      | none => none

-- A fair lasso from `start`: (prefix, loop) where the prefix is a BFS path
-- over the FULL node set handed in (for EG the Sat(phi)-restricted graph,
-- for the LTL product the whole reachable product), and the loop is the
-- witness-chained closed walk inside the fair `region`. The result follows
-- the NDFS trace invariant: the prefix ends with the loop seed, and the
-- loop is [seed, ..., seed]. none when start cannot reach the region.
partial def fairLasso {ν : Type} [BEq ν]
    (nodes : List ν) (edges : List (ν × String × ν)) (region : List ν)
    (spec : FairSpec ν) (start : ν) : Option (List ν × List ν) :=
  match fairWitnesses edges spec region with
  | [] =>
      -- No witnesses at all (CTL over a model whose actors are all vacuous):
      -- any cycle of the region is fair.
      match region with
      | [] => none              -- cannot happen: a region is never empty
      | seed :: _ =>
          match bfsPath nodes edges start seed with
          | some pref => (bfsCycle region edges seed).map fun loop => (pref, loop)
          | none => none
  | first :: rest =>
      let (seed, acc) := match first with
        | .node w => (w, [w])
        | .edge u v => (u, [u, v])
      match bfsPath nodes edges start seed with
      | some pref =>
          match witLoop edges region seed rest (match first with
            | .node _ => seed
            | .edge _ v => v) acc with
          | some loop => some (pref, loop)
          | none => none
      | none => none
