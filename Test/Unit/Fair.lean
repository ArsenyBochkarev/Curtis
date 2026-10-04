import Engine.Fair
import Test.Harness

-- ============================================================================
-- Unit tests of the fair-cycle machinery (Engine/Fair.lean) over small
-- synthetic graphs: Int nodes, actor names "A" / "B". The state predicates
-- are handed in explicitly, so every level check and the witness chaining
-- are exercised in isolation, without a TVL model behind them.
-- ============================================================================

-- An edge of a synthetic graph
def ed (u : Int) (a : String) (v : Int) : FairEdge Int := (u, a, v)

-- A fairness spec over Int nodes: "A" and "B" with explicitly listed
-- enabled nodes (an actor not in the map is disabled everywhere).
def mkSpec (actors : List String) (strong : Bool) (enabledA enabledB : List Int)
    (accept : Option (Int → Bool)) : FairSpec Int := {
  actors  := actors,
  accept  := accept,
  strong  := strong,
  enabled := fun a s =>
    match a with
    | "A" => enabledA.contains s
    | "B" => enabledB.contains s
    | _ => false
}

def noAcc : Option (Int → Bool) := none

-- ============================================================================
-- Weak fairness
-- ============================================================================

-- A cycle 1 <-> 2 executed by B. Actor A is enabled at BOTH states and has
-- no own edge: every cycle is A-unfair (A enabled all along, never executes)
-- -- the region is dead, no recursion could help.
#assert!
  fairRegions [1, 2] [ed 1 "B" 2, ed 2 "B" 1]
    (mkSpec ["A", "B"] false [1, 2] [] noAcc) == []

-- The same graph, but A is disabled at 2: the cycle passes through a state
-- where A is disabled, so WF_A holds vacuously -- the whole SCC is fair.
#assert!
  fairRegions [1, 2] [ed 1 "B" 2, ed 2 "B" 1]
    (mkSpec ["A", "B"] false [1] [] noAcc) == [[1, 2]]

-- A has an own edge inside the region: the cycle crosses it, GF executes A.
#assert!
  fairRegions [1, 2] [ed 1 "A" 2, ed 2 "B" 1]
    (mkSpec ["A", "B"] false [1, 2] [2] noAcc) == [[1, 2]]

-- A one-node region counts only with a self-loop: a deadlock is no cycle.
#assert! fairRegions [1] [ed 1 "A" 1] (mkSpec ["A"] false [1] [] noAcc) == [[1]]
#assert! fairRegions [1] [] (mkSpec ["A"] false [] [] noAcc) == []

-- The Buchi condition (the LTL engine's accepting atom) is a state witness
-- of the same weak kind: a region without an accepting node is dead, and no
-- sub-region can gain one.
#assert!
  fairRegions [1, 2] [ed 1 "B" 2, ed 2 "B" 1]
    (mkSpec ["A", "B"] false [] [] (some (· == 2))) == [[1, 2]]
#assert!
  fairRegions [1, 2] [ed 1 "B" 2, ed 2 "B" 1]
    (mkSpec ["A", "B"] false [] [] (some (· == 5))) == []

-- ============================================================================
-- Strong fairness -- THE sub-cycle regression
-- ============================================================================

-- One maximal SCC {1,2,3} glued by B-edges; A is enabled ONLY at 1 and has
-- no own edge. On any cycle through 1 the actor is enabled at some position
-- (at 1), so SF_A demands an A-edge -- there is none; a fair cycle must
-- avoid the enabled node 1 altogether and live in {2,3}. The maximal SCC
-- alone would be judged dead (A enabled somewhere, no A-edge) -- the
-- recursion must find the fair sub-region {2,3}.
#assert!
  fairRegions [1, 2, 3] [ed 1 "B" 2, ed 2 "B" 1, ed 2 "B" 3, ed 3 "B" 2]
    (mkSpec ["A", "B"] true [1] [] noAcc) == [[2, 3]]

-- The same graph under WEAK fairness needs no recursion: node 2 (or 3) is a
-- state where A is disabled, so the whole SCC is already fair.
#assert!
  fairRegions [1, 2, 3] [ed 1 "B" 2, ed 2 "B" 1, ed 2 "B" 3, ed 3 "B" 2]
    (mkSpec ["A", "B"] false [1] [] noAcc) == [[1, 2, 3]]

-- Strong fairness with an A-edge in the region: no recursion, the cycle
-- crosses the edge and satisfies SF_A regardless of the enabled states.
#assert!
  fairRegions [1, 2, 3] [ed 1 "A" 2, ed 2 "B" 1, ed 2 "B" 3, ed 3 "B" 2]
    (mkSpec ["A", "B"] true [1, 2, 3] [] noAcc) == [[1, 2, 3]]

-- A disabled EVERYWHERE: vacuous under strong fairness too (the premise
-- GF enabled A is false on every cycle), the region is fair as-is.
#assert!
  fairRegions [1, 2] [ed 1 "B" 2, ed 2 "B" 1]
    (mkSpec ["A", "B"] true [] [] noAcc) == [[1, 2]]

-- The dead case is dead under strong fairness as well: A enabled at both
-- nodes, no A-edge, and removing the enabled nodes leaves nothing.
#assert!
  fairRegions [1, 2] [ed 1 "B" 2, ed 2 "B" 1]
    (mkSpec ["A", "B"] true [1, 2] [] noAcc) == []

-- Two failing actors at once: the fair cycle must avoid the enabled nodes
-- of BOTH A (enabled at 1) and B (enabled at 2); only {3, 4} survives.
#assert!
  fairRegions [1, 2, 3, 4]
    [ed 1 "C" 2, ed 2 "C" 1, ed 2 "C" 3, ed 3 "C" 4, ed 4 "C" 3]
    (mkSpec ["A", "B"] true [1] [2] noAcc) == [[3, 4]]

-- ============================================================================
-- reachingBackward / bfsPath / bfsCycle
-- ============================================================================

#assert!
  (reachingBackward [0, 1, 2, 3] [ed 0 "A" 1, ed 1 "A" 2, ed 2 "A" 3] [3]).all
    (fun s => [0, 1, 2, 3].contains s)
    && (reachingBackward [0, 1, 2, 3] [ed 0 "A" 1, ed 1 "A" 2, ed 2 "A" 3] [3]).length == 4

#assert!
  (reachingBackward [0, 1, 2, 3] [ed 0 "A" 1, ed 1 "A" 2, ed 2 "A" 3] [2]).length == 3
    -- 3 does not reach 2
    && !(reachingBackward [0, 1, 2, 3] [ed 0 "A" 1, ed 1 "A" 2, ed 2 "A" 3] [2]).contains 3

#assert! bfsPath [1, 2, 3] [ed 1 "A" 2, ed 2 "A" 3] 1 3 == some [1, 2, 3]
#assert! bfsPath [1, 2, 3] [ed 1 "A" 2, ed 2 "A" 3] 3 1 == none
#assert! bfsPath [1, 2, 3] [ed 1 "A" 2, ed 2 "A" 3] 2 2 == some [2]

-- A self-loop closes over itself: [1, 1]
#assert! bfsCycle [1] [ed 1 "A" 1] 1 == some [1, 1]

-- ============================================================================
-- fairLasso -- the witness-chained lasso
-- ============================================================================

-- Prefix into the region + loop through the witnesses. The graph: 0 -> 1
-- (prefix), the region 1 <-> 2 glued by B-edges; A is disabled everywhere
-- (vacuous, no witness), so the only witness is a B-edge, and the loop must
-- cross it. The exact shape depends on which B-edge is picked first; the
-- invariants hold for any choice: the prefix ends with the loop seed, the
-- loop starts and ends with it, and every hop is an edge.
def lassoSpec : FairSpec Int := mkSpec ["A", "B"] false [] [] noAcc
def lassoRegion : List Int := [1, 2]
def lassoEdges : List (FairEdge Int) := [ed 0 "B" 1, ed 1 "B" 2, ed 2 "B" 1]

#eval show IO Unit from do
  let some (pref, loop) := fairLasso [0, 1, 2] lassoEdges lassoRegion lassoSpec 0
    | throw (IO.userError "test failed: fairLasso returned none")
  unless pref.getLast! == loop.head! do
    throw (IO.userError s!"test failed: prefix {pref} does not end with the seed {loop.head!}")
  unless loop.head! == loop.getLast! do
    throw (IO.userError s!"test failed: loop {loop} is not closed")
  unless loop.length > 1 do
    throw (IO.userError s!"test failed: loop {loop} has no edges")
  -- every consecutive pair of the whole lasso is an edge of the graph (the
  -- prefix already ends with the seed = loop head, so the walk continues
  -- with the loop's TAIL)
  let whole := pref ++ loop.drop 1
  unless (whole.zip (whole.drop 1)).all fun (a, b) =>
      lassoEdges.any fun (u, _, v) => u == a && v == b do
    throw (IO.userError s!"test failed: {whole} is not a path of the graph")
  -- the loop crosses a B-edge (the witness): some hop of the loop is B's
  unless (loop.zip (loop.drop 1)).any fun (a, b) =>
      lassoEdges.any fun (u, act, v) => u == a && v == b && act == "B" do
    throw (IO.userError s!"test failed: loop {loop} crosses no B-edge")

-- An accepting node is a state witness: the loop must pass through it.
-- Region 1 <-> 2 <-> 3 (B-edges), accept = (· == 3): the only witness is
-- node 3 itself, so the loop starts there and closes over a real cycle.
#eval show IO Unit from do
  let spec := mkSpec ["A", "B"] false [] [] (some (· == 3))
  let edges := [ed 0 "B" 1, ed 1 "B" 2, ed 2 "B" 1, ed 2 "B" 3, ed 3 "B" 2]
  let some (_, loop) := fairLasso [0, 1, 2, 3] edges [1, 2, 3] spec 0
    | throw (IO.userError "test failed: fairLasso returned none")
  unless loop.contains 3 do
    throw (IO.userError s!"test failed: loop {loop} misses the accepting witness 3")
  unless loop.head! == loop.getLast! do
    throw (IO.userError s!"test failed: loop {loop} is not closed")
  unless loop.length > 1 do
    throw (IO.userError s!"test failed: loop {loop} has no edges")
  unless (loop.zip (loop.drop 1)).all fun (a, b) =>
      edges.any fun (u, _, v) => u == a && v == b do
    throw (IO.userError s!"test failed: loop {loop} is not a walk of the region")

-- A weak-fairness state witness: A is enabled only at 1, so the loop must
-- pass through a state where A is disabled (any of 2, 3 here) -- it will,
-- but the property to assert is the invariant again, plus that the loop is
-- a closed walk of the region.
#eval show IO Unit from do
  let spec := mkSpec ["A", "B"] false [1] [] noAcc
  let some (_, loop) := fairLasso [0, 1, 2, 3] lassoEdges lassoRegion spec 0
    | throw (IO.userError "test failed: fairLasso returned none")
  unless (loop.zip (loop.drop 1)).all fun (a, b) =>
      lassoEdges.any fun (u, _, v) => u == a && v == b do
    throw (IO.userError s!"test failed: loop {loop} is not a walk of the region")
