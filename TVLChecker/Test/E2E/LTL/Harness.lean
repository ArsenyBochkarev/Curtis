import TVLChecker.Test.Harness
import TVLChecker.Engine.LTL

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

instance : Verifyiable LTL where
  verifyAndExplain startState phi :=
    -- checkLTL searches for an accepting run of ¬φ:
    --   none       => no counterexample, φ holds on every execution
    --   some trace => a run violating φ was found => the lasso is the counterexample
    match checkLTL startState phi with
    | some trace => (false, some (traceToActions trace))
    | none => (true, none)
