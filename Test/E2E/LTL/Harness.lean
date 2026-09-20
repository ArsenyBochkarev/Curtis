import Test.Harness
import Engine.LTL


instance : Verifyiable LTL where
  verifyAndExplain startState phi :=
    -- checkLTL searches for an accepting run of ¬φ:
    --   none       => no counterexample, φ holds on every execution
    --   some trace => a run violating φ was found => the lasso is the counterexample
    match checkLTL startState phi with
    | some trace => (false, some (traceToActions trace))
    | none => (true, none)
