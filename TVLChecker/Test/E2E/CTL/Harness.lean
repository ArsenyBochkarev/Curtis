import TVLChecker.Test.Harness
import TVLChecker.Engine.CTL

instance : Verifyiable CTL where
  verifyAndExplain startState phi :=
    let g := generateGraph startState
    let markedGraph := checkCTL g phi
    let isTrue := match markedGraph.labels.lookup startState with
      | some ctls => ctls.contains phi
      | none => false

    if isTrue then
      (true, none)
    else
      (false, getCounterexample markedGraph startState phi)
