import TVL.TVIR.Frontend
import TVL.TVIR.Spec
import TVL.AtomicProposition
import Test.E2E.LTL.Harness
import Test.E2E.CTL.Harness
import Test.Unit.TVIR

-- ============================================================================
-- Unit tests for the spec frontend of TVL dumps (TVL/TVIR/Spec.lean):
--   * the LTL and CTL formula parsers;
--   * the correct GENERATION of every TVL template and label-based
--     property (docs/specifications/{template,label-based}.md of the TVL
--     repo): FinishingProperty, ValidityProperty, MsgDeliveredProperty,
--     AllTemplateProperties, RecoveryProperty, LossDetectionProperty;
--   * the assembled spec set (both logics) and the verdicts end to end;
--   * the CLI with a ctl spec in the dump.
-- The .tvir scanning itself is tested in Test/Unit/TVIR.lean; the
-- fixtures come from there.
-- ============================================================================

-- ============================================================================
-- 1. The LTL formula parser
-- ============================================================================

def pf (s : String) : Except String LTL := parseLtlFormula exampleDoc s

def expectedFinish : LTL :=
  F (LTL.and (LTL.ap (AtomicProposition.actorFinished "R1"))
        (LTL.and (LTL.ap (AtomicProposition.actorFinished "R2"))
                 (LTL.ap (AtomicProposition.actorFinished "R3"))))

def expectedRecovery : LTL :=
  G (LTL.not (LTL.and (LTL.ap (AtomicProposition.actorAt "R2" 7))
                 (LTL.not (F (LTL.ap (AtomicProposition.actorAt "R2" 10))))))

#assert! eqOk (pf "F (R1.ACTOR_END && R2.ACTOR_END && R3.ACTOR_END)") expectedFinish
#assert! eqOk (pf "[] (R2.fail_send -> <> R2.start_send)") expectedRecovery

-- The letter spellings of the operators parse into the same trees.
#assert! eqOk (pf "<> (R1.ACTOR_END && R2.ACTOR_END && R3.ACTOR_END)") expectedFinish
#assert! eqOk (pf "G (R2.fail_send -> F R2.start_send)") expectedRecovery

-- X and U, in both parenthesized and tight forms.
#assert! eqOk (pf "X R2.fail_send") (LTL.next (LTL.ap (AtomicProposition.actorAt "R2" 7)))
#assert! eqOk (pf "R2.fail_send U R2.start_send") (LTL.until_ (LTL.ap (AtomicProposition.actorAt "R2" 7)) (LTL.ap (AtomicProposition.actorAt "R2" 10)))

def parseErrorsOk : Bool :=
  isErrContaining (pf "") "empty formula"
  && isErrContaining (pf "R2.nosuch") "unknown label"
  && isErrContaining (pf "( R2.fail_send") "')'"
  && isErrContaining (pf "R2.fail_send &&") "unexpected end"
  && isErrContaining (pf "R2.fail_send && )") "unexpected token"

#assert! parseErrorsOk

-- ============================================================================
-- 2. The CTL formula parser
-- ============================================================================

def cf (s : String) : Except String CTL := parseCtlFormula exampleDoc s

def apAt (a : String) (pc : Int) : CTL := CTL.ap (AtomicProposition.actorAt a pc)
def apFin (a : String) : CTL := CTL.ap (AtomicProposition.actorFinished a)

-- The dump example: AG (R2.start_send -> EF R3.ACTOR_END), fully encoded
-- into the ex/eu/eg core.
def expectedCanFinish : CTL :=
  CTL.not (CTL.eu CTL.top
    (CTL.not (ctlImpl (apAt "R2" 10) (CTL.eu CTL.top (apFin "R3")))))

#assert! eqOk (cf "AG (R2.start_send -> EF R3.ACTOR_END)") expectedCanFinish

-- The unary path quantifier prefixes.
#assert! eqOk (cf "EX R2.fail_send") (CTL.ex (apAt "R2" 7))
#assert! eqOk (cf "EF R3.ACTOR_END") (CTL.eu CTL.top (apFin "R3"))
#assert! eqOk (cf "EG R3.ACTOR_END") (CTL.eg (apFin "R3"))
#assert! eqOk (cf "AX R2.fail_send") (CTL.not (CTL.ex (CTL.not (apAt "R2" 7))))
#assert! eqOk (cf "AF R3.ACTOR_END") (CTL.not (CTL.eg (CTL.not (apFin "R3"))))
#assert! eqOk (cf "AG R3.ACTOR_END") (CTL.not (CTL.eu CTL.top (CTL.not (apFin "R3"))))

-- The binary until forms.
#assert! eqOk (cf "E (R2.fail_send U R3.ACTOR_END)") (CTL.eu (apAt "R2" 7) (apFin "R3"))
def expectedAU : CTL :=
  CTL.not (ctlOr (CTL.eu (CTL.not (apFin "R3"))
                          (CTL.and (CTL.not (apAt "R2" 7)) (CTL.not (apFin "R3"))))
                  (CTL.eg (CTL.not (apFin "R3"))))
#assert! eqOk (cf "A (R2.fail_send U R3.ACTOR_END)") expectedAU

-- Boolean connectives encode exactly as in LTL, and true/false parse.
#assert! eqOk (cf "R2.fail_send -> R2.start_send")
  (ctlImpl (apAt "R2" 7) (apAt "R2" 10))
#assert! eqOk (cf "R2.fail_send || R2.start_send")
  (ctlOr (apAt "R2" 7) (apAt "R2" 10))
#assert! eqOk (cf "true") CTL.top
#assert! eqOk (cf "!false") (CTL.not (CTL.not CTL.top))

-- Errors: shared with LTL (atoms) plus the CTL-specific shapes.
def ctlErrorsOk : Bool :=
  isErrContaining (cf "") "empty formula"
  && isErrContaining (cf "R2.nosuch") "unknown label"
  && isErrContaining (cf "EX") "unexpected end"
  && isErrContaining (cf "E (R2.fail_send R3.ACTOR_END)") "expected 'U'"
  && isErrContaining (cf "A (R2.fail_send U R3.ACTOR_END") "')'"
  && isErrContaining (cf "G (R2.fail_send)") "unexpected token" -- LTL spelling, not CTL

#assert! ctlErrorsOk

-- ============================================================================
-- 3. Template and label-based properties: correct generation
-- ============================================================================

-- The example model with other templates / extra labels.
def tmplDoc (templates : List String) (extraLabels : List (String × String × Int)) : TVIRDocument :=
  { exampleDoc with templateSpecs := templates, labels := exampleDoc.labels ++ extraLabels }

-- The actors and the queues of the example model (in first-appearance
-- order, as expandTemplates sees them).
def exampleActors : List String := ["R1", "R2", "R3"]
def exampleQueues : List String := ["Q[R3][R1]", "Q[R2][R1]", "Q[R3][R2]"]

def expand (doc : TVIRDocument) : List (String × LTL) := (expandTemplates doc).2
def expandWarn (doc : TVIRDocument) : List String := (expandTemplates doc).1

-- The loss-detection label pair of the tests: the expiring side on R3
-- (instruction 13), the detector on the other actor R2 (instruction 9).
def lossLabels : List (String × String × Int) :=
  [("R3", "expired_msg_X", 13), ("R2", "X_loss_detected", 9)]

-- FinishingProperty: F (A1.ACTOR_END && ... && An.ACTOR_END).
def finishingOk : Bool :=
  expand (tmplDoc ["FinishingProperty"] []) == [("FinishingProperty", expectedFinish)]
  && (expandWarn (tmplDoc ["FinishingProperty"] [])).isEmpty

#assert! finishingOk

-- ValidityProperty ("if the protocol terminates, all channels must be
-- empty"): one F (A_i.ACTOR_END -> queue_k empty) spec per actor x channel
-- pair -- the conjunction is split so that every check stays small (the
-- LTL engine's atom enumeration is exponential in the formula size).
def validityOk : Bool :=
  expand (tmplDoc ["ValidityProperty"] [])
    == (exampleActors.flatMap fun a =>
         exampleQueues.map fun q =>
           (s!"ValidityProperty_{a}_{q}",
            F (ltlImpl (LTL.ap (AtomicProposition.actorFinished a))
                       (LTL.ap (AtomicProposition.queueEmpty q)))))
  && (expandWarn (tmplDoc ["ValidityProperty"] [])).isEmpty

#assert! validityOk

-- MsgDeliveredProperty: every sent message is eventually received; a
-- message counts as received once its channel drains -- one spec per
-- channel that ever gets a send (split for the same reason).
def msgDeliveredOk : Bool :=
  expand (tmplDoc ["MsgDeliveredProperty"] [])
    == (exampleQueues.map fun q =>
         (s!"MsgDeliveredProperty_{q}",
          G (ltlImpl (LTL.not (LTL.ap (AtomicProposition.queueEmpty q)))
                     (F (LTL.ap (AtomicProposition.queueEmpty q))))))
  && (expandWarn (tmplDoc ["MsgDeliveredProperty"] [])).isEmpty

#assert! msgDeliveredOk

-- RecoveryProperty: one G (A.fail_X -> F A.start_X) per label pair.
def recoveryOk : Bool :=
  expand (tmplDoc ["RecoveryProperty"] [])
    == [("RecoveryProperty_R2_fail_send_0", expectedRecovery)]
  && (expandWarn (tmplDoc ["RecoveryProperty"] [])).isEmpty

#assert! recoveryOk

-- LossDetectionProperty: one G (A.expired_msg_M -> F B.M_loss_detected)
-- per label pair (the docs recommend the two labels on different actors).
def lossDetectionOk : Bool :=
  expand (tmplDoc ["LossDetectionProperty"] lossLabels)
    == [(s!"LossDetectionProperty_R3_expired_msg_X_0",
         G (ltlImpl (LTL.ap (AtomicProposition.actorAt "R3" 13))
                    (F (LTL.ap (AtomicProposition.actorAt "R2" 9)))))]
  && (expandWarn (tmplDoc ["LossDetectionProperty"] lossLabels)).isEmpty

#assert! lossDetectionOk

-- Unpaired / missing labels warn instead of generating anything.
def lossUnpairedOk : Bool :=
  let (ws, ss) := expandTemplates (tmplDoc ["LossDetectionProperty"] [("R3", "expired_msg_Y", 13)])
  ss.isEmpty
  && ws.any (fun w => w.contains "Y_loss_detected")
  && ws.any (fun w => w.contains "nothing generated")

#assert! lossUnpairedOk

-- A model without sends generates no MsgDeliveredProperty, only a warning.
def msgDeliveredNoSendsOk : Bool :=
  let (ws, ss) := expandTemplates { loopDoc with templateSpecs := ["MsgDeliveredProperty"] }
  ss.isEmpty
  && ws.any (fun w => w.contains "no message-sending instructions")

#assert! msgDeliveredNoSendsOk

-- AllTemplateProperties: exactly every property above, in this order.
def allTemplatesOk : Bool :=
  let doc := tmplDoc ["AllTemplateProperties"] lossLabels
  expand doc
    == expand (tmplDoc ["FinishingProperty"] [])
       ++ expand (tmplDoc ["ValidityProperty"] [])
       ++ expand (tmplDoc ["MsgDeliveredProperty"] [])
       ++ expand (tmplDoc ["RecoveryProperty"] [])
       ++ expand (tmplDoc ["LossDetectionProperty"] lossLabels)
  && (expandWarn doc).isEmpty

#assert! allTemplatesOk

-- An unknown template produces no specs and one warning listing the known ones.
def bogusTemplateOk : Bool :=
  match checkedSpecs bogusDoc with
  | .ok s =>
      s.ltl.isEmpty
      && s.ctl.isEmpty
      && s.warnings == ["unknown template spec 'Bogus', skipping (known: FinishingProperty, ValidityProperty, MsgDeliveredProperty, AllTemplateProperties, RecoveryProperty, LossDetectionProperty)"]
  | .error _ => false

#assert! bogusTemplateOk

-- ============================================================================
-- 4. The assembled spec set
-- ============================================================================

-- The example dump plus the ctl user spec (as in Examples/simple.tvir).
def ctlExampleDoc : TVIRDocument :=
  { exampleDoc with userSpecs := exampleDoc.userSpecs ++
      [{ logic := "ctl", name := "CanFinish", formula := "AG (R2.start_send -> EF R3.ACTOR_END)" }] }

def ctlExampleSpecs : SpecSet :=
  match checkedSpecs ctlExampleDoc with
  | .ok s => s
  | .error _ => { ltl := [], ctl := [], warnings := [] }

-- Templates first, then user specs; ctl specs land in their own list.
def specNamesOk : Bool :=
  ctlExampleSpecs.ltl.map (·.1)
    == ["FinishingProperty", "RecoveryProperty_R2_fail_send_0",
        "FinishDuplicate", "RecoveryProperty_R2_fail_send_0"]
  && ctlExampleSpecs.ctl.map (·.1) == ["CanFinish"]
  && (ctlExampleSpecs.ctl[0]?).map (·.2) == some expectedCanFinish
  && ctlExampleSpecs.warnings.isEmpty

#assert! specNamesOk

-- A formula error is annotated with the spec name (both logics).
def specErrorNamesOk : Bool :=
  (match checkedSpecs { exampleDoc with userSpecs :=
      [{ logic := "ltl", name := "BadSpec", formula := "R2.nosuch" }] } with
   | .error m => m.contains "spec 'BadSpec'" && m.contains "unknown label"
   | .ok _ => false)
  && (match checkedSpecs { exampleDoc with userSpecs :=
      [{ logic := "ctl", name := "BadCtl", formula := "R2.nosuch" }] } with
   | .error m => m.contains "spec 'BadCtl'" && m.contains "unknown label"
   | .ok _ => false)

#assert! specErrorNamesOk

-- ============================================================================
-- 5. Verdicts end to end
-- ============================================================================

def specByName (s : SpecSet) (nm : String) : LTL :=
  match s.ltl.find? fun (n, _) => n == nm with
  | some (_, f) => f
  | none => LTL.top

def ctlByName (s : SpecSet) (nm : String) : CTL :=
  match s.ctl.find? fun (n, _) => n == nm with
  | some (_, f) => f
  | none => CTL.top

-- The example model is finite (every run reaches IREnd), so all its F-specs
-- hold; the recovery property holds because the fail_7 -> start_10 loop of
-- R2 can only be exited via 10.
#eval expectVerify exampleState (specByName ctlExampleSpecs "FinishingProperty") true
#eval expectVerify exampleState (specByName ctlExampleSpecs "RecoveryProperty_R2_fail_send_0") true
#eval expectVerify exampleState (specByName ctlExampleSpecs "FinishDuplicate") true

-- The generated ValidityProperty / MsgDeliveredProperty also hold on the
-- example model: every run ends with drained channels.
def templateSpecsOf (templates : List String) : SpecSet :=
  match checkedSpecs (tmplDoc templates []) with
  | .ok s => s
  | .error _ => { ltl := [], ctl := [], warnings := [] }

#eval expectVerify exampleState (specByName (templateSpecsOf ["ValidityProperty"]) "ValidityProperty_R1_Q[R3][R1]") true
#eval expectVerify exampleState (specByName (templateSpecsOf ["MsgDeliveredProperty"]) "MsgDeliveredProperty_Q[R3][R1]") true

def loopState : State :=
  match buildInitialState loopDoc with
  | .ok s => s
  | .error _ => { queues := [], guardVars := [], actorThreads := [], actorGraphs := [] }

def loopSpecs : SpecSet :=
  match checkedSpecs loopDoc with
  | .ok s => s
  | .error _ => { ltl := [], ctl := [], warnings := [] }

-- The skip loop never ends: F (A.ACTOR_END) is violated (a lasso
-- counterexample exists), while staying at the entry PC holds forever.
#eval expectVerify loopState (specByName loopSpecs "NeverEnds") false
#eval expectVerify loopState (specByName loopSpecs "StaysAtStart") true

-- CTL verdicts on the example model:
#eval expectVerify exampleState (ctlByName ctlExampleSpecs "CanFinish") true
-- AG (R1.ACTOR_END) fails: initially R1 has not finished yet.
#eval expectVerify exampleState (CTL.not (CTL.eu CTL.top (CTL.not (apFin "R1")))) false
-- The twin of the E2E CTL safety property: Q[R3][R1] can become non-empty.
def propQueueSafety : CTL :=
  CTL.not (CTL.eu CTL.top (CTL.not (CTL.ap (AtomicProposition.queueEmpty "Q[R3][R1]"))))
#eval expectVerify exampleState propQueueSafety false
-- R3 is guaranteed to finish: AF (R3.ACTOR_END).
#eval expectVerify exampleState (CTL.not (CTL.eg (CTL.not (apFin "R3")))) true

-- CTL verdicts on the loop model (parsed through the surface syntax).
def loopCtl (s : String) : CTL :=
  match parseCtlFormula loopDoc s with
  | .ok f => f
  | .error _ => CTL.not CTL.top

#eval expectVerify loopState (loopCtl "EF (A.ACTOR_END)") false
#eval expectVerify loopState (loopCtl "AG (A.start_loop)") true

-- ============================================================================
-- 6. The CLI smoke tests
-- ============================================================================

-- Both logics in one run: the example dump with its ctl spec.
#eval show IO Unit from do
  let out ← IO.Process.output { cmd := "lake", args := #["exe", "curtis", "Examples/simple.tvir"] }
  unless out.exitCode == 0 do
    throw (IO.userError s!"test failed: smoke: lake exe curtis Examples/simple.tvir exited with {out.exitCode}\nstdout:\n{out.stdout}\nstderr:\n{out.stderr}")
  unless out.stdout.contains "[ltl] FinishingProperty: HOLDS" do
    throw (IO.userError s!"test failed: smoke: no '[ltl] FinishingProperty: HOLDS' in stdout:\n{out.stdout}")
  unless out.stdout.contains "[ctl] CanFinish: HOLDS" do
    throw (IO.userError s!"test failed: smoke: no '[ctl] CanFinish: HOLDS' in stdout:\n{out.stdout}")

-- A violated ctl spec: exit code 1 and a VIOLATED verdict.
#eval show IO Unit from do
  let dump := "Actor: A\n  0: IRSkip(0,1,(-1,-1),0)\n\nUser specs:\n  ctl Stuck: EF (A.ACTOR_END)\n"
  IO.FS.writeFile "/tmp/curtis_test_ctl_loop.tvir" dump
  let out ← IO.Process.output { cmd := "lake", args := #["exe", "curtis", "/tmp/curtis_test_ctl_loop.tvir"] }
  unless out.exitCode == 1 do
    throw (IO.userError s!"test failed: smoke: expected exit code 1, got {out.exitCode}\nstdout:\n{out.stdout}\nstderr:\n{out.stderr}")
  unless out.stdout.contains "[ctl] Stuck: VIOLATED" do
    throw (IO.userError s!"test failed: smoke: no '[ctl] Stuck: VIOLATED' in stdout:\n{out.stdout}")

-- --channel-size: the queue bound is per run, and it can flip a verdict.
-- With the default capacity the sender queues both messages and finishes;
-- with capacity 1 the second send blocks forever (nobody drains), so
-- EF (A.ACTOR_END) stops holding. A bad value is a usage error.
#eval show IO Unit from do
  let dump := "Actor: A\n  0: IRQueuePush(0,1,(-1,-1),1,Q[B][A],M)\n  1: IRQueuePush(1,2,(-1,-1),2,Q[B][A],M)\n  2: IREnd(2,3,(-1,-1))\n\nUser specs:\n  ctl CanDouble: EF (A.ACTOR_END)\n"
  IO.FS.writeFile "/tmp/curtis_test_chan.tvir" dump
  let plain ← IO.Process.output { cmd := "lake", args := #["exe", "curtis", "/tmp/curtis_test_chan.tvir"] }
  unless plain.exitCode == 0 do
    throw (IO.userError s!"test failed: smoke: default capacity exited with {plain.exitCode}\nstdout:\n{plain.stdout}\nstderr:\n{plain.stderr}")
  unless plain.stdout.contains "[ctl] CanDouble: HOLDS" do
    throw (IO.userError s!"test failed: smoke: no '[ctl] CanDouble: HOLDS' in stdout:\n{plain.stdout}")
  let bounded ← IO.Process.output
    { cmd := "lake", args := #["exe", "curtis", "--channel-size", "1", "/tmp/curtis_test_chan.tvir"] }
  unless bounded.exitCode == 1 do
    throw (IO.userError s!"test failed: smoke: --channel-size 1 exited with {bounded.exitCode}\nstdout:\n{bounded.stdout}\nstderr:\n{bounded.stderr}")
  unless bounded.stdout.contains "[ctl] CanDouble: VIOLATED" do
    throw (IO.userError s!"test failed: smoke: no '[ctl] CanDouble: VIOLATED' in stdout:\n{bounded.stdout}")
  let bad ← IO.Process.output
    { cmd := "lake", args := #["exe", "curtis", "--channel-size", "x", "/tmp/curtis_test_chan.tvir"] }
  unless bad.exitCode == 2 do
    throw (IO.userError s!"test failed: smoke: --channel-size x exited with {bad.exitCode}, expected 2\nstdout:\n{bad.stdout}\nstderr:\n{bad.stderr}")
