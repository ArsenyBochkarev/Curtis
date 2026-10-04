import TVL.TVIR.Frontend
import TVL.TVIR.Spec
import Test.Harness

-- ============================================================================
-- Unit tests for the .tvir document scanner and the State builder
-- (TVL/TVIR/Frontend.lean + buildInitialState of TVL/TVIR/Spec.lean)
--
-- The fixtures are plain strings in this file: the example dump from the
-- TVL documentation (also Examples/simple.tvir), its CRLF twin, a minimal
-- infinite model (also Examples/loop.tvir), a dump with an unknown
-- template spec, and a sender without a consumer for the bounded-channel
-- checks. Every check is a named boolean + #assert! (pattern 1 of
-- the cheat sheet in Test/Harness.lean).
-- The spec frontend itself -- formula parsers, template expansion, spec
-- set, verdicts -- and the CLI smoke tests (pattern 3: the binary run
-- on Examples/simple.tvir and the flag handling) are in Test/Unit/TVL.lean
-- (it imports this module and reuses the fixtures).
-- ============================================================================

-- ============================================================================
-- Fixtures
-- ============================================================================

def exampleDump : String := String.intercalate "\n" [
  "Actor: R1",
  "  1: IRQueuePush(1,4,(-1,-1),2,Q[R3][R1],Y)",
  "  2: IRQueuePush(2,5,(-1,-1),3,Q[R2][R1],X)",
  "  3: IREnd(3,6,(-1,-1))",
  "",
  "Actor: R2",
  "  4: IRQueuePop(4,9,(-1,-1),5,Q[R2][R1],X)",
  "  5: IRChoice(5,10,(-1,-1),List(7, 8))",
  "  7: IRSkip(7,11,(-1,-1),10)",
  "  8: IRQueuePush(8,14,(-1,-1),12,Q[R3][R2],X)",
  "  9: IREnd(9,16,(-1,-1))",
  "  10: IRQueuePush(10,12,(-1,-1),11,Q[R3][R2],X)",
  "  11: IRJump(11,10,(-1,-1),9)",
  "  12: IRJump(12,10,(-1,-1),9)",
  "",
  "Actor: R3",
  "  13: IRBranch(13,20,(-1,-1),List(QueueCondition(Q[R3][R2],X,18), QueueCondition(Q[R3][R1],Y,21)),None)",
  "  15: IREnd(15,25,(-1,-1))",
  "  17: IRJump(17,19,(-1,-1),13)",
  "  18: IRJump(18,21,(-1,-1),15)",
  "  20: IRJump(20,20,(-1,-1),17)",
  "  21: IRSkip(21,22,(-1,-1),22)",
  "  22: IRJump(22,20,(-1,-1),17)",
  "",
  "Template specs:",
  "  FinishingProperty",
  "  RecoveryProperty",
  "",
  "User specs:",
  "  ltl FinishDuplicate: F (R1.ACTOR_END && R2.ACTOR_END && R3.ACTOR_END)",
  "  ltl RecoveryProperty_R2_fail_send_0: [] (R2.fail_send -> <> R2.start_send)",
  "",
  "Labels:",
  "  R2.fail_send: 7",
  "  R2.start_send: 10",
  ""]

def crlfDump : String := exampleDump.replace "\n" "\r\n"

def loopDump : String := String.intercalate "\n" [
  "Actor: A",
  "  0: IRSkip(0,1,(-1,-1),0)",
  "",
  "User specs:",
  "  ltl NeverEnds: F (A.ACTOR_END)",
  "  ltl StaysAtStart: G (A.start_loop)",
  "",
  "Labels:",
  "  A.start_loop: 0",
  ""]

-- An unknown template: expands to nothing, warns once.
def bogusDump : String := String.intercalate "\n" [
  "Actor: A",
  "  0: IRSkip(0,1,(-1,-1),0)",
  "",
  "Template specs:",
  "  Bogus",
  ""]

-- Parsers fail loud in tests too: on an error the fixture degrades to an
-- empty document, and every shape assertion below collapses to false.
def exampleDoc : TVIRDocument :=
  match parseTVIR exampleDump with
  | .ok d => d
  | .error _ => { actors := [], templateSpecs := [], userSpecs := [], labels := [], warnings := [] }

def loopDoc : TVIRDocument :=
  match parseTVIR loopDump with
  | .ok d => d
  | .error _ => { actors := [], templateSpecs := [], userSpecs := [], labels := [], warnings := [] }

def bogusDoc : TVIRDocument :=
  match parseTVIR bogusDump with
  | .ok d => d
  | .error _ => exampleDoc

-- Compare an Except with a success value (Except has no BEq instance).
def eqOk {α : Type} [BEq α] (e : Except String α) (v : α) : Bool :=
  match e with
  | .ok x => x == v
  | .error _ => false

-- An Except String that failed with a message containing the substring.
def isErrContaining {α : Type} (e : Except String α) (sub : String) : Bool :=
  match e with
  | .error m => m.contains sub
  | .ok _ => false

-- ============================================================================
-- 1. The document scanner
-- ============================================================================

def parseShapeOk : Bool :=
  match parseTVIR exampleDump with
  | .error _ => false
  | .ok doc =>
      doc.actors.length == 3
      && (doc.actors.lookup "R1").map (fun g => g.length) == some 3
      && (doc.actors.lookup "R2").map (fun g => g.length) == some 8
      && (doc.actors.lookup "R3").map (fun g => g.length) == some 7
      && doc.templateSpecs == ["FinishingProperty", "RecoveryProperty"]
      && doc.labels == [("R2", "fail_send", 7), ("R2", "start_send", 10)]
      && doc.warnings.isEmpty

#assert! parseShapeOk

def parseUserSpecsOk : Bool :=
  exampleDoc.userSpecs == [
    { logic := "ltl", name := "FinishDuplicate"
    , formula := "F (R1.ACTOR_END && R2.ACTOR_END && R3.ACTOR_END)" },
    { logic := "ltl", name := "RecoveryProperty_R2_fail_send_0"
    , formula := "[] (R2.fail_send -> <> R2.start_send)" } ]

#assert! parseUserSpecsOk

-- The line prefix key IS the storage key; the node keeps its own id/scheduler.
def parseNodeOk : Bool :=
  ((exampleDoc.actors.lookup "R1").bind fun g => g.lookup 1)
    == some { id := 1, lineNumber := 4, scheduler := none
            , instr := IRInstruction.push 2 "Q[R3][R1]" "Y" }

#assert! parseNodeOk

-- The branch of R3: two queue conditions, no otherwise-branch.
def parseBranchOk : Bool :=
  match (exampleDoc.actors.lookup "R3").bind fun g => g.lookup 13 with
  | some { instr := IRInstruction.branch cs o, .. } =>
      cs.length == 2
      && cs.head? == some { queueName := "Q[R3][R2]", msg := "X", bodyStart := 18 }
      && (cs.drop 1).head? == some { queueName := "Q[R3][R1]", msg := "Y", bodyStart := 21 }
      && o == none
  | _ => false

#assert! parseBranchOk

-- CRLF line endings are normalized away: same document.
def parseCrlfOk : Bool :=
  match parseTVIR exampleDump, parseTVIR crlfDump with
  | .ok a, .ok b => a == b
  | _, _ => false

#assert! parseCrlfOk

-- A broken line fails with its line number.
def parseErrorOk : Bool :=
  match parseTVIR "Actor: A\n  0: IRBogus(0,1,(-1,-1))\n" with
  | .error m => m.contains "tvir:2:" && m.contains "IRBogus"
  | .ok _ => false

#assert! parseErrorOk

-- ============================================================================
-- 2. The runtime State
-- ============================================================================

def exampleState : State :=
  match buildInitialState exampleDoc with
  | .ok s => s
  | .error _ => { queues := [], guardVars := [], actorThreads := [], actorGraphs := [] }

-- Entry PCs are the minimal instruction keys; queues pre-created empty.
def stateThreadsOk : Bool :=
  exampleState.actorThreads == [("R1", ([1], none)), ("R2", ([4], none)), ("R3", ([13], none))]

#assert! stateThreadsOk

def stateQueuesOk : Bool :=
  let qs := exampleState.queues.map (fun (q, _) => q)
  exampleState.queues.length == 3
  && exampleState.queues.all (fun (_, msgs) => msgs.isEmpty)
  && ["Q[R3][R1]", "Q[R2][R1]", "Q[R3][R2]"].all (fun q => qs.contains q)

#assert! stateQueuesOk

-- A label pointing at an absent instruction is an error, not a crash.
def stateBadLabelOk : Bool :=
  match buildInitialState { exampleDoc with labels := [("R2", "ghost", 99)] } with
  | .error m => m.contains "ghost" && m.contains "99"
  | .ok _ => false

#assert! stateBadLabelOk

-- ============================================================================
-- 3. Bounded channels (the queueCap field of State)
-- ============================================================================

-- A sender that queues two messages into one channel, with no consumer.
def chanDump : String := String.intercalate "\n" [
  "Actor: A",
  "  0: IRQueuePush(0,1,(-1,-1),1,Q[B][A],M)",
  "  1: IRQueuePush(1,2,(-1,-1),2,Q[B][A],M)",
  "  2: IREnd(2,3,(-1,-1))",
  ""]

def chanState : State :=
  match buildInitialState (match parseTVIR chanDump with
    | .ok d => d
    | .error _ => { actors := [], templateSpecs := [], userSpecs := [], labels := [], warnings := [] }) with
  | .ok s => s
  | .error _ => { queues := [], guardVars := [], actorThreads := [], actorGraphs := [] }

-- The default capacity is MAX_QUEUE_SIZE, so both sends go through.
def chanDefaultOk : Bool :=
  chanState.queueCap == MAX_QUEUE_SIZE
  && (match step chanState with
      | [(t1, s1)] =>
          t1.actionName == "push M to Q[B][A]"
          && (match step s1 with
              | [(t2, s2)] =>
                  t2.actionName == "push M to Q[B][A]" && getQueueLen s2 "Q[B][A]" == 2
              | _ => false)
      | _ => false)

#assert! chanDefaultOk

-- With capacity 1 the second send blocks while the channel is full and
-- becomes enabled again once the message is taken.
def chanBoundedOk : Bool :=
  let s := { chanState with queueCap := 1 }
  match step s with
  | [(t1, s1)] =>
      t1.actionName == "push M to Q[B][A]"
      && (step s1).isEmpty                       -- full: the send blocks
      && (match step (pop s1 "Q[B][A]") with     -- drained: enabled again
          | [(t2, _)] => t2.actionName == "push M to Q[B][A]"
          | _ => false)
  | _ => false

#assert! chanBoundedOk
