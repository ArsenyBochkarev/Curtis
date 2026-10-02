import Test.Harness
import TVL.Trace.Replay
import TVL.Trace.Json

-- ============================================================================
-- Trace validation (TVL/Trace/Replay.lean): candidate-set replay of a
-- canonical tvl-trace/1 counterexample against a concrete model.
-- ============================================================================

namespace TraceTests

def instr (id : Int) (i : IRInstruction) : Int × IRNode :=
  (id, { id, lineNumber := 1, scheduler := none, instr := i })

def tstep (idx : Nat) (actor : String) (node : Option Int) : TraceStep :=
  { index := idx, actor, node, next := none, action := "" }

def tstepN (idx : Nat) (actor : String) (node : Option Int) (next : Option Int) : TraceStep :=
  { index := idx, actor, node, next, action := "" }

def isFeasible : ValidateResult → Bool
  | .feasible => true
  | _ => false

/-- A: one bounded loop iteration (guard 0: pass -> 1, exit -> 2). -/
def guardModel : State :=
  mkInitialState
    [ ("A", [instr 0 (.jumpGuard 2 "g" 1 1), instr 1 .endInstr, instr 2 .endInstr]) ]
    []

/-- A: a bounded loop (guard 0: pass -> 1 body, exit -> 3; body skip returns
to the guard). The guard allows a single iteration. -/
def guardLoopModel : State :=
  mkInitialState
    [ ("A", [instr 0 (.jumpGuard 3 "g" 1 1), instr 1 (.skipInstr 0), instr 3 .endInstr]) ]
    []

-- The `next` field disambiguates guard pass vs exit on the same node.
#eval show IO Unit from
  unless isFeasible (validateTrace guardModel
      { isLasso := false, steps := [tstepN 1 "A" (some 0) (some 1)], loopStart := none }) do
    throw (IO.userError "test failed: guard pass (next=body) must be feasible")

#eval show IO Unit from
  unless isFeasible (validateTrace guardLoopModel
      { isLasso := false,
        steps := [tstepN 1 "A" (some 0) (some 1), tstepN 2 "A" (some 1) (some 0),
                  tstepN 3 "A" (some 0) (some 3)],
        loopStart := none })do
    throw (IO.userError "test failed: pass, body, exit must be feasible")

-- A fresh guard always passes (the counter starts above zero): a trace that
-- claims an immediate exit is spurious, and `next` pins that down.
#eval show IO Unit from
  match validateTrace guardModel
      { isLasso := false, steps := [tstepN 1 "A" (some 0) (some 2)], loopStart := none } with
  | .spurious 1 "A" (some 0) => pure ()
  | r => throw (IO.userError s!"test failed: a fresh guard must only pass, got {r.toLine}")

-- After the single allowed iteration the guard can only exit: a trace that
-- claims a second pass is spurious, and `next` pins that down.
#eval show IO Unit from
  match validateTrace guardLoopModel
      { isLasso := false,
        steps := [tstepN 1 "A" (some 0) (some 1), tstepN 2 "A" (some 1) (some 0),
                  tstepN 3 "A" (some 0) (some 1)],
        loopStart := none } with
  | .spurious 3 "A" (some 0) => pure ()
  | r => throw (IO.userError s!"test failed: a second guard pass must be spurious, got {r.toLine}")

-- Without `next` the same trace is accepted: the exit transition also
-- executes the guard node (documented over-approximation).
#eval show IO Unit from
  unless isFeasible (validateTrace guardLoopModel
      { isLasso := false,
        steps := [tstep 1 "A" (some 0), tstep 2 "A" (some 1), tstep 3 "A" (some 0)],
        loopStart := none })do
    throw (IO.userError "test failed: without next the guard step must stay permissive")

/-- A: push X to B; B: pop X. Both end. -/
def pushPopModel : State :=
  mkInitialState
    [ ("A", [instr 0 (.push 2 "Q[B][A]" "X"), instr 2 .endInstr]),
      ("B", [instr 0 (.pop 2 "Q[B][A]" "X"), instr 2 .endInstr]) ]
    ["Q[B][A]"]

/-- A: jump over a push (jumps are silent in both backends). -/
def jumpModel : State :=
  mkInitialState
    [ ("A", [instr 0 (.jump 1), instr 1 (.push 2 "Q[A][A]" "X"), instr 2 .endInstr]) ]
    ["Q[A][A]"]

/-- A: choice between an endless skip loop and termination. -/
def choiceLoopModel : State :=
  mkInitialState
    [ ("A", [instr 0 (.choice [1, 3]), instr 1 (.skipInstr 0), instr 3 .endInstr]) ]
    []

/-- A: a self-skip that never terminates. -/
def foreverModel : State :=
  mkInitialState
    [ ("A", [instr 0 (.skipInstr 0)]) ]
    []

/-- A: choice where both arms fall into IREnd (no cycle at all). -/
def noCycleModel : State :=
  mkInitialState
    [ ("A", [instr 0 (.choice [1, 2]), instr 1 (.skipInstr 3), instr 2 (.skipInstr 3), instr 3 .endInstr]) ]
    []

-- ------------------------------------------------------------------ replay --

#eval show IO Unit from
  unless isFeasible (validateTrace pushPopModel
      { isLasso := false, steps := [tstep 1 "A" (some 0), tstep 2 "B" (some 0)], loopStart := none }) do
    throw (IO.userError "test failed: push-then-pop trace must be feasible")

#eval show IO Unit from
  match validateTrace pushPopModel
      { isLasso := false, steps := [tstep 1 "B" (some 0), tstep 2 "A" (some 0)], loopStart := none } with
  | .spurious 1 "B" (some 0) => pure ()
  | r => throw (IO.userError s!"test failed: pop-before-push must be spurious at step 1, got {r.toLine}")

-- Jumps are silent: a trace step behind a jump matches through the closure.
#eval show IO Unit from
  unless isFeasible (validateTrace jumpModel
      { isLasso := false, steps := [tstep 1 "A" (some 1)], loopStart := none }) do
    throw (IO.userError "test failed: a step behind a silent jump must be feasible")

-- node = none is a wildcard: it matches any transition of the actor.
#eval show IO Unit from
  unless isFeasible (validateTrace pushPopModel
      { isLasso := false, steps := [tstep 1 "A" none, tstep 2 "B" (some 0)], loopStart := none }) do
    throw (IO.userError "test failed: an unlabeled plumbing step must be feasible")

-- ------------------------------------------------------------------ lassos --

-- Non-empty loop that closes: choice -> skip -> back to the choice.
#eval show IO Unit from
  unless isFeasible (validateTrace choiceLoopModel
      { isLasso := true, steps := [tstep 1 "A" (some 0), tstep 2 "A" (some 1)], loopStart := some 2 }) do
    throw (IO.userError "test failed: the closing skip loop must be feasible")

-- Empty loop, terminating model: the final state stutters at IREnd.
#eval show IO Unit from
  unless isFeasible (validateTrace pushPopModel
      { isLasso := true, steps := [tstep 1 "A" (some 0), tstep 2 "B" (some 0)], loopStart := some 3 }) do
    throw (IO.userError "test failed: an empty loop over a terminal state must be feasible")

-- Empty loop, but the actor can always move: stuttering is not realizable.
#eval show IO Unit from
  match validateTrace foreverModel
      { isLasso := true, steps := [tstep 1 "A" (some 0)], loopStart := some 2 } with
  | .spuriousLoop 2 => pure ()
  | r => throw (IO.userError s!"test failed: endless skip must give spuriousLoop, got {r.toLine}")

-- Non-empty loop that does not close: both choice arms end at IREnd.
#eval show IO Unit from
  match validateTrace noCycleModel
      { isLasso := true, steps := [tstep 1 "A" (some 0), tstep 2 "A" (some 1)], loopStart := some 2 } with
  | .spuriousLoop 2 => pure ()
  | r => throw (IO.userError s!"test failed: acyclic loop body must give spuriousLoop, got {r.toLine}")

-- ------------------------------------------------------------ trace parsing --

#eval show IO Unit from do
  let text := "{\"format\":\"tvl-trace/1\",\"kind\":\"lasso\",\"channel_size\":20,\"steps\":[" ++
    "{\"index\":1,\"actor\":\"R1\",\"node\":12,\"action\":\"push X to Q[R2][R1]\"}," ++
    "{\"index\":2,\"actor\":\"R2\",\"node\":null,\"action\":\"L_END_ACTOR_R2\"}]," ++
    "\"loop_start_index\":2}"
  match parseTrace text with
  | .error m => throw (IO.userError s!"test failed: parseTrace rejected a valid trace: {m}")
  | .ok tf =>
      unless tf.isLasso && tf.loopStart == some 2 && tf.steps.length == 2 do
        throw (IO.userError "test failed: parseTrace mis-parsed the header")
      match tf.steps with
      | [s1, s2] =>
          unless s1.actor == "R1" && s1.node == some 12 && s2.actor == "R2" && s2.node.isNone do
            throw (IO.userError "test failed: parseTrace mis-parsed the steps")
      | _ => throw (IO.userError "test failed: parseTrace mis-parsed the step count")

#eval show IO Unit from
  match parseTrace "{\"format\":\"other/1\",\"steps\":[]}" with
  | .error m => unless m.contains "format" do
      throw (IO.userError s!"test failed: wrong-format rejection message: {m}")
  | .ok _ => throw (IO.userError "test failed: parseTrace accepted a wrong format tag")

-- The "System" pseudo-actor (TLC's loop-closure marker) is skipped.
#eval show IO Unit from
  unless isFeasible (validateTrace pushPopModel
      { isLasso := false, steps := [tstep 1 "A" (some 0), tstep 2 "System" (some 0), tstep 3 "B" (some 0)],
        loopStart := none })do
    throw (IO.userError "test failed: a System bookkeeping step must be skipped")

-- IREnd appears as a real step in TLC traces (`L_<id>: finished := true`)
-- but is terminal in Curtis: the step consumes no transition, it only prunes
-- the candidates down to those parked at the node.
#eval show IO Unit from
  unless isFeasible (validateTrace pushPopModel
      { isLasso := false,
        steps := [tstep 1 "A" (some 0), tstep 2 "A" (some 2), tstep 3 "B" (some 0), tstep 4 "B" (some 2)],
        loopStart := none })do
    throw (IO.userError "test failed: IREnd steps must be consumed without a transition")

-- ----------------------------------------------- step is stepTagged projected --

def bfsStates (s : State) (depth : Nat) : List State :=
  match depth with
  | 0 => [s]
  | d + 1 =>
      let next := (step s).map (fun (_, t) => t)
      let uniq : List State :=
        next.foldl (fun acc t => if acc.contains t then acc else acc ++ [t]) []
      uniq.flatMap (fun t => bfsStates t d)

#eval show IO Unit from
  let states := bfsStates pushPopModel 4
  let bad := states.filter fun s =>
    (step s) != (stepTagged s).map fun t => (t.trans, t.next)
  unless bad.isEmpty do
    throw (IO.userError s!"test failed: step disagrees with stepTagged on {bad.length} states")

-- --------------------------------------------------------------- CLI smoke --

def validateSmokeModel : String :=
  "Actor: A\n" ++
  "  0: IRQueuePush(0, 1, (-1,-1), 2, Q[B][A], X)\n" ++
  "  2: IREnd(2, 1, (-1,-1))\n" ++
  "\n" ++
  "Actor: B\n" ++
  "  0: IRQueuePop(0, 1, (-1,-1), 2, Q[B][A], X)\n" ++
  "  2: IREnd(2, 1, (-1,-1))\n"

def feasibleTraceJson : String :=
  "{\"format\":\"tvl-trace/1\",\"kind\":\"safety\",\"channel_size\":20,\"steps\":[" ++
  "{\"index\":1,\"actor\":\"A\",\"node\":0,\"action\":\"push\"}," ++
  "{\"index\":2,\"actor\":\"B\",\"node\":0,\"action\":\"pop\"}]}"

def spuriousTraceJson : String :=
  "{\"format\":\"tvl-trace/1\",\"kind\":\"safety\",\"channel_size\":20,\"steps\":[" ++
  "{\"index\":1,\"actor\":\"B\",\"node\":0,\"action\":\"pop\"}," ++
  "{\"index\":2,\"actor\":\"A\",\"node\":0,\"action\":\"push\"}]}"

#eval show IO Unit from do
  IO.FS.writeFile "/tmp/curtis_test_validate.tvir" validateSmokeModel
  IO.FS.writeFile "/tmp/curtis_test_trace_ok.json" feasibleTraceJson
  IO.FS.writeFile "/tmp/curtis_test_trace_bad.json" spuriousTraceJson
  let ok ← IO.Process.output
    { cmd := ".lake/build/bin/curtis",
      args := #["validate", "/tmp/curtis_test_validate.tvir", "/tmp/curtis_test_trace_ok.json"] }
  unless ok.exitCode == 0 && ok.stdout.contains "validate: feasible" do
    throw (IO.userError s!"test failed: smoke feasible: exit {ok.exitCode}\n{ok.stdout}\n{ok.stderr}")
  let bad ← IO.Process.output
    { cmd := ".lake/build/bin/curtis",
      args := #["validate", "/tmp/curtis_test_validate.tvir", "/tmp/curtis_test_trace_bad.json"] }
  unless bad.exitCode == 1 && bad.stdout.contains "validate: spurious step=1 actor=B node=0" do
    throw (IO.userError s!"test failed: smoke spurious: exit {bad.exitCode}\n{bad.stdout}\n{bad.stderr}")

-- ------------------------------------------------------------------ branch-hoist projection --

/-- A: receive-alts at 0 (case q/m -> body 2, otherwise 3); B pushes m. -/
def altsModel : State :=
  mkInitialState
    [ ("A", [instr 0 (.branch [{ queueName := "q", msg := "m", bodyStart := 2 }] (some 3)),
             instr 2 (.skipInstr 4),
             instr 3 (.skipInstr 4),
             instr 4 .endInstr]),
      ("B", [instr 0 (.push 2 "q" "m"), instr 2 .endInstr]) ]
    ["q"]

/-- The projection branch-hoist would produce for altsModel: the inserted pop
id 7 maps back to the head 0. -/
def proj7 : Projection := { mappings := [("A", 7, 0)] }

-- A counterexample through the case body: with the projection the choice step
-- is consumed (actor parked at the branch) and the pop step is remapped onto
-- the concrete IRBranch transition, which fires because m is at the head.
#eval show IO Unit from
  unless isFeasible (validateTrace altsModel
      { isLasso := false,
        steps := [tstepN 1 "B" (some 0) (some 2), tstepN 2 "A" (some 0) (some 7),
                  tstepN 3 "A" (some 7) (some 2), tstepN 4 "A" (some 2) (some 4)],
        loopStart := none } proj7)do
    throw (IO.userError "test failed: a case-body trace must be feasible under the projection")

-- The same trace without the projection: the choice step's next=7 refers to
-- a node the concrete model does not have, so it dies right there.
#eval show IO Unit from
  match validateTrace altsModel
      { isLasso := false,
        steps := [tstepN 1 "B" (some 0) (some 2), tstepN 2 "A" (some 0) (some 7),
                  tstepN 3 "A" (some 7) (some 2), tstepN 4 "A" (some 2) (some 4)],
        loopStart := none } with
  | .spurious 2 "A" (some 0) => pure ()
  | r => throw (IO.userError s!"test failed: without the projection the trace must die at the choice step, got {r.toLine}")

-- Early entry with an empty stutter loop: the abstract counterexample has the
-- actor enter the branch and block forever at the hoisted pop. The prefix is
-- reproducible (the actor parks at the branch), but the concrete model is not
-- terminal there (the otherwise arm is available) - a MEANINGFUL spuriousLoop,
-- not an immediate death on an unknown node.
#eval show IO Unit from
  match validateTrace altsModel
      { isLasso := true, steps := [tstepN 1 "A" (some 0) (some 7)], loopStart := some 2 } proj7 with
  | .spuriousLoop 2 => pure ()
  | r => throw (IO.userError s!"test failed: early entry must give spuriousLoop, got {r.toLine}")

-- The otherwise arm is a real concrete transition; it replays normally even
-- with a projection loaded.
#eval show IO Unit from
  unless isFeasible (validateTrace altsModel
      { isLasso := false,
        steps := [tstepN 1 "A" (some 0) (some 3), tstepN 2 "A" (some 3) (some 4)],
        loopStart := none } proj7)do
    throw (IO.userError "test failed: the otherwise arm must replay normally")

-- parseProjection keeps only branch-hoist decisions.
#eval show IO Unit from do
  let text := "{\"format\":\"tvl-abstraction-report/1\",\"applied\":[" ++
    "{\"actor\":\"A\",\"node\":0,\"kind\":\"branch-hoist\",\"inserted\":[7,11]}," ++
    "{\"actor\":\"R2\",\"node\":5,\"kind\":\"loop-unroll\",\"inserted\":[]}]," ++
    "\"refused\":[]}"
  match parseProjection text with
  | .error m => throw (IO.userError s!"test failed: parseProjection rejected a valid report: {m}")
  | .ok p =>
      unless p.headOf "A" 7 == some 0 && p.headOf "A" 11 == some 0
          && p.headOf "R2" 7 == none && p.isBranchHead "A" 0 && !p.isBranchHead "R2" 5 do
        throw (IO.userError "test failed: parseProjection mis-parsed the mappings")

#eval show IO Unit from
  match parseProjection "{\"format\":\"other/1\",\"applied\":[]}" with
  | .error m => unless m.contains "format" do
      throw (IO.userError s!"test failed: wrong-format rejection message: {m}")
  | .ok _ => throw (IO.userError "test failed: parseProjection accepted a wrong format tag")

-- validateProjection rejects a head that is not an IRBranch of the model.
#eval show IO Unit from
  match validateProjection altsModel { mappings := [("B", 0, 2)] } with
  | .error m => unless m.contains "not an IRBranch" do
      throw (IO.userError s!"test failed: guardrail message: {m}")
  | .ok _ => throw (IO.userError "test failed: validateProjection accepted a non-branch head")

-- --------------------------------------------------- CLI smoke: --abstraction --

def altsSmokeModel : String :=
  "Actor: A\n" ++
  "  0: IRBranch(0, 1, (-1,-1), List(QueueCondition(q,m,2)), Some(3))\n" ++
  "  2: IRSkip(2, 3, (-1,-1), 4)\n" ++
  "  3: IRSkip(3, 4, (-1,-1), 4)\n" ++
  "  4: IREnd(4, 5, (-1,-1))\n" ++
  "\n" ++
  "Actor: B\n" ++
  "  0: IRQueuePush(0, 1, (-1,-1), 2, q, m)\n" ++
  "  2: IREnd(2, 2, (-1,-1))\n"

def altsSmokeTrace : String :=
  "{\"format\":\"tvl-trace/1\",\"kind\":\"safety\",\"channel_size\":20,\"steps\":[" ++
  "{\"index\":1,\"actor\":\"B\",\"node\":0,\"next\":2,\"action\":\"push\"}," ++
  "{\"index\":2,\"actor\":\"A\",\"node\":0,\"next\":7,\"action\":\"choice\"}," ++
  "{\"index\":3,\"actor\":\"A\",\"node\":7,\"next\":2,\"action\":\"pop\"}," ++
  "{\"index\":4,\"actor\":\"A\",\"node\":2,\"next\":4,\"action\":\"skip\"}]}"

def altsSmokeAbs : String :=
  "{\"format\":\"tvl-abstraction-report/1\"," ++
  "\"applied\":[{\"actor\":\"A\",\"node\":0,\"kind\":\"branch-hoist\",\"inserted\":[7]}]," ++
  "\"refused\":[]}"

#eval show IO Unit from do
  IO.FS.writeFile "/tmp/curtis_test_alts.tvir" altsSmokeModel
  IO.FS.writeFile "/tmp/curtis_test_alts_trace.json" altsSmokeTrace
  IO.FS.writeFile "/tmp/curtis_test_alts_abs.json" altsSmokeAbs
  let ok ← IO.Process.output
    { cmd := ".lake/build/bin/curtis",
      args := #["validate", "--abstraction", "/tmp/curtis_test_alts_abs.json",
                "/tmp/curtis_test_alts.tvir", "/tmp/curtis_test_alts_trace.json"] }
  unless ok.exitCode == 0 && ok.stdout.contains "validate: feasible" do
    throw (IO.userError s!"test failed: smoke projection feasible: exit {ok.exitCode}\n{ok.stdout}\n{ok.stderr}")
  let noProj ← IO.Process.output
    { cmd := ".lake/build/bin/curtis",
      args := #["validate", "/tmp/curtis_test_alts.tvir", "/tmp/curtis_test_alts_trace.json"] }
  unless noProj.exitCode == 1 && noProj.stdout.contains "validate: spurious step=2 actor=A node=0" do
    throw (IO.userError s!"test failed: smoke no-projection spurious: exit {noProj.exitCode}\n{noProj.stdout}\n{noProj.stderr}")

end TraceTests
