import TVL.Sema
import TVL.Trace.Json

/-!
# Trace validation (`curtis validate`)

Validates a canonical `tvl-trace/1` counterexample (produced by TVL's
verifier.py from SPIN or TLC) against the CONCRETE model: can the concrete
model actually execute this sequence of (actor, executed node) steps?

## Method

Candidate-set replay without backtracking: keep the set of all states the
concrete model can be in after having reproduced the trace so far (dedup via
the structural Hashable State). Per step, expand every candidate with
`stepTagged` and keep the successors whose `(processId, node)` match the step.
The set empties exactly at the first step the concrete model cannot reproduce.

Jumps are silent in both backends (gotos fold into the next statement), so
candidates are closed under IRJump transitions before matching — a trace step
matches across a chain of jumps. Conversely, an explicit jump step (if a
backend ever emits one) still matches the jump transition itself. Steps with
`node = none` are plumbing (INIT, L_END_*, flag bookkeeping) with no pc event:
they match any transition of that actor. Steps of the pseudo-actor "System"
(TLC's loop-closure marker) are skipped.

## Lassos

For `kind = "lasso"` the prefix must be feasible, plus the loop must be
realizable in the concrete model: an EMPTY loop (loop_start_index beyond the
last step) means the counterexample stutters in the final state forever —
realizable iff some final candidate is terminal (no successor at all); a
NON-EMPTY loop must replay and close: from the loop's final candidates some
plain-transition path must lead back to a loop-start candidate.

Note on liveness: feasibility here means "this infinite behavior exists in the
concrete model", not "a fair one" — Curtis does not model fairness, and the
property itself is not re-checked (that would be full verification).
-/

/-- One `tvl-trace/1` step. `index` is the 1-based position in the trace.
`next` (when present) is the actor's pc AFTER the step — the trace writer
derives it from the backend state, and it disambiguates same-node transitions
(an IRJumpGuard pass and exit both execute the guard node). -/
structure TraceStep where
  index  : Nat
  actor  : String
  node   : Option Int
  next   : Option Int := none
  action : String

/-- A parsed `tvl-trace/1` document. `loopStart` is the 1-based index of the
first loop step; `some (steps.length + 1)` encodes an empty (stutter) loop. -/
structure TraceFile where
  isLasso   : Bool
  steps     : List TraceStep
  loopStart : Option Nat

inductive ValidateResult where
  | feasible
  | spurious (step : Nat) (actor : String) (node : Option Int)
  | spuriousLoop (fromStep : Nat)

namespace ValidateResult

def verdict : ValidateResult → String
  | .feasible => "feasible"
  | .spurious _ _ _ => "spurious"
  | .spuriousLoop _ => "spurious"

/-- The machine-readable line consumed by the CEGAR driver. -/
def toLine : ValidateResult → String
  | .feasible => "validate: feasible"
  | .spurious k a n =>
      let nodeTxt := match n with | some i => toString i | none => "?"
      s!"validate: spurious step={k} actor={a} node={nodeTxt}"
  | .spuriousLoop k => s!"validate: spurious step={k} actor=? node=?"

end ValidateResult

private def reqString (j : Json) (name : String) : Except String String :=
  match j.field? name >>= Json.asString? with
  | some s => .ok s
  | none => .error s!"missing or non-string field \"{name}\""

private def parseTraceStep (idx : Nat) (j : Json) : Except String TraceStep :=
  do
    let actor ← reqString j "actor"
    let node := j.field? "node" >>= Json.asInt?
    let next := j.field? "next" >>= Json.asInt?
    let action := (j.field? "action" >>= Json.asString?).getD ""
    return { index := idx, actor, node, next, action }

/-- Parse a `tvl-trace/1` document (unknown fields are ignored). -/
def parseTrace (text : String) : Except String TraceFile := do
  let j ← JsonParser.parse text
  match j.field? "format" >>= Json.asString? with
  | some "tvl-trace/1" => pure ()
  | other => throw s!"expected format \"tvl-trace/1\", got {match other with | some f => f | none => "none"}"
  let kind := (j.field? "kind" >>= Json.asString?).getD "safety"
  let steps ←
    match j.field? "steps" with
    | none => throw "missing field \"steps\""
    | some sj =>
        let items := sj.items
        items.zipIdx.foldlM (fun (acc : List TraceStep) (item, i) =>
          return acc ++ [← parseTraceStep (i + 1) item]) []
  let loopStart := j.field? "loop_start_index" >>= Json.asInt? |>.map (·.toNat)
  return { isLasso := kind == "lasso", steps, loopStart }

/-! ## Candidate-set replay -/

/-- Transitive closure through silent (IRJump) transitions. -/
private partial def silentClosure (visited : List State) : List State → List State
  | [] => visited
  | c :: rest =>
      if visited.contains c then silentClosure visited rest
      else
        let jumps := (stepTagged c).filter (·.silent) |>.map (·.next)
        silentClosure (c :: visited) (jumps ++ rest)

private def dedupStates (states : List State) : List State :=
  states.foldl (fun acc s => if acc.contains s then acc else s :: acc) []

private def matchesStep (t : TaggedTransition) (st : TraceStep) : Bool :=
  t.trans.processId == st.actor &&
  match st.node with
  | some n => t.node == n
  | none => true

private def actorAtPc (s : State) (actor : String) (pc : Int) : Bool :=
  match s.actorThreads.lookup actor with
  | some (pcs, _) => pcs.contains pc
  | none => false

/-- The candidate states after one reproduced step (empty = infeasible).
When the step carries `next`, the actor's pc after the step (closed under
silent jumps) must be exactly that node. -/
private def advance (cands : List State) (st : TraceStep) : List State :=
  let expanded := silentClosure [] cands
  let nexts := expanded.flatMap fun c =>
    ((stepTagged c).filter (matchesStep · st)).map (·.next)
      |>.filter fun s =>
        match st.next with
        | none => true
        | some n => (silentClosure [] [s]).any fun s' => actorAtPc s' st.actor n
  dedupStates nexts

/-- Does any thread of the actor sit on an IREnd node in this state? -/
private def actorAtEnd (s : State) (actor : String) : Bool :=
  match s.actorThreads.lookup actor with
  | some (pcs, _) => pcs.any fun pc =>
      match getInstruction s actor pc with
      | some { instr := .endInstr, .. } => true
      | _ => false
  | none => false

/-- IREnd steps need special treatment: the backends compile IREnd into real
statements (`L_<id>: <actor>_finished := true`, plus the L_END_ACTOR_* tail),
so traces contain them as steps, while in Curtis IREnd is terminal (no
transition). A step referencing an IREnd node is reproducible iff a thread of
the actor is parked at that node (then it consumes no transition, pruning the
candidates to those parked there); a plumbing step with no node of an actor
parked at IREnd is likewise consumed. Returns none otherwise. -/
private def consumeEndStep (cands : List State) (st : TraceStep) : Option (List State) :=
  match st.node with
  | none =>
      if cands.any (fun s => actorAtEnd s st.actor) then some cands else none
  | some n =>
      let parkedAtEnd (s : State) : Bool :=
        match s.actorThreads.lookup st.actor with
        | some (pcs, _) =>
            pcs.contains n &&
            match getInstruction s st.actor n with
            | some { instr := .endInstr, .. } => true
            | _ => false
        | none => false
      let kept := cands.filter parkedAtEnd
      if kept.isEmpty then none else some kept

/-- Replay a step sequence; `.ok` carries the final candidates, `.error` the
first unreproducible step. -/
def replayPrefix (cands : List State) : List TraceStep → Except ValidateResult (List State)
  | [] => .ok cands
  | st :: rest =>
      -- "System" is TLC's loop-closure bookkeeping, not a real actor step
      if st.actor == "System" then replayPrefix cands rest
      else
        match consumeEndStep cands st with
        | some cands' => replayPrefix cands' rest
        | none =>
            let next := advance cands st
            if next.isEmpty then .error <| .spurious st.index st.actor st.node
            else replayPrefix next rest

/-- Can any plain-transition path from `frontier` reach a state in `targets`? -/
private partial def canReach (targets : List State) (visited : List State) : List State → Bool
  | [] => false
  | c :: rest =>
      if visited.contains c then canReach targets visited rest
      else if targets.any (· == c) then true
      else canReach targets (c :: visited) ((stepTagged c).map (·.next) ++ rest)

/-- Validate a parsed trace against the initial state of the concrete model. -/
def validateTrace (start : State) (tf : TraceFile) : ValidateResult :=
  match tf.loopStart with
  | none =>
      match replayPrefix [start] tf.steps with
      | .ok _ => .feasible
      | .error r => r
  | some ls =>
      let n := ls - 1
      match replayPrefix [start] (tf.steps.take n) with
      | .error r => r
      | .ok afterPrefix =>
          match tf.steps.drop n with
          | [] =>
              -- Empty loop: the abstract counterexample stutters in the final
              -- state forever; realizable iff some candidate is terminal.
              if afterPrefix.any fun c => (stepTagged c).isEmpty then .feasible
              else .spuriousLoop ls
          | loopSteps =>
              match replayPrefix afterPrefix loopSteps with
              | .error r => r
              | .ok afterLoop =>
                  if canReach afterPrefix [] afterLoop then .feasible
                  else .spuriousLoop ls
