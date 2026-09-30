-- Global constant bounding the channel capacity (Rule 1): the default
-- bound; a run may override it through the queueCap field of State
-- (the --channel-size option of curtis).
def MAX_QUEUE_SIZE : Nat := 10

structure Transition where
  processId  : String
  actionName : String
  deriving BEq, Hashable

-- Helper structure for the IRBranch instruction
structure QueueCondition where
  queueName : String
  msg       : String
  bodyStart : Int
  deriving BEq, Hashable

-- Inductive type describing the operands of each instruction.
-- The IR has no nested expressions, the graph is flat, so control transfers
-- go by Int identifiers.
inductive IRInstruction where
  | push (next : Int) (qName : String) (msgName : String)
  | pop (next : Int) (qName : String) (msgName : String)
  | branch (cases : List QueueCondition) (otherwiseOpt : Option Int)
  | jump (target : Int)
  | jumpGuard (next : Int) (guardVar : String) (target : Int) (iterations : Int)
  | choice (branches : List Int)
  | parallelExec (branchStarts : List Int) (breakExit : Int)
  | parallelEnd (joinPc : Int)
  | skipInstr (next : Int)
  | endInstr
  deriving BEq, Hashable

-- Scheduler context: (start of the parallel block, branch index)
abbrev SchedulerContext := Int × Int

-- A full graph node (control-flow graph node): metadata plus the instruction
structure IRNode where
  id         : Int
  lineNumber : Int
  scheduler  : Option SchedulerContext -- none when not inside a parallel block
  instr      : IRInstruction
  deriving BEq, Hashable

-- Execution graph of a single actor
abbrev ActorGraph := List (Int × IRNode) -- could later become Std.HashMap Int IRNode

-- Whole-system state for the interpreter
structure State where
  queues       : List (String × List String)             -- queue name (format "Q[A][B]", A = receiver, B = sender) -> message tokens
  queueCap     : Nat := MAX_QUEUE_SIZE                   -- channel capacity of this run (Rule 1): a send into a full queue blocks
  guardVars    : List (String × Int)                     -- counters for countable loops
  actorThreads : List (String × (List Int × Option Int)) -- key: actor name, value: list of PCs (one per thread);
                                                         -- optionally the breakExit PC of the current parallel block
  actorGraphs  : List (String × ActorGraph)              -- code storage (CFG per actor)
  deriving BEq, Hashable

def getQueueLen (s : State) (qName : String) : Nat :=
  match s.queues.lookup qName with
  | some q => q.length
  | none   => 0

def push (s : State) (qName : String) (msg : String) : State :=
  let newQ := s.queues.map (fun (k, v) => if k == qName then (k, v.concat msg) else (k, v))
  { s with queues := newQ }

def pop (s : State) (qName : String) : State :=
  let newQ := s.queues.map (fun (k, v) => if k == qName then (k, v.drop 1) else (k, v))
  { s with queues := newQ }

def getInstruction (s : State) (actor : String) (pc : Int) : Option IRNode :=
  match s.actorGraphs.lookup actor with
  | some graph => graph.lookup pc
  | none => none

def getPCs (s : State) (actorName : String) : Option (List Int) :=
  match s.actorThreads.lookup actorName with
  | some (pcs, _) => pcs
  | none => none

def updateGuardVar (s : State) (gName : String) (val : Int) : State :=
  let newGuards := match s.guardVars.lookup gName with
    | some _ => s.guardVars.map fun (k, v) => if k == gName then (k, val) else (k, v)
    | none   => (gName, val) :: s.guardVars
  { s with guardVars := newGuards }

-- Update the PC of a specific thread inside an actor.
-- Implements the "kill switch": when the new PC equals breakExit, all
-- threads of the actor collapse into one.
def updateThreadPc (s : State) (actor : String) (threadIdx : Nat) (newPc : Int) : State :=
  let newThreads := s.actorThreads.map fun (a, (pcs, breakOpt)) =>
    if a == actor then
      -- Emergency exit from a parallel block (Rule 5: break)
      if breakOpt == some newPc then
        (a, ([newPc], none)) -- kill the other threads, reset the context
      else
        (a, (pcs.set threadIdx newPc, breakOpt))
    else (a, (pcs, breakOpt))
  { s with actorThreads := newThreads }

-- Which queues an IR instruction touches:
-- push and pop work with a single queue, branch may read several
-- (receive alts); the remaining instructions are purely local.
def instrQueues (instr : IRInstruction) : List String :=
  match instr with
  | .push _ q _     => [q]
  | .pop _ q _      => [q]
  | .branch cases _ => cases.map fun c => c.queueName
  | _ => []

-- One successor of a state together with the id of the instruction that
-- executed (the pre-state pc). This is exactly the identity of a step in the
-- canonical tvl-trace/1 counterexample format, so trace validation matches on
-- (processId, node). `silent` marks transitions that never surface as trace
-- steps in either target backend: both fold gotos, so an IRJump execution is
-- invisible to the trace and validation passes through it freely.
structure TaggedTransition where
  trans  : Transition
  node   : Int
  next   : State
  silent : Bool := false

-- All successors of the current state, each tagged with the executed pc.
-- `step` below is the untagged projection, so the two always agree.
def stepTagged (s : State) : List TaggedTransition :=
  s.actorThreads.flatMap fun (actor, (pcs, _)) =>

    -- SCENARIO A: barrier synchronization at IRParallelEnd.
    -- Fires when there is more than one thread and ALL of them sit on a
    -- parallelEnd instruction.
    let isReadyToJoin := (pcs.length > 1) && pcs.all fun pc =>
      match getInstruction s actor pc with
      | some { instr := IRInstruction.parallelEnd _, .. } => true
      | _ => false

    if isReadyToJoin then
      -- Wait until every branch has finished its work, take the joinPc from
      -- any branch and collapse them all.
      match getInstruction s actor pcs.head! with
      | some { instr := IRInstruction.parallelEnd joinPc, .. } =>
          let newThreads := s.actorThreads.map fun (a, t) =>
            if a == actor then (a, ([joinPc], none)) else (a, t)
          let nextState := { s with actorThreads := newThreads }
          let trans := { processId := actor, actionName := "parallel join" }
          [{ trans, node := pcs.head!, next := nextState }]
      | _ => []

    else
      -- SCENARIO B: independent interleaving
      pcs.zipIdx.flatMap fun (currentPc, threadIdx) =>
        match getInstruction s actor currentPc with
        | none => []
        | some node =>
          -- Every arm below builds its tagged successor(s) through this
          let tagged (trans : Transition) (nextState : State) (silent : Bool := false) : List TaggedTransition :=
            [{ trans, node := currentPc, next := nextState, silent }]
          match node.instr with

          -- 1. Send: append the message to the queue;
          --    blocks until there is room if the queue is full.
          | .push next qName msgName =>
              if getQueueLen s qName < s.queueCap then
                let nextState := push (updateThreadPc s actor threadIdx next) qName msgName
                let trans := { processId := actor, actionName := s!"push {msgName} to {qName}" }
                tagged trans nextState
              else []

          -- 2. Single receive. Blocks until the head of the queue matches.
          | .pop next qName msgName =>
              match s.queues.lookup qName with
              | some (head :: _) =>
                  if head == msgName then
                    let nextState := updateThreadPc (pop s qName) actor threadIdx next
                    let trans := { processId := actor, actionName := s!"pop {msgName}" }
                    tagged trans nextState
                  else []
              | _ => []

          -- 3. Branching on messages (receive alts).
          | .branch cases otherwiseOpt =>
              let readyCases := cases.filter fun c =>
                match s.queues.lookup c.queueName with
                | some (head :: _) => head == c.msg
                | _ => false

              if readyCases.isEmpty then
                -- No matching message: take the otherwise branch.
                match otherwiseOpt with
                | some otherPc =>
                    let nextState := updateThreadPc s actor threadIdx otherPc
                    let trans := { processId := actor, actionName := "branch otherwise" }
                    tagged trans nextState
                | none => []
              else
                -- Run the branch whose message has arrived.
                readyCases.flatMap fun c =>
                  let nextState := updateThreadPc (pop s c.queueName) actor threadIdx c.bodyStart
                  let trans := { processId := actor, actionName := s!"branch receive {c.msg}" }
                  tagged trans nextState

          -- 4. Unconditional jump.
          | .jump target =>
              let nextState := updateThreadPc s actor threadIdx target
              let trans := { processId := actor, actionName := s!"jump to {target}" }
              tagged trans nextState (silent := true)

          -- 5. Conditional jump for bounded loops.
          | .jumpGuard next guardVar target iterations =>
              let currentVal := match s.guardVars.lookup guardVar with
                | some v => v
                | none   => iterations -- initialize the counter

              if currentVal > 0 then
                let nextState := updateGuardVar (updateThreadPc s actor threadIdx target) guardVar (currentVal - 1)
                let trans := { processId := actor, actionName := s!"loop guard pass ({currentVal})" }
                tagged trans nextState
              else
                let nextState := updateThreadPc s actor threadIdx next
                let trans := { processId := actor, actionName := "loop guard exit" }
                tagged trans nextState

          -- 6. Nondeterministic choice of one of the branches.
          | .choice branches =>
              branches.flatMap fun branchPc =>
                let nextState := updateThreadPc s actor threadIdx branchPc
                let trans := { processId := actor, actionName := s!"choice -> {branchPc}" }
                tagged trans nextState

          -- 7. Start of a parallel block.
          | .parallelExec branchStarts breakExit =>
              let newThreads := s.actorThreads.map fun (a, (p, b)) =>
                if a == actor then (a, (branchStarts, some breakExit)) else (a, (p, b))
              let nextState := { s with actorThreads := newThreads }
              let trans := { processId := actor, actionName := "parallel fork" }
              tagged trans nextState

          -- 8. End of a parallel branch; blocks until the barrier.
          | .parallelEnd _ => []

          -- 9. A no-op (skip).
          | .skipInstr next =>
              let nextState := updateThreadPc s actor threadIdx next
              let trans := { processId := actor, actionName := "skip" }
              tagged trans nextState

          -- 10. The actor has finished its work.
          | .endInstr => []

-- All successors of the current state (the untagged projection of stepTagged;
-- kept as the sole interpreter entry point for the engines).
def step (s : State) : List (Transition × State) :=
  (stepTagged s).map fun t => (t.trans, t.next)
