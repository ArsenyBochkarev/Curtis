import TVLChecker.TVL.Sema

-- Inductive type for atomic predicates
inductive AtomicProposition where
  -- 1. The queue is empty
  | queueEmpty (qName : String)
  -- 2. The actor is at a specific instruction
  | actorAt (actor : String) (pc : Int)
  -- 3. A loop counter (guardVar) equals a specific value
  | guardEq (varName : String) (val : Int)

  -- 4. The queue length is strictly greater than the given number
  -- (useful for finding potential channel overflows)
  | queueSizeGt (qName : String) (size : Nat)

  -- 5. The actor has finished successfully
  -- (all of its live threads reached an endInstr instruction)
  | actorFinished (actor : String)

  deriving BEq, Hashable, Repr

-- Evaluate a predicate on a concrete state
def evalAP (s : State) (ap : AtomicProposition) : Bool :=
  match ap with
  | .queueEmpty qName =>
    match s.queues.lookup qName with
    | some q => q.isEmpty
    | none => true -- a queue missing from the map has never been written to (it is empty)

  | .actorAt actor pc =>
    match s.actorThreads.lookup actor with
    | some (pcs, _) => pcs.contains pc
    | none => false

  | .guardEq varName val =>
    match s.guardVars.lookup varName with
    | some v => v == val
    | none => false

  | .queueSizeGt qName size =>
    getQueueLen s qName > size

  | .actorFinished actor =>
    match getPCs s actor with
    | some pcs =>
        pcs.all fun (pc) =>
          match getInstruction s actor pc with
          | some node =>
              match node.instr with
              | .endInstr => true
              | _ => false
          | none => false
    | none => false
