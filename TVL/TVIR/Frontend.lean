import TVL.Sema

-- ============================================================================
-- The .tvir text format frontend
--
-- TVL (the modeling language) dumps its IR into a textual .tvir file:
-- actor blocks with instruction lines, then optional "Template specs:",
-- "User specs:" and "Labels:" sections, always in this order. This module
-- parses that text into a TVIRDocument -- a plain syntax-level picture of
-- the dump. Turning the document into a runtime State and the specs into
-- formulas lives in TVL/TVIR/Spec.lean.
--
-- TVL identifiers match [a-zA-Z_][a-zA-Z0-9_]* -- no dots, colons or
-- spaces -- so "Actor:" headers, "<id>: <instr>" lines,
-- "<actor>.<label>: <id>" and "<logic> <name>: <formula>" split
-- unambiguously on the first ':' of the line.
-- ============================================================================

-- One user-defined spec line: "<logic> <name>: <formula>".
-- The formula stays raw text here -- it is parsed into an LTL term later
-- (and only for ltl; ctl specs are recognized but not checked yet).
structure TVIRUserSpec where
  logic   : String -- "ltl" | "ctl"
  name    : String
  formula : String
  deriving BEq, Repr

-- The whole parsed dump, in file order.
structure TVIRDocument where
  actors        : List (String × ActorGraph)   -- actor name -> its instructions
  templateSpecs : List String                  -- template property names
  userSpecs     : List TVIRUserSpec
  labels        : List (String × String × Int) -- (actor, label, instruction key)
  warnings      : List String                  -- non-fatal notes (key != id)
  deriving BEq

-- ============================================================================
-- Small string helpers
--
-- Hand-rolled rather than String.trimRight / String.dropRight / posOf:
-- in this toolchain their replacements return String.Slice, and the
-- two-space indent of .tvir lines is significant, so the exact shape of
-- the stripping matters anyway.
-- ============================================================================

def isTVIRIdent (s : String) : Bool :=
  let okStart (c : Char) : Bool := c.isAlpha || c == '_'
  let okChar (c : Char) : Bool := c.isAlphanum || c == '_'
  match s.toList with
  | c :: rest => okStart c && rest.all okChar
  | [] => false

-- Strip trailing whitespace only (the leading indent must survive).
def trimTrailing (s : String) : String :=
  String.ofList ((s.toList.reverse.dropWhile Char.isWhitespace).reverse)

-- Strip whitespace on both sides.
def stripWs (s : String) : String :=
  String.ofList (((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse)

-- Split at the first occurrence of c: (before, after), c itself dropped.
def splitOnFirstChar (c : Char) (s : String) : Option (String × String) :=
  let rec go (pre : List Char) (rest : List Char) : Option (String × String) :=
    match rest with
    | d :: tail => if d == c then some (String.ofList pre.reverse, String.ofList tail) else go (d :: pre) tail
    | [] => none
  go [] s.toList

-- Drop the last character (an empty string stays empty).
def dropLastChar (s : String) : String :=
  String.ofList s.toList.dropLast

-- Drop the first n characters (an empty string stays empty).
def dropChars (n : Nat) (s : String) : String :=
  String.ofList (s.toList.drop n)

-- ============================================================================
-- Instruction argument parsing
-- ============================================================================

-- Split an argument list at the commas of depth 0: commas nested inside
-- parentheses (List(...), QueueCondition(...), scheduler tuples) do not
-- cut. Queue names like Q[R3][R1] contain no commas or parens, so the
-- paren depth is all that matters.
def splitTopLevelCommas (s : String) : Except String (List String) :=
  let rec go (rest : List Char) (depth : Nat) (cur : List Char) (acc : List String)
      : Except String (List String) :=
    match rest with
    | [] =>
        if cur.isEmpty && !acc.isEmpty then Except.error "trailing comma"
        else Except.ok (acc.reverse ++ (if cur.isEmpty then [] else [stripWs (String.ofList cur.reverse)]))
    | '(' :: rest' => go rest' (depth + 1) ('(' :: cur) acc
    | ')' :: rest' =>
        if depth == 0 then Except.error "unbalanced ')'"
        else go rest' (depth - 1) (')' :: cur) acc
    | ',' :: rest' =>
        if depth == 0 then
          if cur.isEmpty then Except.error "empty argument"
          else go rest' depth [] (stripWs (String.ofList cur.reverse) :: acc)
        else go rest' depth (',' :: cur) acc
    | c :: rest' => go rest' depth (c :: cur) acc
  go s.toList 0 [] []

def parseIntArg (s : String) : Except String Int :=
  match (stripWs s).toInt? with
  | some i => Except.ok i
  | none => Except.error s!"expected an integer, got '{s}'"

def parseIdentArg (s : String) : Except String String :=
  let t := stripWs s
  if isTVIRIdent t then Except.ok t
  else Except.error s!"expected an identifier, got '{s}'"

-- Queue names have the shape Q[Receiver][Sender]: not plain identifiers,
-- but they cannot contain parens or commas (the split has already used
-- both), so only emptiness needs checking here.
def parseQueueNameArg (s : String) : Except String String :=
  let t := stripWs s
  if t.isEmpty then Except.error s!"expected a queue name, got '{s}'"
  else Except.ok t

-- The scheduler context argument "(start, index)": the pair (-1,-1)
-- encodes "not inside a parallel block" (none).
def parseSchedulerArg (s : String) : Except String (Option (Int × Int)) := do
  let t := stripWs s
  unless t.startsWith "(" && t.endsWith ")" do
    throw s!"expected a scheduler context '(a,b)', got '{s}'"
  let args ← splitTopLevelCommas (dropLastChar (dropChars 1 t))
  match args with
  | [a, b] =>
    let a' ← parseIntArg a
    let b' ← parseIntArg b
    if a' == -1 && b' == -1 then pure none else pure (some (a', b'))
  | _ => throw s!"expected a scheduler context '(a,b)', got '{s}'"

-- An optional-integer argument: "None", "Some(n)" or "Some n".
def parseOptIntArg (s : String) : Except String (Option Int) := do
  let t := stripWs s
  if t == "None" then return none
  else if t.startsWith "Some(" && t.endsWith ")" then return some (← parseIntArg (dropLastChar (dropChars 5 t)))
  else if t.startsWith "Some " then return some (← parseIntArg (dropChars 5 t))
  else throw s!"expected 'None' or 'Some(n)', got '{s}'"

-- "QueueCondition(q,msg,bodyStart)"
def parseQueueCondArg (s : String) : Except String QueueCondition := do
  let t := stripWs s
  unless t.startsWith "QueueCondition(" && t.endsWith ")" do
    throw s!"expected 'QueueCondition(q,msg,bodyStart)', got '{s}'"
  let args ← splitTopLevelCommas (dropLastChar (dropChars 15 t))
  match args with
  | [q, m, b] => do
    let q' ← parseQueueNameArg q
    let m' ← parseIdentArg m
    let b' ← parseIntArg b
    return { queueName := q', msg := m', bodyStart := b' }
  | _ => throw s!"expected 'QueueCondition(q,msg,bodyStart)', got '{s}'"

-- "List(a, b, ...)" of integers (choice targets, parallel branch starts).
def parseIntListArg (s : String) : Except String (List Int) := do
  let t := stripWs s
  unless t.startsWith "List(" && t.endsWith ")" do
    throw s!"expected 'List(...)', got '{s}'"
  let args ← splitTopLevelCommas (dropLastChar (dropChars 5 t))
  args.mapM parseIntArg

-- "List(QueueCondition(...), ...)" -- the case list of IRBranch.
def parseQueueCondListArg (s : String) : Except String (List QueueCondition) := do
  let t := stripWs s
  unless t.startsWith "List(" && t.endsWith ")" do
    throw s!"expected 'List(...)', got '{s}'"
  let args ← splitTopLevelCommas (dropLastChar (dropChars 5 t))
  args.mapM parseQueueCondArg

private def arityError (opcode : String) (args : List String) : Except String IRInstruction :=
  Except.error s!"'{opcode}' expects a different number of arguments, got {args.length}: [{String.intercalate ", " args}]"

-- The opcode-specific arguments, i.e. everything after the common
-- (id, lineNumber, scheduler) prefix.
def parseInstructionArgs (opcode : String) (args : List String) : Except String IRInstruction :=
  match opcode with
  | "IRQueuePush" =>
      match args with
      | [n, q, m] => return IRInstruction.push (← parseIntArg n) (← parseQueueNameArg q) (← parseIdentArg m)
      | _ => arityError opcode args
  | "IRQueuePop" =>
      match args with
      | [n, q, m] => return IRInstruction.pop (← parseIntArg n) (← parseQueueNameArg q) (← parseIdentArg m)
      | _ => arityError opcode args
  | "IRBranch" =>
      match args with
      | [cs, o] => return IRInstruction.branch (← parseQueueCondListArg cs) (← parseOptIntArg o)
      | _ => arityError opcode args
  | "IRJump" =>
      match args with
      | [t] => return IRInstruction.jump (← parseIntArg t)
      | _ => arityError opcode args
  | "IRJumpGuard" =>
      match args with
      | [n, g, t, i] => return IRInstruction.jumpGuard (← parseIntArg n) (← parseIdentArg g) (← parseIntArg t) (← parseIntArg i)
      | _ => arityError opcode args
  | "IRChoice" =>
      match args with
      | [bs] => return IRInstruction.choice (← parseIntListArg bs)
      | _ => arityError opcode args
  | "IRParallelExec" =>
      match args with
      | [bs, e] => return IRInstruction.parallelExec (← parseIntListArg bs) (← parseIntArg e)
      | _ => arityError opcode args
  | "IRParallelEnd" =>
      match args with
      | [j] => return IRInstruction.parallelEnd (← parseIntArg j)
      | _ => arityError opcode args
  | "IRSkip" =>
      match args with
      | [n] => return IRInstruction.skipInstr (← parseIntArg n)
      | _ => arityError opcode args
  | "IREnd" =>
      match args with
      | [] => return IRInstruction.endInstr
      | _ => arityError opcode args
  | _ =>
      Except.error s!"unknown IR opcode '{opcode}' (known: IRQueuePush, IRQueuePop, IRBranch, IRJump, IRJumpGuard, IRChoice, IRParallelExec, IRParallelEnd, IRSkip, IREnd) -- the .tvir dump may come from a newer TVL compiler than curtis supports"

-- One instruction line "<key>: <opcode>(<args>)".
-- The node is stored under the line prefix key: the runtime resolves PCs
-- by the ActorGraph key (Sema.getInstruction does graph.lookup pc), and
-- control transfers in the dump refer to these keys.
def parseInstruction (s : String) : Except String (Int × IRNode) := do
  let (keyStr, rest) ← match splitOnFirstChar ':' s with
    | some p => pure p
    | none => throw s!"expected '<id>: <instruction>', got '{s}'"
  let key ← match (stripWs keyStr).toInt? with
    | some k => pure k
    | none => throw s!"expected an integer instruction id, got '{keyStr}'"
  let t := stripWs rest
  let (opcode, args) ← match splitOnFirstChar '(' t with
    | none => throw s!"expected '<opcode>(<args>)', got '{t}'"
    | some (op, after) => do
        unless after.endsWith ")" do throw s!"missing ')' in '{t}'"
        pure (stripWs op, ← splitTopLevelCommas (dropLastChar after))
  match args with
  | idArg :: lineArg :: schedArg :: extra => do
      let id ← parseIntArg idArg
      let ln ← parseIntArg lineArg
      let sched ← parseSchedulerArg schedArg
      return (key, { id := id, lineNumber := ln, scheduler := sched
                    , instr := ← parseInstructionArgs opcode extra })
  | _ => throw s!"'{opcode}': expected at least (id, lineNumber, scheduler) arguments"

-- ============================================================================
-- The document scanner
-- ============================================================================

-- Sections appear in a fixed order; the phase tracks how far we got.
inductive TVIRPhase where
  | actors | template | user | labels
  deriving BEq

def TVIRPhase.rank : TVIRPhase → Nat
  | .actors => 0 | .template => 1 | .user => 2 | .labels => 3

def parseTVIR (input : String) : Except String TVIRDocument := do
  -- Normalize: strip a possible BOM and CRLF / lone CR line endings.
  let s0 := if input.startsWith "﻿" then dropChars 1 input else input
  let lines := ((s0.replace "\r\n" "\n").replace "\r" "\n").splitOn "\n" |>.map trimTrailing

  let mut phase := TVIRPhase.actors
  -- Actors in REVERSE file order, each with a REVERSED instruction list;
  -- the HEAD entry is the actor block currently being read.
  let mut actors : List (String × ActorGraph) := []
  let mut templateSpecs : List String := []
  let mut userSpecs : List TVIRUserSpec := []
  let mut labels : List (String × String × Int) := []
  let mut warnings : List String := []

  for (line, no) in lines.zipIdx 1 do
    let atLine (msg : String) : String := s!"tvir:{no}: {msg}"
    if line.isEmpty then continue

    -- Section headers: each at most once, always in this order.
    let headerPhase : Option TVIRPhase :=
      if line == "Template specs:" then some .template
      else if line == "User specs:" then some .user
      else if line == "Labels:" then some .labels
      else none
    if let some p := headerPhase then
      if p.rank <= phase.rank then
        throw (atLine s!"section '{line}' is repeated or out of order")
      phase := p
      continue

    -- Actor header
    if phase == .actors && line.startsWith "Actor: " then
      let nm := stripWs (dropChars 7 line)
      unless isTVIRIdent nm do
        throw (atLine s!"invalid actor name '{nm}'")
      if actors.any (fun (a, _) => a == nm) then
        throw (atLine s!"duplicate actor '{nm}'")
      actors := (nm, []) :: actors
      continue

    -- Section content: exactly two spaces of indent.
    unless line.startsWith "  " do
      throw (atLine "unrecognized line (expected a header or a two-space-indented entry)")
    let body := stripWs (dropChars 2 line)

    match phase with
    | .actors =>
        match actors with
        | [] => throw (atLine "instruction outside an actor block")
        | (nm, g) :: rest =>
            let (key, node) ← parseInstruction body |>.mapError atLine
            if g.any (fun (k, _) => k == key) then
              throw (atLine s!"duplicate instruction id {key}")
            if key != node.id then
              warnings := atLine s!"instruction key {key} != id {node.id} (control flow follows the key)" :: warnings
            actors := (nm, (key, node) :: g) :: rest
    | .template =>
        unless isTVIRIdent body do
          throw (atLine s!"invalid template spec name '{body}'")
        templateSpecs := body :: templateSpecs
    | .user =>
        let (left, formula) ← match splitOnFirstChar ':' body with
          | some p => pure p
          | none => throw (atLine s!"expected '<logic> <name>: <formula>', got '{body}'")
        match (stripWs left).splitOn " " with
        | [logic, name] =>
            unless logic == "ltl" || logic == "ctl" do
              throw (atLine s!"unknown spec logic '{logic}' (expected ltl or ctl)")
            unless isTVIRIdent name do
              throw (atLine s!"invalid spec name '{name}'")
            let formula := stripWs formula
            if formula.isEmpty then
              throw (atLine s!"spec '{name}' has an empty formula")
            userSpecs := { logic := logic, name := name, formula := formula } :: userSpecs
        | parts =>
            throw (atLine s!"expected '<logic> <name>: <formula>', got '{body}' ({parts.length} words before ':')")
    | .labels =>
        let (left, idStr) ← match splitOnFirstChar ':' body with
          | some p => pure p
          | none => throw (atLine s!"expected '<actor>.<label>: <id>', got '{body}'")
        match (stripWs left).splitOn "." with
        | [actor, label] =>
            unless isTVIRIdent actor && isTVIRIdent label do
              throw (atLine s!"invalid label '{left}' (expected <actor>.<label>)")
            let id ← match (stripWs idStr).toInt? with
              | some i => pure i
              | none => throw (atLine s!"expected an integer instruction id, got '{idStr}'")
            -- A repeated (actor, label) with the same target is a benign
            -- duplicate; with a different target it is ambiguous.
            if labels.any (fun (a, l, i) => a == actor && l == label && i != id) then
              throw (atLine s!"label '{actor}.{label}' is defined with different ids")
            unless labels.any (fun (a, l, i) => a == actor && l == label && i == id) do
              labels := (actor, label, id) :: labels
        | _ => throw (atLine s!"invalid label '{left}' (expected <actor>.<label>)")

  return { actors := actors.reverse.map (fun (nm, g) => (nm, g.reverse))
          , templateSpecs := templateSpecs.reverse
          , userSpecs := userSpecs.reverse
          , labels := labels.reverse
          , warnings := warnings.reverse }
