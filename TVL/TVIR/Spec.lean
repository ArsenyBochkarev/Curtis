import TVL.TVIR.Frontend
import TVL.AtomicProposition
import TVL.Logics.LTL
import TVL.Logics.CTL

-- ============================================================================
-- From a parsed .tvir dump (TVIRDocument) to checkable things:
--   * buildInitialState -- the runtime State (queues, threads, graphs);
--   * parseLtlFormula / parseCtlFormula -- the surface syntax of spec
--     formulas into LTL / CTL terms;
--   * expandTemplates / checkedSpecs -- the TVL template and label-based
--     properties into concrete LTL specs, plus the user specs of both
--     logics.
-- ============================================================================

-- Entry PC of an actor = the minimal instruction key of its block (the
-- first line: dump instructions are sorted by id, and the runtime resolves
-- PCs by these keys).
def actorEntryPc (graph : ActorGraph) : Option Int :=
  match graph with
  | [] => none
  | (k, _) :: rest => some (rest.foldl (fun acc (k', _) => if k' < acc then k' else acc) k)

-- The runtime State of the dump: every queue touched by any instruction is
-- created empty (Sema.push maps only over existing keys -- an unlisted
-- queue would silently swallow pushes), every actor starts single-threaded
-- at its entry PC.
def buildInitialState (doc : TVIRDocument) : Except String State := do
  let mut threads : List (String × (List Int × Option Int)) := []
  let mut graphs : List (String × ActorGraph) := []
  for (nm, g) in doc.actors do
    match actorEntryPc g with
    | none => throw s!"actor '{nm}' has no instructions"
    | some entry =>
      threads := (nm, ([entry], none)) :: threads
      graphs := (nm, g) :: graphs
  for (a, l, id) in doc.labels do
    match graphs.lookup a with
    | none => throw s!"label '{a}.{l}' refers to unknown actor '{a}'"
    | some g =>
        unless g.any (fun (k, _) => k == id) do
          throw s!"label '{a}.{l}' points to instruction {id}, absent from actor '{a}'"
  let queues := (graphs.flatMap fun (_, g) => g.flatMap fun (_, n) => instrQueues n.instr) |>.eraseDups
  return { queues := queues.map fun q => (q, [])
          , guardVars := []
          , actorThreads := threads.reverse
          , actorGraphs := graphs.reverse }

-- ============================================================================
-- The LTL surface syntax of .tvir specs
--
-- Grammar (one function per precedence LEVEL, loosest binding last):
--   level 4  implies:  or ('->' implies)?           right-associative
--   level 3  or:       and ('||' or)?
--   level 2  and:      until ('&&' and)?
--   level 1  until:    unary ('U' until)?
--   level 0  unary:    '!' unary | '[]' unary | '<>' unary | 'X' unary | primary
--             primary: '(' implies ')' | atom | 'true' | 'false'
--             atom:    IDENT '.' IDENT   e.g. R2.fail_send, R1.ACTOR_END
--
-- Encodings (LTL has no or/implies constructors):
--   a -> b  =  !(a && !b);   a || b  =  !(!a && !b)
--   '[]' / 'G' = always, '<>' / 'F' = eventually, 'X' = next, 'U' = until_
-- (TVL dumps spell the operators both ways: "F (R1.ACTOR_END && ...)"
-- and "[] (R2.fail_send -> <> R2.start_send)".)
-- A bare 'X'/'F'/'G' is an operator: atoms are always IDENT '.' IDENT,
-- and a '.' never follows the operator letter, so the readings never
-- collide even for an actor actually named X, F or G.
-- ============================================================================

inductive LtlTok where
  | glob | eventual | not | and | or | imp
  | lparen | rparen | dot
  | ident : String → LtlTok
  deriving BEq, Repr, Inhabited
-- The binary 'U' is recognized in the parser as an ident not followed by
-- '.' (a '.' would start an atom of an actor actually named U).

private instance : Inhabited LTL := ⟨LTL.top⟩
private instance : Inhabited CTL := ⟨CTL.top⟩

private def ltlIdentChar (c : Char) : Bool := c.isAlphanum || c == '_'

private def flushIdent (acc : List LtlTok) (idb : List Char) : List LtlTok :=
  if idb.isEmpty then acc else LtlTok.ident (String.ofList idb.reverse) :: acc

private def ltlTokenize (s : String) : Except String (List LtlTok) :=
  let rec go (rest : List Char) (acc : List LtlTok) (idb : List Char)
      : Except String (List LtlTok) :=
    match rest with
    | [] => Except.ok (flushIdent acc idb).reverse
    | '[' :: ']' :: rest' => go rest' (LtlTok.glob :: flushIdent acc idb) []
    | '<' :: '>' :: rest' => go rest' (LtlTok.eventual :: flushIdent acc idb) []
    | '-' :: '>' :: rest' => go rest' (LtlTok.imp :: flushIdent acc idb) []
    | '&' :: '&' :: rest' => go rest' (LtlTok.and :: flushIdent acc idb) []
    | '|' :: '|' :: rest' => go rest' (LtlTok.or :: flushIdent acc idb) []
    | '!' :: rest' => go rest' (LtlTok.not :: flushIdent acc idb) []
    | '(' :: rest' => go rest' (LtlTok.lparen :: flushIdent acc idb) []
    | ')' :: rest' => go rest' (LtlTok.rparen :: flushIdent acc idb) []
    | '.' :: rest' => go rest' (LtlTok.dot :: flushIdent acc idb) []
    | c :: rest' =>
        if c.isWhitespace then go rest' (flushIdent acc idb) []
        else if ltlIdentChar c then go rest' acc (c :: idb)
        else Except.error s!"unexpected character '{c}' in formula"
  go s.toList [] []

-- The atom Actor.Label of the surface syntax: ACTOR_END is the pseudo-label
-- for "the actor has finished" (it never appears in the Labels section);
-- anything else is resolved to the actor's instruction key via the label
-- table. Shared by the LTL and CTL parsers.
private def resolveAtom (doc : TVIRDocument) (actor label : String)
    : Except String AtomicProposition := do
  unless doc.actors.any fun (a, _) => a == actor do
    throw s!"unknown actor '{actor}' in atom '{actor}.{label}'"
  if label == "ACTOR_END" then
    return AtomicProposition.actorFinished actor
  match doc.labels.find? fun (a, l, _) => a == actor && l == label with
  | some (_, _, pc) => return AtomicProposition.actorAt actor pc
  | none =>
    let known := (doc.labels.filter fun (a, _, _) => a == actor).map fun (_, l, _) => s!"{actor}.{l}"
    throw s!"unknown label '{actor}.{label}' (labels of '{actor}': {String.intercalate ", " known})"

-- Precedence-climbing descent over the token list (partial, like the
-- engine's DFS functions: the recursion mixes level descents with
-- parenthesized restarts at the top level, and the token list is clearly
-- finite -- a bad formula either errors out or exhausts the tokens).
-- Levels: 0 = implies (top), 1 = or, 2 = and, 3 = until, 4 = unary/primary.
private partial def parseLevel (doc : TVIRDocument) (level : Nat) (toks : List LtlTok)
    : Except String (LTL × List LtlTok) :=
  match level with
  | 0 => do -- implies (top):  a -> b  =  !(a && !b)
      let (f, rest) ← parseLevel doc 1 toks
      match rest with
      | .imp :: rest' =>
          let (g, rest'') ← parseLevel doc 0 rest'
          return (LTL.not (LTL.and f (LTL.not g)), rest'')
      | _ => return (f, rest)
  | 1 => do -- or:  a || b  =  !(!a && !b)
      let (f, rest) ← parseLevel doc 2 toks
      match rest with
      | .or :: rest' =>
          let (g, rest'') ← parseLevel doc 1 rest'
          return (LTL.not (LTL.and (LTL.not f) (LTL.not g)), rest'')
      | _ => return (f, rest)
  | 2 => do -- and
      let (f, rest) ← parseLevel doc 3 toks
      match rest with
      | .and :: rest' =>
          let (g, rest'') ← parseLevel doc 2 rest'
          return (LTL.and f g, rest'')
      | _ => return (f, rest)
  | 3 => do -- until (right-associative)
      let (f, rest) ← parseLevel doc 4 toks
      match rest with
      | .ident "U" :: .dot :: _ => return (f, rest) -- atom of an actor named U
      | .ident "U" :: rest' =>
          let (g, rest'') ← parseLevel doc 3 rest'
          return (LTL.until_ f g, rest'')
      | _ => return (f, rest)
  | _ => -- unary / primary
      match toks with
      | .not :: rest => parseLevel doc 4 rest |>.map fun (f, r) => (LTL.not f, r)
      | .glob :: rest => parseLevel doc 4 rest |>.map fun (f, r) => (G f, r)
      | .eventual :: rest => parseLevel doc 4 rest |>.map fun (f, r) => (F f, r)
      -- The atom pattern comes first: a letter operator (X, F, G)
      -- directly followed by '.' is an actor name, not an operator.
      | .ident s :: .dot :: .ident l :: rest =>
          match resolveAtom doc s l with
          | .ok p => .ok (LTL.ap p, rest)
          | .error e => .error e
      | .ident "X" :: rest => parseLevel doc 4 rest |>.map fun (f, r) => (LTL.next f, r)
      | .ident "F" :: rest => parseLevel doc 4 rest |>.map fun (f, r) => (F f, r)
      | .ident "G" :: rest => parseLevel doc 4 rest |>.map fun (f, r) => (G f, r)
      | .lparen :: rest =>
          match parseLevel doc 0 rest with
          | .ok (f, .rparen :: rest') => .ok (f, rest')
          | .ok _ => .error "expected ')' after the parenthesized formula"
          | .error e => .error e
      | .ident "true" :: rest => .ok (LTL.top, rest)
      | .ident "false" :: rest => .ok (LTL.not LTL.top, rest)
      | [] => .error "unexpected end of formula"
      | t :: _ => .error s!"unexpected token {reprStr t}"

def parseLtlFormula (doc : TVIRDocument) (s : String) : Except String LTL := do
  if (stripWs s).isEmpty then throw "empty formula"
  let toks ← ltlTokenize s
  let (f, rest) ← parseLevel doc 0 toks
  unless rest.isEmpty do
    throw s!"unexpected trailing tokens ({rest.length} left, starting with {reprStr rest.head!})"
  return f

-- ============================================================================
-- The CTL surface syntax of .tvir specs
--
-- The same token stream as the LTL syntax (the tokenizer is shared); the
-- path quantifiers are the letter prefixes EX / EF / EG / AX / AF / AG and
-- the parenthesized binary forms  E (phi U psi)  /  A (phi U psi).
--
-- The core CTL type has only ex / eu / eg -- everything else is encoded:
--   EF phi = E[true U phi]        AX phi = !EX(!phi)
--   AF phi = !EG(!phi)            AG phi = !E[true U !phi]
--   A[p U q] = !( E[!q U (!p && !q)] || EG !q )
-- A quantifier letter directly followed by '.' is an actor name, not an
-- operator (atoms are always IDENT '.' IDENT), so actors actually named
-- E, A, EF, ... still parse.
--
-- Levels: 0 = implies (top), 1 = or, 2 = and, 3 = unary/quantifier/primary
-- (CTL has no bare binary U: it only appears inside E (...) / A (...)).
-- ============================================================================

-- a || b and a -> b in the CTL core syntax (no or/implies constructors).
def ctlOr (a b : CTL) : CTL := CTL.not (CTL.and (CTL.not a) (CTL.not b))
def ctlImpl (a b : CTL) : CTL := CTL.not (CTL.and a (CTL.not b))

private partial def parseCtlLevel (doc : TVIRDocument) (level : Nat) (toks : List LtlTok)
    : Except String (CTL × List LtlTok) :=
  match level with
  | 0 => do -- implies (top), right-associative:  a -> b  =  !(a && !b)
      let (f, rest) ← parseCtlLevel doc 1 toks
      match rest with
      | .imp :: rest' =>
          let (g, rest'') ← parseCtlLevel doc 0 rest'
          return (ctlImpl f g, rest'')
      | _ => return (f, rest)
  | 1 => do -- or:  a || b  =  !(!a && !b)
      let (f, rest) ← parseCtlLevel doc 2 toks
      match rest with
      | .or :: rest' =>
          let (g, rest'') ← parseCtlLevel doc 1 rest'
          return (ctlOr f g, rest'')
      | _ => return (f, rest)
  | 2 => do -- and
      let (f, rest) ← parseCtlLevel doc 3 toks
      match rest with
      | .and :: rest' =>
          let (g, rest'') ← parseCtlLevel doc 2 rest'
          return (CTL.and f g, rest'')
      | _ => return (f, rest)
  | _ => -- unary / path quantifiers / primary
      match toks with
      | .not :: rest => parseCtlLevel doc 3 rest |>.map fun (f, r) => (CTL.not f, r)
      -- The atom pattern comes first: a quantifier directly followed by '.'
      -- is an actor name (an actor actually named EF or E), not an operator.
      | .ident s :: .dot :: .ident l :: rest =>
          match resolveAtom doc s l with
          | .ok p => .ok (CTL.ap p, rest)
          | .error e => .error e
      -- The unary path quantifier prefixes, tight-binding like X/F/G in LTL.
      | .ident "EX" :: rest => parseCtlLevel doc 3 rest |>.map fun (f, r) => (CTL.ex f, r)
      | .ident "EF" :: rest => parseCtlLevel doc 3 rest |>.map fun (f, r) => (CTL.eu CTL.top f, r)
      | .ident "EG" :: rest => parseCtlLevel doc 3 rest |>.map fun (f, r) => (CTL.eg f, r)
      | .ident "AX" :: rest => parseCtlLevel doc 3 rest |>.map fun (f, r) => (CTL.not (CTL.ex (CTL.not f)), r)
      | .ident "AF" :: rest => parseCtlLevel doc 3 rest |>.map fun (f, r) => (CTL.not (CTL.eg (CTL.not f)), r)
      | .ident "AG" :: rest => parseCtlLevel doc 3 rest |>.map fun (f, r) => (CTL.not (CTL.eu CTL.top (CTL.not f)), r)
      -- E (phi U psi): some path keeps phi until psi.
      | .ident "E" :: .lparen :: rest => do
          let (f, rest') ← parseCtlLevel doc 0 rest
          match rest' with
          | .ident "U" :: rest'' =>
              let (g, rest3) ← parseCtlLevel doc 0 rest''
              match rest3 with
              | .rparen :: rest4 => return (CTL.eu f g, rest4)
              | _ => throw "expected ')' closing 'E (phi U psi)'"
          | _ => throw "expected 'U' inside 'E (phi U psi)'"
      -- A (phi U psi): every path keeps phi until psi.
      | .ident "A" :: .lparen :: rest => do
          let (f, rest') ← parseCtlLevel doc 0 rest
          match rest' with
          | .ident "U" :: rest'' =>
              let (g, rest3) ← parseCtlLevel doc 0 rest''
              match rest3 with
              | .rparen :: rest4 =>
                  let witness := CTL.eu (CTL.not g) (CTL.and (CTL.not f) (CTL.not g))
                  return (CTL.not (ctlOr witness (CTL.eg (CTL.not g))), rest4)
              | _ => throw "expected ')' closing 'A (phi U psi)'"
          | _ => throw "expected 'U' inside 'A (phi U psi)'"
      | .lparen :: rest =>
          match parseCtlLevel doc 0 rest with
          | .ok (f, .rparen :: rest') => .ok (f, rest')
          | .ok _ => .error "expected ')' after the parenthesized formula"
          | .error e => .error e
      | .ident "true" :: rest => .ok (CTL.top, rest)
      | .ident "false" :: rest => .ok (CTL.not CTL.top, rest)
      | [] => .error "unexpected end of formula"
      | t :: _ => .error s!"unexpected token {reprStr t}"

def parseCtlFormula (doc : TVIRDocument) (s : String) : Except String CTL := do
  if (stripWs s).isEmpty then throw "empty formula"
  let toks ← ltlTokenize s
  let (f, rest) ← parseCtlLevel doc 0 toks
  unless rest.isEmpty do
    throw s!"unexpected trailing tokens ({rest.length} left, starting with {reprStr rest.head!})"
  return f

-- ============================================================================
-- Template specs
-- ============================================================================

-- Conjunction over a list without filler conjuncts:
-- [a, b, c] -> a && (b && c), [] -> top.
def andAll : List LTL → LTL
  | [] => LTL.top
  | [f] => f
  | f :: fs => LTL.and f (andAll fs)

-- a -> b in the LTL core syntax
def ltlImpl (a b : LTL) : LTL := LTL.not (LTL.and a (LTL.not b))

-- Expand the "Template specs" of the dump into concrete LTL properties
-- (the TVL docs: docs/specifications/{template,label-based}.md):
--   FinishingProperty: eventually every actor finishes --
--     F (A1.ACTOR_END && ... && An.ACTOR_END);
--   ValidityProperty ("if the protocol terminates, all channels must be
--     empty"): F (A_i.ACTOR_END -> queue_k empty) per actor/channel pair;
--   MsgDeliveredProperty (message delivery guarantee: every sent message
--     is eventually received): message identity is invisible in the queue
--     states, so a message counts as received once its channel drains --
--     G (!queueEmpty Q -> F queueEmpty Q) per channel that ever gets a
--     send;
--   RecoveryProperty (label-based): for every actor label pair
--     fail_X / start_X -- G (A.fail_X -> F A.start_X);
--   LossDetectionProperty (label-based): for every label pair
--     expired_msg_M (on A) / M_loss_detected (on any actor B) --
--     G (A.expired_msg_M -> F B.M_loss_detected).
--   AllTemplateProperties: every property above at once.
-- Label-based specs are named RecoveryProperty_A_fail_X_k /
-- LossDetectionProperty_A_expired_msg_M_k (k numbers the generated specs
-- from 0, as TVL itself does when it instantiates the template);
-- ValidityProperty / MsgDeliveredProperty specs are named
-- ValidityProperty_A_Q / MsgDeliveredProperty_Q per conjunct.
-- The ValidityProperty / MsgDeliveredProperty conjunctions are split into
-- one spec per conjunct (as the label-based templates already are): the
-- verdict over all specs is exactly the conjunction and a counterexample
-- pinpoints the violated pair -- and each check stays small. The LTL
-- engine enumerates 2^|closure| candidate atoms before filtering
-- (checkLTLCore), so one 9-conjunct ValidityProperty (closure 66 on the
-- example model) would enumerate ~2^66 subsets, while per-conjunct specs
-- stay at 2^10..2^12.
-- Unknown template names are skipped with a warning.
-- Returns (warnings, specs).
partial def expandTemplates (doc : TVIRDocument) : List String × List (String × LTL) := Id.run do
  let mut warnings : List String := []
  let mut specs : List (String × LTL) := []
  let mut recoveryIdx := 0
  let mut lossIdx := 0
  -- Every queue of the model (for ValidityProperty) and every queue that
  -- messages are sent into (for MsgDeliveredProperty).
  let queues :=
    (doc.actors.flatMap fun (_, g) => g.flatMap fun (_, n) => instrQueues n.instr) |>.eraseDups
  let pushedQueues :=
    (doc.actors.flatMap fun (_, g) => g.filterMap fun (_, n) =>
      match n.instr with
      | .push _ q _ => some q
      | _ => none) |>.eraseDups
  for name in doc.templateSpecs do
    if name == "AllTemplateProperties" then
      -- Every known template, as if each keyword were listed separately.
      let all := ["FinishingProperty", "ValidityProperty", "MsgDeliveredProperty",
                  "RecoveryProperty", "LossDetectionProperty"]
      let (ws, ss) := expandTemplates { doc with templateSpecs := all }
      warnings := warnings ++ ws
      specs := specs ++ ss
    else if name == "FinishingProperty" then
      let ends := doc.actors.map fun (a, _) => LTL.ap (AtomicProposition.actorFinished a)
      specs := specs ++ [("FinishingProperty", F (andAll ends))]
    else if name == "ValidityProperty" then
      let pairs := doc.actors.flatMap fun (a, _) => queues.map fun q => (a, q)
      if pairs.isEmpty then
        warnings := warnings ++
          ["template ValidityProperty: no channels in the model, nothing generated"]
      else
        specs := specs ++ (pairs.map fun (a, q) =>
          (s!"ValidityProperty_{a}_{q}",
           F (ltlImpl (LTL.ap (AtomicProposition.actorFinished a))
                      (LTL.ap (AtomicProposition.queueEmpty q)))))
    else if name == "MsgDeliveredProperty" then
      if pushedQueues.isEmpty then
        warnings := warnings ++
          ["template MsgDeliveredProperty: no message-sending instructions, nothing generated"]
      else
        specs := specs ++ (pushedQueues.map fun q =>
          (s!"MsgDeliveredProperty_{q}",
           G (ltlImpl (LTL.not (LTL.ap (AtomicProposition.queueEmpty q)))
                      (F (LTL.ap (AtomicProposition.queueEmpty q))))))
    else if name == "RecoveryProperty" then
      let mut generated := 0
      for (a, _) in doc.actors do
        for (la, l, pcFail) in doc.labels do
          if la == a && l.startsWith "fail_" then
            let suffix := dropChars 5 l
            match doc.labels.find? fun (la', l', _) => la' == a && l' == "start_" ++ suffix with
            | some (_, _, pcStart) =>
              specs := specs ++ [(s!"RecoveryProperty_{a}_{l}_{recoveryIdx}",
                                  G (ltlImpl (LTL.ap (AtomicProposition.actorAt a pcFail))
                                             (F (LTL.ap (AtomicProposition.actorAt a pcStart)))))]
              recoveryIdx := recoveryIdx + 1
              generated := generated + 1
            | none =>
              warnings := warnings ++
                [s!"template RecoveryProperty: label '{a}.{l}' has no matching 'start_{suffix}', skipped"]
      if generated == 0 then
        warnings := warnings ++
          ["template RecoveryProperty: no fail_*/start_* label pairs found, nothing generated"]
    else if name == "LossDetectionProperty" then
      let mut generated := 0
      for (la, l, pcExpired) in doc.labels do
        if l.startsWith "expired_msg_" then
          let msgName := dropChars "expired_msg_".length l
          let partner := msgName ++ "_loss_detected"
          -- The detector label may sit on any actor; the docs recommend a
          -- different one from the expiring side.
          match doc.labels.find? fun (_, l', _) => l' == partner with
          | some (lb, _, pcDetected) =>
            specs := specs ++ [(s!"LossDetectionProperty_{la}_expired_msg_{msgName}_{lossIdx}",
                                G (ltlImpl (LTL.ap (AtomicProposition.actorAt la pcExpired))
                                           (F (LTL.ap (AtomicProposition.actorAt lb pcDetected)))))]
            lossIdx := lossIdx + 1
            generated := generated + 1
          | none =>
            warnings := warnings ++
              [s!"template LossDetectionProperty: label '{la}.{l}' has no matching '{partner}', skipped"]
      if generated == 0 then
        warnings := warnings ++
          ["template LossDetectionProperty: no expired_msg_*/<msg>_loss_detected label pairs found, nothing generated"]
    else
      warnings := warnings ++
        [s!"unknown template spec '{name}', skipping (known: FinishingProperty, ValidityProperty, MsgDeliveredProperty, AllTemplateProperties, RecoveryProperty, LossDetectionProperty)"]
  return (warnings, specs)

-- Everything Main needs to run the checks: the expanded template specs
-- plus the parsed user specs, per logic.
structure SpecSet where
  ltl      : List (String × LTL)
  ctl      : List (String × CTL)
  warnings : List String

def checkedSpecs (doc : TVIRDocument) : Except String SpecSet := do
  let (tmplWarnings, ltlTmpl) := expandTemplates doc
  let mut ltl := ltlTmpl
  let mut ctl := []
  for us in doc.userSpecs do
    if us.logic == "ltl" then
      let phi ← parseLtlFormula doc us.formula |>.mapError fun m => s!"spec '{us.name}': {m}"
      ltl := ltl ++ [(us.name, phi)]
    else -- "ctl" (validated by the scanner)
      let phi ← parseCtlFormula doc us.formula |>.mapError fun m => s!"spec '{us.name}': {m}"
      ctl := ctl ++ [(us.name, phi)]
  return { ltl := ltl, ctl := ctl, warnings := tmplWarnings }
