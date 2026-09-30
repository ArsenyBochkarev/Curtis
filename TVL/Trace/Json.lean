-- Minimal JSON parser for the canonical tvl-trace/1 counterexample format
-- (objects, arrays, strings, integers, booleans, null — the trace writer only
-- ever emits integers, so no floats are needed). Written in the same spirit
-- as TVL/TVIR/Frontend.lean: a recursive-descent parser over List Char with
-- Except String errors, no dependencies.

inductive Json where
  | obj   (fields : List (String × Json))
  | arr   (items : List Json)
  | str   (s : String)
  | num   (n : Int)
  | bool  (b : Bool)
  | null  : Json
  deriving BEq

namespace Json

/-- Field lookup (first match), none for non-objects or missing fields. -/
def field? : Json → String → Option Json
  | .obj fields, name => fields.lookup name
  | _, _ => none

/-- Integer value, none for anything else. -/
def asInt? : Json → Option Int
  | .num n => some n
  | _ => none

/-- String value, none for anything else. -/
def asString? : Json → Option String
  | .str s => some s
  | _ => none

/-- Array items, [] for anything else. -/
def items : Json → List Json
  | .arr xs => xs
  | _ => []

end Json

namespace JsonParser

private def skipWs : List Char → List Char
  | c :: rest => match c with
    | ' '  => skipWs rest
    | '\t' => skipWs rest
    | '\n' => skipWs rest
    | '\r' => skipWs rest
    | _    => c :: rest
  | [] => []

private def fail (msg : String) : Except String α := .error msg

private def isHexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

private def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

mutual

private partial def parseValue : List Char → Except String (Json × List Char)
  | [] => fail "unexpected end of JSON input"
  | cs =>
      match skipWs cs with
      | [] => fail "unexpected end of JSON input"
      | c :: rest =>
          match c with
          | '{' => parseObj rest
          | '[' => parseArr rest
          | '"' => do
              let (s, rest') ← parseString rest
              return (.str s, rest')
          | 't' => parseLit "true" (.bool true) (c :: rest)
          | 'f' => parseLit "false" (.bool false) (c :: rest)
          | 'n' => parseLit "null" .null (c :: rest)
          | _ =>
              if c == '-' || c.isDigit then parseNum (c :: rest)
              else fail s!"unexpected character '{c}'"

private partial def parseLit : String → Json → List Char → Except String (Json × List Char)
  | word, v, cs =>
      let n := word.length
      if cs.take n == word.toList then return (v, cs.drop n)
      else fail s!"expected '{word}'"

private partial def parseNum (cs : List Char) : Except String (Json × List Char) := do
  let neg := match cs with | '-' :: _ => true | _ => false
  let (ds, rest) := cs.dropWhile (· == '-') |>.span (·.isDigit)
  if ds.isEmpty then fail "expected a number"
  else
    let magnitude := ds.foldl (fun acc d => acc * 10 + (d.toNat - '0'.toNat)) 0
    return (.num (if neg then -magnitude else magnitude), rest)

private partial def parseStringAux (acc : String) : List Char → Except String (String × List Char)
  | [] => fail "unterminated string"
  | '"' :: rest => return (acc, rest)
  | '\\' :: e :: rest =>
      let cont (c : Char) (rest : List Char) : Except String (String × List Char) :=
        parseStringAux (acc.push c) rest
      match e with
      | '"'  => cont '"' rest
      | '\\' => cont '\\' rest
      | '/'  => cont '/' rest
      | 'b'  => cont (Char.ofNat 8) rest
      | 'f'  => cont (Char.ofNat 12) rest
      | 'n'  => cont '\n' rest
      | 'r'  => cont (Char.ofNat 13) rest
      | 't'  => cont '\t' rest
      | 'u'  =>
          let hex := rest.take 4
          if hex.length != 4 || !(hex.all isHexDigit) then fail "malformed \\u escape"
          else
            let val := hex.foldl (fun acc h => acc * 16 + hexVal h) 0
            cont (Char.ofNat val) (rest.drop 4)
      | other => fail s!"unknown escape '\\{other}'"
  | c :: rest => parseStringAux (acc.push c) rest

private partial def parseString (cs : List Char) : Except String (String × List Char) :=
  parseStringAux "" cs

private partial def parseObj (cs : List Char) : Except String (Json × List Char) := do
  match skipWs cs with
  | '}' :: rest => return (.obj [], rest)
  | _ => parseObj.objFields [] cs
where objFields (acc : List (String × Json)) (cs : List Char) :
      Except String (Json × List Char) := do
    match skipWs cs with
    | [] => fail "unterminated object"
    | '"' :: rest => do
        let (name, afterName) ← parseString rest
        match skipWs afterName with
        | ':' :: afterColon => do
            let (v, afterValue) ← parseValue afterColon
            match skipWs afterValue with
            | ',' :: nextField => objFields ((name, v) :: acc) nextField
            | '}' :: rest' => return (.obj (((name, v) :: acc).reverse), rest')
            | _ => fail "expected ',' or '}' in object"
        | _ => fail "expected ':' after object key"
    | _ => fail "expected '\"' (object key)"

private partial def parseArr (cs : List Char) : Except String (Json × List Char) := do
  match skipWs cs with
  | ']' :: rest => return (.arr [], rest)
  | _ => parseArr.arrItems [] cs
where arrItems (acc : List Json) (cs : List Char) : Except String (Json × List Char) := do
  let (v, afterValue) ← parseValue cs
  match skipWs afterValue with
  | ',' :: nextItem => arrItems (v :: acc) nextItem
  | ']' :: rest' => return (.arr ((v :: acc).reverse), rest')
  | _ => fail "expected ',' or ']' in array"

end

/-- Entry point: text -> JSON value (no trailing content allowed). -/
def parse (text : String) : Except String Json := do
  let (v, rest) ← parseValue text.toList
  if skipWs rest != [] then fail "trailing content after JSON value"
  return v
