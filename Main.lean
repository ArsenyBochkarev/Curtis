import TVL.TVIR.Frontend
import TVL.TVIR.Spec
import Engine.LTL
import Engine.CTL
import Opts.POR
import TVL.Output.CTL

-- ============================================================================
-- curtis -- the standalone CLI
--
--   usage: curtis [--debug] [--dot FILE] <input.tvir>
--
-- Reads a .tvir dump (the IR of a TVL model), rebuilds the runtime State
-- and checks every spec of the dump: template specs expanded into concrete
-- formulas, user specs parsed from the surface syntax of both logics.
--   exit 0 -- every spec holds
--   exit 1 -- some spec is violated
--   exit 2 -- usage / IO / parse error
--
-- LTL specs go to the Buchi-automaton engine; partial order reduction is
-- applied automatically, exactly as checkLTL does: never for formulas with
-- the X operator. CTL specs go to the explicit-graph labeling engine
-- (generateGraph + checkCTL); a violated CTL spec gets a witness trace
-- whenever the engine can build one (negation-headed formulas).
-- ============================================================================

structure CliOpts where
  debug       : Bool := false
  dotFile     : Option String := none
  channelSize : Option Nat := none
  input       : Option String := none

def usage : String :=
  "usage: curtis [--debug] [--dot FILE] [--channel-size N] <input.tvir>\n" ++
  "  --debug          model summary, expanded formulas and state counts on stderr\n" ++
  "  --dot FILE       also write the state graph as DOT (counterexample highlighted)\n" ++
  "  --channel-size N bound each message queue to N messages (default 10);\n" ++
  "                   a send into a full queue blocks until it drains\n" ++
  "exit codes: 0 -- all specs hold, 1 -- some spec violated, 2 -- error"

def parseArgs (args : List String) : Except String CliOpts := do
  let mut opts : CliOpts := {}
  let mut positional : List String := []
  let mut rest := args
  while let a :: rest' := rest do
    rest := rest'
    match a with
    | "--debug" => opts := { opts with debug := true }
    | "--dot" =>
        match rest' with
        | f :: rest'' =>
            if f.startsWith "-" then
              throw s!"--dot expects a file name, got '{f}'"
            opts := { opts with dotFile := some f }
            rest := rest''
        | [] => throw "--dot expects a file name"
    | "--channel-size" =>
        match rest' with
        | v :: rest'' =>
            match v.toNat? with
            | some n =>
                if n == 0 then
                  throw s!"--channel-size expects a positive integer, got '{v}'"
                else
                  opts := { opts with channelSize := some n }
                  rest := rest''
            | none => throw s!"--channel-size expects a positive integer, got '{v}'"
        | [] => throw "--channel-size expects a positive integer"
    | input =>
        if input.startsWith "-" then
          throw s!"unknown flag '{input}'"
        positional := positional ++ [input]
  if positional.isEmpty then throw "no input file given"
  if positional.length > 1 then
    throw s!"expected exactly one input file, got {positional.length}"
  return { opts with input := positional.head? }

-- IO with the error funneled into Except (so that a failure is just one
-- more match arm in the pipeline below).
def readFileSafe (path : String) : IO (Except String String) := do
  try return .ok (← IO.FS.readFile path)
  catch e => return .error s!"cannot read '{path}': {e}"

def writeFileSafe (path : String) (contents : String) : IO (Except String Unit) := do
  try return .ok (← IO.FS.writeFile path contents)
  catch e => return .error s!"cannot write '{path}': {e}"

-- An LTL formula back into surface syntax (for --debug); the F/G sugar of
-- the input is recovered from its encoding (until_ top / its negation).
partial def ltlToString (phi : LTL) : String :=
  match phi with
  | .top => "true"
  | .ap p => reprStr p
  | .not (.until_ .top (.not f)) => s!"[] ({ltlToString f})"
  | .not (.until_ .top f) => s!"[] (!({ltlToString f}))"
  | .not f => s!"!({ltlToString f})"
  | .until_ .top f => s!"<> ({ltlToString f})"
  | .until_ f g => s!"({ltlToString f} U {ltlToString g})"
  | .and f g => s!"({ltlToString f} && {ltlToString g})"
  | .next f => s!"X ({ltlToString f})"

-- A CTL formula back into surface syntax (for --debug); the quantifier
-- sugar of the input is recovered from the ex/eu/eg encodings. (The DOT
-- exporter has its own unicode ctlToString for graph labels.)
partial def ctlToSurface (phi : CTL) : String :=
  match phi with
  | .top => "true"
  | .ap p => reprStr p
  | .not (.eu .top (.not f)) => s!"AG ({ctlToSurface f})"
  | .not (.eu .top f) => s!"AG (!({ctlToSurface f}))"
  | .not (.eg (.not f)) => s!"AF ({ctlToSurface f})"
  | .not (.eg f) => s!"AF (!({ctlToSurface f}))"
  | .not (.ex (.not f)) => s!"AX ({ctlToSurface f})"
  | .not f => s!"!({ctlToSurface f})"
  | .ex f => s!"EX ({ctlToSurface f})"
  | .eu .top f => s!"EF ({ctlToSurface f})"
  | .eu f g => s!"E ({ctlToSurface f} U {ctlToSurface g})"
  | .eg f => s!"EG ({ctlToSurface f})"
  | .and f g => s!"({ctlToSurface f} && {ctlToSurface g})"

-- The pure half of the run: text -> (document, state, checkable specs).
-- Every possible failure (parse, label, formula) is a single error message
-- with a tvir:<line>: prefix.
def prepare (text : String) : Except String (TVIRDocument × State × SpecSet) := do
  let doc ← parseTVIR text
  let state ← buildInitialState doc
  let specSet ← checkedSpecs doc
  return (doc, state, specSet)

def runChecker (opts : CliOpts) : IO UInt32 := do
  let some input := opts.input
    | do IO.eprintln usage; return 2
  let text ← match ← readFileSafe input with
    | .error m => do IO.eprintln s!"curtis: error: {m}"; return 2
    | .ok t => pure t
  let (doc, state, specSet) ← match prepare text with
    | .error m => do IO.eprintln s!"curtis: error: {m}"; return 2
    | .ok p => pure p
  -- A run may override the default channel capacity (Rule 1 of the TVL
  -- semantics): sends into a full queue then block until it drains.
  let state := match opts.channelSize with
    | some n => { state with queueCap := n }
    | none => state
  -- Warnings (unknown template specs, key != id dump lines, unpaired
  -- labels) go to stderr and never affect the exit code.
  for w in doc.warnings ++ specSet.warnings do
    IO.eprintln s!"curtis: warning: {w}"
  if opts.debug then
    let instrCount := doc.actors.foldl (fun acc (_, g) => acc + g.length) 0
    IO.eprintln s!"model: {doc.actors.length} actors, {instrCount} instructions, {doc.labels.length} labels"
    IO.eprintln s!"queues: {String.intercalate ", " (state.queues.map (·.1))}"
    IO.eprintln s!"channel capacity: {state.queueCap}"
    for (name, phi) in specSet.ltl do
      IO.eprintln s!"[ltl] {name}: {ltlToString phi}"
    for (name, phi) in specSet.ctl do
      IO.eprintln s!"[ctl] {name}: {ctlToSurface phi}"
  if specSet.ltl.isEmpty && specSet.ctl.isEmpty then
    IO.println "curtis: no specs to check"
  let mut violated := false
  let mut cexForDot : Option (List String) := none
  for (name, phi) in specSet.ltl do
    -- The same reduction policy as checkLTL: never for formulas with X.
    let porOpt := if formulaUsesNext phi then none else some (getVisibleAPs phi)
    let (trace?, states) := checkLTLCore state phi porOpt
    match trace? with
    | none =>
        IO.println s!"[ltl] {name}: HOLDS"
        if opts.debug then IO.eprintln s!"  checked over {states} product states"
    | some t =>
        violated := true
        IO.println s!"[ltl] {name}: VIOLATED"
        let acts := traceToActionsMarked t
        IO.println "  counterexample (a lasso of actions):"
        for (a, i) in acts.zipIdx 1 do
          IO.println s!"    {i}. {a}"
        if opts.debug then IO.eprintln s!"  found over {states} product states"
        if cexForDot.isNone then cexForDot := some acts
  unless specSet.ctl.isEmpty do
    let graph := generateGraph state
    for (name, phi) in specSet.ctl do
      let marked := checkCTL graph phi
      let holds :=
        match marked.labels.lookup state with
        | some ctls => ctls.contains phi
        | none => false
      if holds then
        IO.println s!"[ctl] {name}: HOLDS"
      else
        violated := true
        IO.println s!"[ctl] {name}: VIOLATED"
        -- A linear witness exists for negation-headed formulas; for the
        -- other shapes the labeled graph (see --dot) is the explanation.
        match getCounterexample marked state phi with
        | some acts =>
            IO.println "  counterexample (a trace of actions):"
            for (a, i) in acts.zipIdx 1 do
              IO.println s!"    {i}. {a}"
            if cexForDot.isNone then cexForDot := some acts
        | none =>
            IO.println "  no linear counterexample for this formula shape (use --dot to inspect the graph)"
      if opts.debug then IO.eprintln s!"  checked over {graph.states.length} states"
  if let some dotFile := opts.dotFile then
    let graph := generateGraph state
    let dot := exportToDot graph state cexForDot
    match ← writeFileSafe dotFile dot with
    | .error m => do IO.eprintln s!"curtis: error: {m}"; return 2
    | .ok _ => pure ()
  return if violated then 1 else 0

def main (args : List String) : IO UInt32 :=
  match parseArgs args with
  | .error m => do
      IO.eprintln s!"curtis: error: {m}"
      IO.eprintln usage
      return 2
  | .ok opts => runChecker opts
