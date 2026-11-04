import Solcore.Synthesis.Core.Generator
import Solcore.Synthesis.Source.ScalarMeaning.CallGraphEmitter
import Solcore.Synthesis.Source.ScalarMeaning.FunctionEmitter
import Solcore.Synthesis.Source.ScalarMeaning.MutationEmitter
import Solcore.Synthesis.Source.ScalarMeaning.PrimitiveEmitter
import Solcore.Test.Synthesis.CallGraphs
import Solcore.Test.Synthesis.Scalars
import Solcore.Test.Synthesis.Generators
import Solcore.Synthesis.Source.ScalarMeaning.AggregateCallGraphEmitter
import Solcore.Test.Synthesis.Aggregates
import Solcore.Synthesis.Source.AggregateCases
import Solcore.Synthesis.Source.ScalarMeaning.AggregateEmitter
import Solcore.Synthesis.Source.ScalarMeaning.CallGraphLoopEmitter
import Solcore.Synthesis.Source.GenericCases
import Solcore.Synthesis.Source.ScalarMeaning.GenericEmitter
import Solcore.Synthesis.Source.KeyedStorageCases
import Solcore.Synthesis.Source.ScalarMeaning.KeyedEmitter
import Solcore.ContractRuntime.CheckedContractRegistry
import Solcore.Synthesis.Source.EventLogCases
import Solcore.Synthesis.Source.ScalarMeaning.LogEmitter
import Solcore.Synthesis.Source.LoopCases
import Solcore.Synthesis.Source.ScalarMeaning.LoopEmitter
import Solcore.Test.Synthesis.Loops
import Solcore.Synthesis.Source.StorageRollbackCases
import Solcore.Synthesis.Source.StorageCases
import Solcore.Synthesis.Source.ScalarMeaning.RollbackEmitter
import Solcore.Synthesis.Source.ScalarMeaning.StorageEmitter

/-!
# Source meaning tests

The independent source meaning run on actual emitter output: scalars, aggregates, loops, generics, keyed
storage, logs and rollback.
-/

section
-- leanmerge: from Solcore.Test.SourceScalarMeaning
/-! Executable checks of the scalar source meaning on actual emitter output.
Each emitted text is lexed, parsed and run under the independent source
semantics, then compared with the original Core program on the Core machine.
The theorems in `ScalarMeaning.Emitter` cover every successful emission; these
checks exercise the same definitions and the tokenizer on real texts. -/
set_option autoImplicit false

namespace Tests.SourceScalarMeaning

open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.ScalarMeaning

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def coreWord (program : Program) : IO Nat :=
  match program.runStateful 100000 with
  | .done (.word word) _ => pure word.val
  | _ => throw (IO.userError "Core reference did not return a Word")

private def admit (body : Wire.Expr) : IO CheckedWordProgram :=
  match CheckedWordProgram.ofProgram? {resultType := .word, dataDefinitions := [], body} with
  | some program => pure program
  | none => throw (IO.userError "closed source-meaning fixture failed the G0 checker")

private def checkedFunction (body : Wire.Expr) : IO CheckedWordFunction :=
  match CheckedWordFunction.ofBody? body with
  | some function => pure function
  | none => throw (IO.userError "runtime-input source-meaning fixture failed its checker")

/-- The emitted text parses to a file whose printing is that text. -/
private def checkReprint (label source : String) : IO Unit := do
  let some file := parseSource source |
    throw (IO.userError s!"emitted source is outside the parsed fragment: {label}")
  ensure (file.print == source) s!"parsed source does not print back to the emitted text: {label}"

private def checkClosed (label : String) (program : CheckedWordProgram) : IO Unit := do
  let emitted ← match emit program with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"closed emission failed: {label}: {reprStr error}")
  checkReprint label emitted.source
  let expected ← coreWord program.program.toCore
  ensure (sourceCall emitted.source "run" [] == some expected)
    s!"closed source meaning differs from Core: {label}"
  ensure (sourceCall emitted.source "run" [0] == none)
    s!"closed method accepted an extra argument: {label}"
  ensure (sourceCall emitted.source "other" [] == none)
    s!"source call accepted an undeclared method: {label}"

def boundaryInputs : List Nat :=
  [0, 1, 2, 255, 256, 2 ^ 255 - 1, 2 ^ 255, 2 ^ 256 - 1]

private def checkInput (label : String) (function : CheckedWordFunction) : IO Unit := do
  let emitted ← match Input.emit function with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"input emission failed: {label}: {reprStr error}")
  checkReprint label emitted.source
  for input in boundaryInputs do
    let expected ← coreWord (function.instantiate (Word.ofNatModulo input)).toCore
    ensure (sourceCall emitted.source "run" [input] == some expected)
      s!"input source meaning differs from Core: {label} at {input}"
  ensure (sourceCall emitted.source "run" [2 ^ 256] == none)
    s!"input method accepted an argument outside uint256: {label}"
  ensure (sourceCall emitted.source "run" [] == none)
    s!"input method accepted a missing argument: {label}"

/-- Named helpers become free functions; each runtime input is compared with
the original Core binding chain. -/
private def checkFunctions (label : String) (helpers : List Wire.Expr) (entry : Wire.Expr) :
    IO Unit := do
  let some graph := CheckedWordFunctionDAG.ofParts? helpers entry |
    throw (IO.userError s!"named-helper fixture failed its checker: {label}")
  let emitted ← match Function.emit graph with
    | .ok value => pure value
    | .error error =>
        throw (IO.userError s!"named-helper emission failed: {label}: {reprStr error}")
  checkReprint label emitted.source
  for input in boundaryInputs do
    let expected ← coreWord (graph.instantiate (Word.ofNatModulo input)).toCore
    ensure (sourceCall emitted.source "run" [input] == some expected)
      s!"named-helper source meaning differs from Core: {label} at {input}"
  let undeclared := emitted.source.replace "= sc_fn0(" "= sc_fnx("
  ensure (undeclared != emitted.source) s!"named-helper fixture has no call to sc_fn0: {label}"
  ensure ((parseSource undeclared).isSome && sourceCall undeclared "run" [1] == none)
    s!"a call to an undeclared helper received a meaning: {label}"

private def wordExpr (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def high : Nat := 2 ^ 255
private def maximum : Nat := 2 ^ 256 - 1

private def emitPrimitive (label : String) (function : CheckedWordFunction) :
    IO EmittedProgram :=
  match Primitive.emit function with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"primitive emission failed: {label}: {reprStr error}")

/-- Raw primitive bodies: each runtime input is compared with the original
Core function. -/
private def checkPrimitive (label : String) (body : Wire.Expr) (inputs : List Nat) :
    IO Unit := do
  let function ← checkedFunction body
  let emitted ← emitPrimitive label function
  checkReprint label emitted.source
  for input in inputs ++ boundaryInputs do
    let expected ← coreWord (function.instantiate (Word.ofNatModulo input)).toCore
    ensure (sourceCall emitted.source "run" [input] == some expected)
      s!"primitive source meaning differs from Core: {label} at {input}"

/-- Zero divisors and moduli, out-of-range shifts, byte indices and sign
positions, negative signed operands and large exponents. -/
private def primitiveBoundaries : List (String × Wire.Expr × List Nat) :=
  [Wire.BinaryOp.wordDiv, .wordMod, .wordSdiv, .wordSmod].map (fun operation =>
      ("zero divisor", .binary operation (.var 0) (wordExpr 0), [])) ++
  [Wire.TernaryOp.wordAddMod, .wordMulMod].flatMap (fun operation =>
      [("zero modulus", .ternary operation (.var 0) (wordExpr maximum) (wordExpr 0), []),
        ("unit modulus", .ternary operation (.var 0) (wordExpr maximum) (wordExpr 1), []),
        ("large modulus",
          .ternary operation (.var 0) (wordExpr maximum) (wordExpr (maximum - 1)), [])]) ++
  [("shift left amount", .binary .wordShl (wordExpr 1) (.var 0), [257]),
    ("shift right amount", .binary .wordShr (wordExpr maximum) (.var 0), [257]),
    ("arithmetic shift negative", .binary .wordSar (wordExpr high) (.var 0), [257]),
    ("arithmetic shift positive", .binary .wordSar (wordExpr (high - 1)) (.var 0), [257]),
    ("signed division negative", .binary .wordSdiv (.var 0) (wordExpr 2), [maximum - 6]),
    ("signed division both negative", .binary .wordSdiv (.var 0) (wordExpr (maximum - 1)),
      [maximum - 6]),
    ("signed remainder negative", .binary .wordSmod (.var 0) (wordExpr (maximum - 1)),
      [maximum - 6, 7]),
    ("signed greater negative", .ifE (.binary .wordSgt (.var 0) (wordExpr high)) (wordExpr 1)
      (wordExpr 0), []),
    ("byte index", .binary .wordByte (.var 0) (wordExpr (high + 4660)), [30, 31, 32]),
    ("sign position", .binary .wordSignExtend (.var 0) (wordExpr 128), [31, 32]),
    ("sign extend word", .binary .wordSignExtend (wordExpr 1) (.var 0), [32768]),
    ("exponent", .binary .wordPow (wordExpr 2) (.var 0), [254, 257]),
    ("negative base", .binary .wordPow (wordExpr maximum) (.var 0), [3]),
    ("zero exponent", .binary .wordPow (.var 0) (wordExpr 0), []),
    ("nested primitives", .ternary .wordMulMod
      (.binary .wordShl (.var 0) (.unary .wordClz (.var 0)))
      (.binary .wordSar (.var 0) (wordExpr 3))
      (.letE (.binary .wordSmod (.var 0) (wordExpr 1000)) (.binary .wordAdd (.var 0) (.var 1))),
      [12345])]

/-- Hand-known results of the primitive fixtures, copied from the Core
regression in `SourcePrimitiveEmitter` and independent of both Core and the
source semantics. -/
private def knownPrimitiveResults : List (String × Nat × Nat) := [
  ("div", 1, 0), ("div", maximum, high - 1), ("mod", maximum, 1),
  ("shl", maximum, maximum - 1), ("shl", high, 0), ("shr", maximum, high - 1),
  ("sar", 5, 2), ("sar", maximum, maximum), ("sar", high, high + high / 2),
  ("sdiv", 7, maximum - 6), ("sdiv", maximum, 1), ("sdiv", high, high),
  ("smod", 7, 1), ("smod", maximum - 6, maximum), ("smod", high, 0),
  ("sgt", 1, 1), ("sgt", maximum, 0), ("sgt", high, 0), ("sgt", high - 1, 1),
  ("addmod", maximum, 1), ("addmod", maximum - 1, 0), ("mulmod", high, 1),
  ("clz", 0, 256), ("clz", 1, 255), ("clz", high, 0), ("clz", high - 1, 1),
  ("byte", maximum, 255), ("byte", high, 0), ("pow", maximum, 1), ("pow", high, 0),
  ("signextend", 127, 127), ("signextend", 128, maximum - 127), ("signextend", 256, 0)]

private def checkKnownPrimitives : IO Unit := do
  for (label, input, expected) in knownPrimitiveResults do
    let some (_, body) := Tests.SourcePrimitiveEmitter.fixtures.find? (·.1 == label) |
      throw (IO.userError s!"missing primitive fixture: {label}")
    let emitted ← emitPrimitive label (← checkedFunction body)
    ensure (sourceCall emitted.source "run" [input] == some expected)
      s!"primitive source meaning differs from its hand-known result: {label} at {input}"

/-- A call reaches only the opcode its alias imports. -/
private def checkPrimitiveImports : IO Unit := do
  let emitted ← emitPrimitive "import" (← checkedFunction (.binary .wordDiv (.var 0) (wordExpr 2)))
  ensure (sourceCall emitted.source "run" [7] == some 3) "the division fixture changed"
  let dropped := emitted.source.replace "div as sc_div, " ""
  ensure (dropped != emitted.source) "the import line lost its division alias"
  ensure ((parseSource dropped).isSome && sourceCall dropped "run" [7] == none)
    "a call to an alias that is not imported received a meaning"
  let swapped := emitted.source.replace "div as sc_div, mod as sc_mod"
    "mod as sc_div, div as sc_mod"
  ensure (swapped != emitted.source) "the import line changed its first aliases"
  ensure (sourceCall swapped "run" [7] == some 1)
    "an alias did not take the meaning of the opcode it imports"

private def callExpr (index : Nat) (argument : Wire.Expr) : Wire.Expr :=
  .apply (.var index) argument

/-- Call graphs: helpers may call earlier helpers and the raw opcode aliases.
Each input is compared with the original Core binding chain, and the listed
pairs also with hand-known Words from the Core regression in
`SourceCallGraphEmitter`. -/
private def checkCallGraph (label : String) (helpers : List Wire.Expr) (entry : Wire.Expr)
    (known : List (Nat × Nat)) : IO Unit := do
  let some graph := CheckedWordFunctionDAG.ofParts? helpers entry |
    throw (IO.userError s!"call-graph fixture failed its checker: {label}")
  let emitted ← match CallGraph.emit graph with
    | .ok value => pure value
    | .error error =>
        throw (IO.userError s!"call-graph emission failed: {label}: {reprStr error}")
  checkReprint label emitted.source
  for input in known.map Prod.fst ++ boundaryInputs do
    let expected ← coreWord (graph.instantiate (Word.ofNatModulo input)).toCore
    ensure (sourceCall emitted.source "run" [input] == some expected)
      s!"call-graph source meaning differs from Core: {label} at {input}"
  for (input, expected) in known do
    ensure (sourceCall emitted.source "run" [input] == some expected)
      s!"call-graph source meaning differs from its hand-known result: {label} at {input}"

/-- Raw opcodes applied to helper results, through an identity helper. -/
private def callGraphPrimitives : List (String × Wire.Expr × Nat × Nat) :=
  let c := callExpr 1
  [("clz", .unary .wordClz (c (.var 0)), 0, 256),
    ("div", .binary .wordDiv (c (.var 0)) (c (wordExpr 2)), 5, 2),
    ("mod", .binary .wordMod (c (.var 0)) (c (wordExpr 0)), maximum, 0),
    ("shl", .binary .wordShl (c (wordExpr 1)) (c (.var 0)), 255, high),
    ("shr", .binary .wordShr (c (wordExpr maximum)) (c (.var 0)), 256, 0),
    ("sar", .binary .wordSar (c (wordExpr high)) (c (.var 0)), maximum, maximum),
    ("sdiv", .binary .wordSdiv (c (.var 0)) (c (wordExpr maximum)), high, high),
    ("smod", .binary .wordSmod (c (.var 0)) (c (wordExpr 2)), maximum - 6, maximum),
    ("sgt", .ifE (.binary .wordSgt (c (.var 0)) (c (wordExpr 0))) (wordExpr 1) (wordExpr 0),
      high - 1, 1),
    ("byte", .binary .wordByte (c (.var 0)) (c (wordExpr 0x1234)), 31, 0x34),
    ("pow", .binary .wordPow (c (wordExpr maximum)) (c (.var 0)), maximum, maximum),
    ("signextend", .binary .wordSignExtend (c (wordExpr 0)) (c (.var 0)), 0x80, maximum - 0x7f),
    ("addmod", .ternary .wordAddMod (c (.var 0)) (c (wordExpr 1)) (c (wordExpr maximum)),
      maximum, 1),
    ("mulmod", .ternary .wordMulMod (c (.var 0)) (c (wordExpr 2)) (c (wordExpr maximum)),
      high, 1)]

private def checkCallGraphs : IO Unit := do
  checkCallGraph "mixed" Tests.SourceCallGraphEmitter.mixedHelpers
    Tests.SourceCallGraphEmitter.mixedEntry [(0, 11), (1, 6), (maximum, 1), (high, high / 2)]
  checkCallGraph "branch calls" [.binary .wordAdd (.var 0) (wordExpr 1)]
    (.ifE (.binary .wordEq (callExpr 1 (.var 0)) (wordExpr 1))
      (.letE (wordExpr 7) (callExpr 2 (.binary .wordAdd (.var 0) (.var 1))))
      (callExpr 1 (callExpr 1 (.var 0))))
    [(0, 8), (1, 3), (maximum, 1)]
  for (label, body, input, expected) in callGraphPrimitives do
    checkCallGraph s!"helper operands of {label}" [.var 0] body [(input, expected)]
  for (label, helpers, entry) in Tests.SourceFunctionEmitter.fixtures do
    checkCallGraph s!"named helpers {label}" helpers entry []

/-- Hand-known results of the mutation fixtures, copied from the Core regression
in `SourceMutationEmitter`. -/
private def knownMutation : List (String × (Nat → Nat)) := [
  ("load-before-store", fun input => (input + 2) % 2 ^ 256),
  ("independent-cells", fun input => (input + 11) % 2 ^ 256),
  ("callee-isolation", fun input => (2 * input + 3) % 2 ^ 256),
  ("unit-before-call", fun _ => 20),
  ("bool-and-unit", fun input => if input == 0 then 0 else (input + 1) % 2 ^ 256),
  ("nested-store-value", fun _ => 5)]

/-- Private mutable locals: each input is compared with the original Core
binding chain and with the hand-known result. -/
private def checkMutation (label : String) (helpers : List Wire.Expr) (entry : Wire.Expr) :
    IO Unit := do
  let some graph := LocalMutation.CheckedDAG.ofParts? helpers entry |
    throw (IO.userError s!"mutation fixture failed its checker: {label}")
  let emitted ← match Mutation.emit graph with
    | .ok value => pure value
    | .error error =>
        throw (IO.userError s!"mutation emission failed: {label}: {reprStr error}")
  checkReprint label emitted.source
  let some (_, known) := knownMutation.find? (·.1 == label) |
    throw (IO.userError s!"missing hand-known mutation result: {label}")
  for input in boundaryInputs do
    let expected ← coreWord (graph.instantiate (Word.ofNatModulo input)).toCore
    ensure (sourceCall emitted.source "run" [input] == some expected)
      s!"mutation source meaning differs from Core: {label} at {input}"
    ensure (expected == known input)
      s!"mutation Core result differs from its hand-known result: {label} at {input}"

/-- A write to a cell that was never declared has no meaning. -/
private def checkMutationRejection : IO Unit := do
  let some graph := LocalMutation.CheckedDAG.ofParts? [Tests.SourceMutationEmitter.snapshotBody]
      Tests.SourceMutationEmitter.entry |
    throw (IO.userError "mutation rejection fixture failed its checker")
  let emitted ← match Mutation.emit graph with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"mutation rejection emission failed: {reprStr error}")
  let undeclared := emitted.source.replace "sc_c0 = " "sc_c9 = "
  ensure (undeclared != emitted.source) "mutation fixture has no write to sc_c0"
  ensure ((parseSource undeclared).isSome && sourceCall undeclared "run" [1] == none)
    "a write to an undeclared cell received a meaning"

/-- Hand-known Words for the wrap-around and bitwise fixtures, independent of
both Core and the source semantics. -/
private def knownClosedResults : List (String × Nat) := [
  ("zero", 0), ("maximum", 2 ^ 256 - 1), ("add-wrap", 0), ("sub-wrap", 2 ^ 256 - 1),
  ("mul-wrap", 0), ("word-and", 8), ("word-or", 254), ("word-xor", 246),
  ("word-not", 2 ^ 256 - 11), ("word-equal", 1), ("word-greater-unsigned", 1),
  ("bool-not", 55), ("nested-locals", 2 ^ 256 - 2), ("branch-scope-true", 14),
  ("branch-scope-false", 29)]

private def checkKnown : IO Unit := do
  for (label, expected) in knownClosedResults do
    let some (_, body) := Tests.SourceSynthesisEmitter.fixtures.find? (·.1 == label) |
      throw (IO.userError s!"missing closed fixture: {label}")
    let emitted ← match emit (← admit body) with
      | .ok value => pure value
      | .error error => throw (IO.userError s!"closed emission failed: {label}: {reprStr error}")
    ensure (sourceCall emitted.source "run" [] == some expected)
      s!"closed source meaning differs from its hand-known result: {label}"

/-- Texts outside the fragment, or without a meaning, are rejected rather than
given a default value. -/
private def checkRejections : IO Unit := do
  let program ← admit (.ifE (.binary .wordEq (.word Word.zero) (.word Word.zero))
    (.word (Word.ofNatModulo 1)) (.word Word.zero))
  let emitted ← match emit program with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"rejection fixture emission failed: {reprStr error}")
  ensure ((emitted.source.splitOn "==").length == 2) "rejection fixture lost its equality"
  let spaced := emitted.source.replace "==" "= ="
  ensure (parseSource spaced).isNone "a split equality operator was accepted"
  let unparenthesized := emitted.source.replace "(sc_v0 == sc_v1)" "sc_v0 == sc_v1"
  ensure (unparenthesized != emitted.source) "rejection fixture changed its operand names"
  ensure (parseSource unparenthesized).isNone "an unparenthesized operator was accepted"
  let undeclared := emitted.source.replace "return uint256(sc_v3)" "return uint256(sc_v9)"
  ensure (undeclared != emitted.source) "rejection fixture changed its result name"
  ensure ((parseSource undeclared).isSome && sourceCall undeclared "run" [] == none)
    "an undeclared local received a meaning"
  let wrongType := emitted.source.replace "let sc_v2: bool" "let sc_v2: word"
  ensure (wrongType != emitted.source) "rejection fixture changed its condition binding"
  ensure ((parseSource wrongType).isSome && sourceCall wrongType "run" [] == none)
    "a mistyped declaration received a meaning"
  let large := emitted.source.replace "let sc_v0: word = 0;"
    s!"let sc_v0: word = {2 ^ 256};"
  ensure (large != emitted.source) "rejection fixture changed its first literal"
  ensure ((parseSource large).isSome && sourceCall large "run" [] == none)
    "a literal outside word received a meaning"

/-- Generated closed programs; unsupported operations are explicit emitter
errors and are only counted. -/
private def checkGenerated : IO (Nat × Nat) := do
  let mut checked := 0
  let mut excluded := 0
  for index in List.range 96 do
    match generate {seed := Seed.ofNat (index + 1), maxProgramNodes := 40} with
    | .error _ => excluded := excluded + 1
    | .ok generated =>
        match emit generated.checkedProgram with
        | .error _ => excluded := excluded + 1
        | .ok _ =>
            checkClosed s!"generated seed {index + 1}" generated.checkedProgram
            checked := checked + 1
  return (checked, excluded)

def testSourceScalarMeaning : IO Unit := do
  for (label, body) in Tests.SourceSynthesisEmitter.fixtures do
    checkClosed label (← admit body)
  checkKnown
  for (label, body) in Tests.SourceInputEmitter.fixtures do
    checkInput label (← checkedFunction body)
  for (label, helpers, entry) in Tests.SourceFunctionEmitter.fixtures do
    checkFunctions label helpers entry
  for (label, body) in Tests.SourcePrimitiveEmitter.fixtures do
    checkPrimitive label body []
  for (label, body, inputs) in primitiveBoundaries do
    checkPrimitive label body inputs
  checkKnownPrimitives
  checkPrimitiveImports
  checkCallGraphs
  for (label, helpers, entry) in Tests.SourceMutationEmitter.fixtures do
    checkMutation label helpers entry
  checkMutationRejection
  checkRejections
  let (checked, excluded) ← checkGenerated
  ensure (checked ≥ 16) s!"too few generated programs reached the source meaning: {checked}"
  let closed := Tests.SourceSynthesisEmitter.fixtures.length
  let inputs := Tests.SourceInputEmitter.fixtures.length
  let graphs := Tests.SourceFunctionEmitter.fixtures.length
  let primitives := Tests.SourcePrimitiveEmitter.fixtures.length + primitiveBoundaries.length
  let callGraphs := 2 + callGraphPrimitives.length + graphs
  let mutations := Tests.SourceMutationEmitter.fixtures.length
  IO.println (s!"scalar source meaning: {closed} closed fixtures, {inputs} input fixtures, " ++
    s!"{graphs} named-helper graphs, {primitives} raw primitive bodies, {callGraphs} " ++
    s!"call graphs and {mutations} mutation graphs x at least {boundaryInputs.length} " ++
    s!"inputs, {checked} generated programs ({excluded} excluded) agree with Core")

end Tests.SourceScalarMeaning
end

section
-- leanmerge: from Solcore.Test.SourceAggregateCallGraphMeaning
/-! Executable checks of the source meaning on actual aggregate call-graph
emitter output. Each emitted text is lexed, parsed and run under the
independent source semantics, then compared with the original Core binding
chain on the Core machine. `AggregateCallGraph.emit_source_meaning` covers
every successful emission; these checks exercise the same definitions, the
tokenizer and the unconditional alias import on real texts, and observe that
the final Core store is empty, which the theorem leaves existential. -/
set_option autoImplicit false

namespace Tests.SourceAggregateCallGraphMeaning

open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.ScalarMeaning
open Solcore.Synthesis.Core.Aggregates (CheckedDAG)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- The Word that Core returns. The renderer refuses cells, so the final store
must be empty. -/
private def coreWord (label : String) (program : Program) : IO Nat :=
  match program.runStateful 100000 with
  | .done (.word word) store => do
      ensure store.isEmpty s!"aggregate call-graph Core run left a cell: {label}"
      pure word.val
  | _ => throw (IO.userError s!"Core reference did not return a Word: {label}")

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def call (index : Nat) (argument : Wire.Expr) : Wire.Expr := .apply (.var index) argument
private def wrap (value : Nat) : Nat := value % 2 ^ 256
private def maximum : Nat := 2 ^ 256 - 1
private def high : Nat := 2 ^ 255

private def checked (label : String) (helpers : List Wire.Expr) (entry : Wire.Expr) :
    IO CheckedDAG :=
  match CheckedDAG.ofParts? helpers entry with
  | some graph => pure graph
  | none => throw (IO.userError s!"aggregate call-graph fixture failed its checker: {label}")

private def emitted (label : String) (graph : CheckedDAG) : IO EmittedProgram :=
  match AggregateCallGraph.emit graph with
  | .ok value => pure value
  | .error error =>
      throw (IO.userError s!"aggregate call-graph emission failed: {label}: {reprStr error}")

/-- The emitted text parses to a file whose printing is that text, with one free
function per helper and the raw opcode aliases always imported. -/
private def checkReprint (label : String) (graph : CheckedDAG) (source : String) : IO Unit := do
  let some file := parseSource source |
    throw (IO.userError s!"emitted aggregate call-graph source is outside the fragment: {label}")
  ensure (file.print == source)
    s!"parsed aggregate call-graph source does not print back: {label}"
  ensure (file.opcodeAliases == primitiveAliases &&
      file.functions.length == graph.helpers.length &&
      file.contract == AggregateCallGraph.contractName)
    s!"aggregate call-graph file has other aliases, helpers or contract: {label}"

/-- Every boundary input, and every input with a hand-known result, agrees with
Core; a hand-known formula must agree as well. Returns the emitted text. -/
private def checkGraph (label : String) (graph : CheckedDAG) (known : List (Nat × Nat) := [])
    (formula : Option (Nat → Nat) := none) : IO String := do
  let program ← emitted label graph
  checkReprint label graph program.source
  for input in known.map Prod.fst ++ Tests.SourceScalarMeaning.boundaryInputs do
    let expected ← coreWord label (graph.instantiate (Word.ofNatModulo input)).toCore
    ensure (sourceCall program.source "run" [input] == some expected)
      s!"aggregate call-graph source meaning differs from Core: {label} at {input}"
    if let some result := formula then
      ensure (expected == result input)
        s!"aggregate call-graph Core result differs from its formula: {label} at {input}"
  for (input, expected) in known do
    ensure (sourceCall program.source "run" [input] == some expected)
      s!"aggregate call-graph source differs from its hand-known result: {label} at {input}"
  ensure (sourceCall program.source "run" [2 ^ 256] == none)
    s!"aggregate call-graph method accepted an argument outside uint256: {label}"
  return program.source

/-- The nine minimal composition shapes of `SourceAggregateCallGraphEmitter` and
its scalar, adjacent and outer-local graphs, over the identity helper, with
hand-known results. -/
private def shapeFixtures : List (String × Wire.Expr × (Nat → Nat)) := [
  ("pair-component-call", .first (.pair (call 1 (.var 0)) (word 2)), fun input => input),
  ("sum-payload-call", .letE (.inRight .word (call 1 (.var 0))) (word 3), fun _ => 3),
  ("projected-call-argument", .letE (.pair (.var 0) (word 1)) (call 2 (.second (.var 0))),
    fun _ => 1),
  ("case-scrutinee-call", .caseE (.ifE (.binary .wordEq (call 1 (.var 0)) (word 0))
      (.inLeft .word (word 1)) (.inRight .word (word 2))) (.var 0) (word 7),
    fun input => if input == 0 then 1 else 7),
  ("case-branch-call", .caseE (.inLeft .word (.var 0)) (call 2 (.var 1)) (word 0),
    fun input => input),
  ("payload-call-argument", .letE (call 1 (.var 0))
      (.caseE (.inRight .word (.var 0)) (word 0) (call 3 (.var 0))),
    fun input => input),
  ("aggregate-let", .letE (.inLeft .word (.var 0)) (call 2 (.var 1)), fun input => input),
  ("aggregate-branch", .letE (call 1 (.var 0))
      (.first (.ifE (.bool true) (.pair (.var 0) (word 1)) (.pair (word 2) (.var 0)))),
    fun input => input),
  ("nested-case", .letE (call 1 (.var 0))
      (.caseE (.inLeft .word (.var 0)) (.caseE (.inRight .word (.var 0)) (.var 0) (.var 1))
        (word 0)),
    fun input => input),
  ("scalar-call", call 1 (.var 0), fun input => input),
  ("adjacent-call", .binary .wordAdd (call 1 (.var 0)) (.first (.pair (.var 0) (word 1))),
    fun input => wrap (2 * input)),
  ("outer-local", .caseE (.inLeft .word (word 1)) (call 2 (.var 1)) (word 0),
    fun input => input)]

/-- Raw opcodes applied to helper results, with the hand-known results of the
call-graph checks in `SourceScalarMeaning`. -/
private def primitiveBodies : List (String × Wire.Expr × Nat × Nat) :=
  let c := call 1
  [("clz", .unary .wordClz (c (.var 0)), 0, 256),
    ("div", .binary .wordDiv (c (.var 0)) (c (word 2)), 5, 2),
    ("mod", .binary .wordMod (c (.var 0)) (c (word 0)), maximum, 0),
    ("shl", .binary .wordShl (c (word 1)) (c (.var 0)), 255, high),
    ("shr", .binary .wordShr (c (word maximum)) (c (.var 0)), 256, 0),
    ("sar", .binary .wordSar (c (word high)) (c (.var 0)), maximum, maximum),
    ("sdiv", .binary .wordSdiv (c (.var 0)) (c (word maximum)), high, high),
    ("smod", .binary .wordSmod (c (.var 0)) (c (word 2)), maximum - 6, maximum),
    ("sgt", .ifE (.binary .wordSgt (c (.var 0)) (c (word 0))) (word 1) (word 0), high - 1, 1),
    ("byte", .binary .wordByte (c (.var 0)) (c (word 0x1234)), 31, 0x34),
    ("pow", .binary .wordPow (c (word maximum)) (c (.var 0)), maximum, maximum),
    ("signextend", .binary .wordSignExtend (c (word 0)) (c (.var 0)), 0x80, maximum - 0x7f),
    ("addmod", .ternary .wordAddMod (c (.var 0)) (c (word 1)) (c (word maximum)), maximum, 1),
    ("mulmod", .ternary .wordMulMod (c (.var 0)) (c (word 2)) (c (word maximum)), high, 1)]

/-- A Word placed in a pair and projected back, or carried as a right payload
and returned from its case. -/
private def aggregateWrappers : List (String × (Wire.Expr → Wire.Expr)) := [
  ("projected", fun body => .first (.pair body (.var 0))),
  ("payload", fun body => .caseE (.inRight .word body) (word 0) (.var 0))]

/-- Generated graphs from the `runtime-aggregate-call-graphs` generator, which
together cover every composition shape. -/
private def checkGenerated : IO Nat := do
  let mut count := 0
  let mut shapes : List String := []
  for budget in [96, 192, 256] do
    for seed in List.range 8 do
      match AggregateCallGraph.generate {seed := Seed.ofNat seed, maxProgramNodes := budget} with
      | .error error => throw (IO.userError
          s!"aggregate call-graph generator failed at seed {seed}: {reprStr error}")
      | .ok generated =>
          let graph := generated.function
          let _ ← checkGraph s!"generated budget {budget} seed {seed}" graph
          shapes := (shapes ++ AggregateCallGraph.structuralShapes graph).eraseDups
          count := count + 1
  ensure (AggregateCallGraph.shapeCatalog.all shapes.contains)
    "generated aggregate call graphs missed a composition shape"
  return count

/-- Texts outside the fragment, or without a meaning, are rejected rather than
given a default value. -/
private def checkRejections (shapesSource payloadSource primitiveSource : String) :
    IO Unit := do
  let swapped := payloadSource.replace "case inl(" "case inr("
  ensure (swapped != payloadSource) "payload fixture has no left case"
  ensure (parseSource swapped).isNone "a sum match with two right cases was accepted"
  let escaped := payloadSource.replace "return uint256(sc_v2);" "return uint256(sc_p5);"
  ensure (escaped != payloadSource) "payload fixture changed its result name"
  ensure ((parseSource escaped).isSome && sourceCall escaped "run" [1] == none)
    "a case payload received a meaning after its case"
  let paired := shapesSource.replace "let sc_v12: word = (sc_v6 + sc_v9);"
    "let sc_v12: word = sc_fn0(sc_v4);"
  ensure (paired != shapesSource) "all-shapes fixture changed its second helper"
  ensure ((parseSource paired).isSome && sourceCall paired "run" [1] == none)
    "a helper applied to a pair received a meaning"
  let pairResult := shapesSource.replace "    return sc_v12;" "    return sc_v4;"
  ensure (pairResult != shapesSource) "all-shapes fixture changed its second helper result"
  ensure ((parseSource pairResult).isSome && sourceCall pairResult "run" [1] == none)
    "a helper that returns a pair for a word received a meaning"
  match shapesSource.splitOn "\n\n" with
  | [imports, first, second, contract] =>
      let reordered := "\n\n".intercalate [imports, second, first, contract]
      ensure ((parseSource reordered).isSome && sourceCall reordered "run" [1] == none)
        "a helper that calls a later helper received a meaning"
  | _ => throw (IO.userError "all-shapes fixture no longer has two helpers")
  let stripped := primitiveSource.replace (Primitive.opcodeImport ++ "\n") ""
  ensure (stripped != primitiveSource) "primitive fixture has no alias import"
  ensure ((parseSource stripped).isSome && sourceCall stripped "run" [1] == none)
    "a primitive text without its alias import received a meaning"

def testSourceAggregateCallGraphMeaning : IO Unit := do
  let shapes ← checked "all shapes" Tests.SourceAggregateCallGraphEmitter.allShapesHelpers
    Tests.SourceAggregateCallGraphEmitter.allShapesEntry
  -- x > 5: 8x + 4 through the left payload; otherwise 4x + 1 through the right.
  let shapesSource ← checkGraph "all shapes" shapes
    (formula := some fun input => if input > 5 then wrap (8 * input + 4) else 4 * input + 1)
  for (label, entry, formula) in shapeFixtures do
    let _ ← checkGraph label (← checked label [.var 0] entry) (formula := some formula)
  let projected ← checked "projected call pair" [.var 0]
    (.first (.pair (call 1 (.var 0)) (.var 0)))
  let _ ← checkGraph "projected call pair" projected [(9, 9)] (some fun input => input)
  let payload ← checked "payload helper call" [.binary .wordAdd (.var 0) (word 1)]
    (.letE (.inRight .word (.var 0)) (.caseE (.var 0) (word 0) (call 3 (.var 0))))
  let payloadSource ← checkGraph "payload helper call" payload [(41, 42)]
    (some fun input => wrap (input + 1))
  let mixed ← checked "call-graph mixed" Tests.SourceCallGraphEmitter.mixedHelpers
    Tests.SourceCallGraphEmitter.mixedEntry
  let _ ← checkGraph "call-graph mixed" mixed [(0, 11), (1, 6), (maximum, 1), (high, high / 2)]
  let mut primitiveSource := ""
  for (wrapper, aggregate) in aggregateWrappers do
    for (label, body, input, expected) in primitiveBodies do
      let graph ← checked s!"{wrapper} {label}" [.var 0] (aggregate body)
      let source ← checkGraph s!"{wrapper} {label}" graph [(input, expected)]
      if primitiveSource.isEmpty then primitiveSource := source
  let generated ← checkGenerated
  checkRejections shapesSource payloadSource primitiveSource
  IO.println (s!"aggregate call-graph source meaning: the all-shapes graph, " ++
    s!"{shapeFixtures.length} shape fixtures, 3 call fixtures, " ++
    s!"{aggregateWrappers.length * primitiveBodies.length} raw primitive bodies and " ++
    s!"{generated} generated graphs x {Tests.SourceScalarMeaning.boundaryInputs.length} " ++
    "inputs agree with Core")

end Tests.SourceAggregateCallGraphMeaning
end

section
-- leanmerge: from Solcore.Test.SourceAggregateMeaning
/-! Executable checks of the source meaning on actual aggregate emitter
output. Each emitted text is lexed, parsed and run under the independent
source semantics, then compared with the original Core binding chain on the
Core machine. `Aggregate.emit_source_meaning` covers every successful
emission; these checks exercise the same definitions, the tokenizer and the
conditional alias import on real texts. -/
set_option autoImplicit false

namespace Tests.SourceAggregateMeaning

open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.ScalarMeaning
open Solcore.Synthesis.Core.Aggregates (CheckedDAG)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def coreWord (program : Program) : IO Nat :=
  match program.runStateful 100000 with
  | .done (.word word) _ => pure word.val
  | _ => throw (IO.userError "Core reference did not return a Word")

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def arg : Wire.Expr := .var 0
private def entry : Wire.Expr := .apply (.var 1) (.var 0)

private def checked (label : String) (helpers : List Wire.Expr) (body : Wire.Expr := entry) :
    IO CheckedDAG :=
  match CheckedDAG.ofParts? helpers body with
  | some graph => pure graph
  | none => throw (IO.userError s!"aggregate fixture failed its checker: {label}")

private def emitted (label : String) (graph : CheckedDAG) : IO EmittedProgram :=
  match Aggregate.emit graph with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"aggregate emission failed: {label}: {reprStr error}")

/-- The emitted text parses to a file whose printing is that text, and the file
imports the raw opcode aliases exactly when a rendered body uses one. -/
private def checkReprint (label : String) (graph : CheckedDAG) (source : String) : IO Unit := do
  let some file := parseSource source |
    throw (IO.userError s!"emitted aggregate source is outside the parsed fragment: {label}")
  ensure (file.print == source) s!"parsed aggregate source does not print back: {label}"
  let uses := (graph.helpers ++ [graph.entry]).any AggregateRenderer.usesOpcodeAliases
  ensure (file.opcodeAliases == if uses then primitiveAliases else [])
    s!"aggregate alias import does not follow alias use: {label}"

/-- Every boundary input agrees with Core; an optional hand-known formula must
agree as well. Returns the emitted text. -/
private def checkAggregate (label : String) (graph : CheckedDAG)
    (known : Option (Nat → Nat) := none) : IO String := do
  let program ← emitted label graph
  checkReprint label graph program.source
  for input in Tests.SourceScalarMeaning.boundaryInputs do
    let expected ← coreWord (graph.instantiate (Word.ofNatModulo input)).toCore
    ensure (sourceCall program.source "run" [input] == some expected)
      s!"aggregate source meaning differs from Core: {label} at {input}"
    if let some formula := known then
      ensure (expected == formula input)
        s!"aggregate Core result differs from its hand-known result: {label} at {input}"
  ensure (sourceCall program.source "run" [2 ^ 256] == none)
    s!"aggregate method accepted an argument outside uint256: {label}"
  return program.source

private def wrap (value : Nat) : Nat := value % 2 ^ 256

/-- Hand-known results of the aggregate emitter regression fixtures, as
general formulas of the input. -/
private def knownFixtures : List (String × (Nat → Nat)) := [
  ("pair-snapshot", fun input => wrap (input + 2)),
  ("projection-once", fun input => wrap (2 * input + 3)),
  ("sum-snapshot", fun input => wrap (input + if input == 0 then 9 else 10)),
  ("payload-helper-isolation", fun input => if input == 0 then 7 else wrap (2 * input + 4)),
  ("aggregate-case-joins", fun input => if input == 0 then 10 else wrap (2 * input + 22)),
  ("unit-case-effects", fun input => if input == 0 then 7 else wrap (input + 1))]

/-- The template result of `AggregateCases` for a scalar part, as a formula. -/
private def templateResult (pattern input scalar : Nat) : Nat :=
  let high := input ≥ 2 ^ 255
  if pattern = 0 then wrap (input + scalar)
  else if pattern = 1 then (if high then input ^^^ scalar else wrap (input + scalar))
  else if pattern = 2 then wrap (input + if high then scalar + scalar else scalar)
  else wrap (input + if high then input ^^^ scalar else wrap (input + scalar))

/-- Raw primitives inside and around aggregates, so the file imports the
aliases. -/
private def primitiveBodies : List (String × Wire.Expr) := [
  ("clz", .unary .wordClz arg),
  ("addmod", .ternary .wordAddMod arg (word 3) arg),
  ("mulmod-zero", .ternary .wordMulMod (word 5) arg (word 0)),
  ("sgt-branch", .ifE (.binary .wordSgt arg (word 1)) (.binary .wordDiv arg arg) (word 0)),
  ("pair-div-shl", .letE (.pair (.binary .wordDiv arg (word 3)) (.binary .wordShl arg (word 4)))
    (.binary .wordAdd (.first (.var 0)) (.second (.var 0)))),
  ("case-sdiv-sar", .caseE (.ifE (.binary .wordSgt arg (word 0))
      (.inLeft .word (.binary .wordSdiv arg (word 7)))
      (.inRight .word (.binary .wordSar arg (word 2))))
    (.binary .wordSmod (.var 0) (word 5)) (.binary .wordByte (word 31) (.var 0))),
  ("cell-exp-signextend", .letE (.newCell .word arg)
    (.letE (.storeCell (.var 0) (.binary .wordPow (.loadCell (.var 0)) (word 3)))
      (.binary .wordSignExtend (word 0) (.loadCell (.var 1))))),
  ("shr-mod-sum", .letE (.inRight .word (.binary .wordShr arg (word 255)))
    (.caseE (.var 0) (.var 0) (.binary .wordMod (.var 0) (word 2))))] ++
  ([Wire.BinaryOp.wordDiv, .wordMod, .wordShl, .wordShr, .wordSar, .wordSdiv, .wordSmod,
    .wordByte, .wordPow, .wordSignExtend].map fun operation =>
      (reprStr operation, .binary operation arg (word 255)))

/-- Generated aggregate graphs from the `runtime-aggregates` generator. -/
private def checkGenerated : IO Nat := do
  let mut count := 0
  for seed in List.range 24 do
    match Aggregate.generatedFunction (Seed.ofNat seed) 256 with
    | .error error => throw (IO.userError s!"aggregate generator failed at seed {seed}: {error}")
    | .ok (graph, _) =>
        let _ ← checkAggregate s!"generated seed {seed}" graph
        count := count + 1
  return count

/-- Texts outside the fragment, or without a meaning, are rejected rather than
given a default value. -/
private def checkRejections (pairSource sumSource primitiveSource : String) : IO Unit := do
  let swapped := sumSource.replace "case inl(" "case inr("
  ensure (swapped != sumSource) "sum fixture has no left case"
  ensure (parseSource swapped).isNone "a sum match with two right cases was accepted"
  let escaped := sumSource.replace "    return sc_v10;" "    return sc_p11;"
  ensure (escaped != sumSource) "sum fixture changed its result name"
  ensure ((parseSource escaped).isSome && sourceCall escaped "run" [1] == none)
    "a case payload received a meaning after its case"
  let notSum := sumSource.replace "match (sc_v8)" "match (sc_c0)"
  ensure (notSum != sumSource) "sum fixture changed its scrutinee"
  ensure ((parseSource notSum).isSome && sourceCall notSum "run" [1] == none)
    "a sum match on a word received a meaning"
  let notWord := pairSource.replace "(sc_v1, sc_v3)" "(sc_v1, true)"
  ensure (notWord != pairSource) "pair fixture changed its components"
  ensure ((parseSource notWord).isSome && sourceCall notWord "run" [1] == none)
    "a pair with a Boolean component received a meaning"
  let mistyped := pairSource.replace "sc_v7 = sc_p8;" "sc_v7 = sc_v5;"
  ensure (mistyped != pairSource) "pair fixture changed its projection"
  ensure ((parseSource mistyped).isSome && sourceCall mistyped "run" [1] == none)
    "assigning a pair to a word received a meaning"
  let unimported := pairSource.replace "(sc_v7 + sc_v10)" "sc_div(sc_v7, sc_v10)"
  ensure (unimported != pairSource) "pair fixture changed its final sum"
  ensure ((parseSource unimported).isSome && sourceCall unimported "run" [1] == none)
    "a call to an alias that is not imported received a meaning"
  let importLine := "import { " ++ ", ".intercalate AggregateRenderer.opcodeAliases ++
    " } from std.opcodes;\n"
  let stripped := primitiveSource.replace importLine ""
  ensure (stripped != primitiveSource) "primitive fixture has no alias import"
  ensure ((parseSource stripped).isSome && sourceCall stripped "run" [1] == none)
    "a primitive text without its alias import received a meaning"

def testSourceAggregateMeaning : IO Unit := do
  let mut pairSource := ""
  let mut sumSource := ""
  for (label, helpers, body) in Tests.SourceAggregateEmitter.fixtures do
    let some (_, known) := knownFixtures.find? (·.1 == label) |
      throw (IO.userError s!"missing hand-known aggregate result: {label}")
    let source ← checkAggregate label (← checked label helpers body) known
    if label == "pair-snapshot" then pairSource := source
    if label == "sum-snapshot" then sumSource := source
  let mut joins := 0
  for target in [Aggregates.Target.word, .bool, .unit, .wordPair, .wordSum] do
    for useCase in [false, true] do
      let label := s!"join {reprStr target} {useCase}"
      let graph ← checked label [Tests.SourceAggregateEmitter.joinBody target useCase]
      let _ ← checkAggregate label graph (some fun input =>
        if target == .unit then 17 else if input == 0 then 13 else 11)
      joins := joins + 1
  for pattern in List.range 4 do
    let label := s!"template {pattern}"
    let graph ← checked label [Aggregate.template pattern (word 2)]
    let _ ← checkAggregate label graph (some fun input => templateResult pattern input 2)
  let mut primitiveSource := ""
  for (label, body) in primitiveBodies do
    let graph ← checked label [body]
    ensure (AggregateRenderer.usesOpcodeAliases body) s!"primitive body uses no alias: {label}"
    primitiveSource ← checkAggregate label graph
  let generated ← checkGenerated
  checkRejections pairSource sumSource primitiveSource
  let fixtures := Tests.SourceAggregateEmitter.fixtures.length
  IO.println (s!"aggregate source meaning: {fixtures} emitter fixtures, {joins} joins, " ++
    s!"4 templates, {primitiveBodies.length} raw primitive bodies and {generated} generated " ++
    s!"graphs x {Tests.SourceScalarMeaning.boundaryInputs.length} inputs agree with Core")

end Tests.SourceAggregateMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCallGraphLoopMeaning
/-! Executable checks of the loop meaning on actual call-graph loop emitter
output. Each emitted text is lexed, parsed with the loop grammar and run under
the fuel-indexed source semantics, then compared with the original Core
bounded loop on the Core machine. `CallGraphLoop.emit_source_meaning` covers
every successful emission; these checks exercise the same definitions on real
texts. They also observe the exact fuel each loop needs, that the final Core
store is the accumulator cell holding the result (the theorem leaves the store
existential), that loop-free texts keep their `sourceCall` meaning, and that
altered loops lose or change their meaning. -/
set_option autoImplicit false

namespace Tests.SourceCallGraphLoopMeaning

open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.ScalarMeaning
open Solcore.Synthesis.Core.CallGraphLoop (CheckedPlan)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- The Word that Core returns. The final store must be the one accumulator
cell, holding that Word. -/
private def coreWord (label : String) (program : Program) : IO Nat :=
  match program.runStateful 100000 with
  | .done (.word word) [.word cell] => do
      ensure (cell == word) s!"call-graph loop accumulator differs from its result: {label}"
      pure word.val
  | _ => throw (IO.userError s!"Core loop did not return a Word with one cell: {label}")

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def call (index : Nat) (argument : Wire.Expr) : Wire.Expr := .apply (.var index) argument
private def wrap (value : Nat) : Nat := value % 2 ^ 256
private def maximum : Nat := 2 ^ 256 - 1
private def high : Nat := 2 ^ 255

/-- `count` applications of `step`. -/
private def iterate (step : Nat → Nat) : Nat → Nat → Nat
  | 0, value => value
  | count + 1, value => iterate step count (step value)

private def checkedPlan (label : String) (helpers : List Wire.Expr) (entry : Wire.Expr)
    (mask : Nat) : IO CheckedPlan := do
  let some graph := CheckedWordFunctionDAG.ofParts? helpers entry |
    throw (IO.userError s!"call-graph loop step failed its checker: {label}")
  let some plan := CheckedPlan.ofParts? graph mask |
    throw (IO.userError s!"call-graph loop plan failed its checker: {label}")
  pure plan

private def emitted (label : String) (plan : CheckedPlan) : IO EmittedProgram :=
  match CallGraphLoop.emit plan with
  | .ok value => pure value
  | .error error =>
      throw (IO.userError s!"call-graph loop emission failed: {label}: {reprStr error}")

/-- The emitted text parses with the loop grammar to a file whose printing is
that text, with the raw aliases, one free function per helper and `sc_step`
last. The loop-free grammar rejects it. -/
private def checkReprint (label : String) (plan : CheckedPlan) (source : String) : IO Unit := do
  let some file := parseLoopSource source |
    throw (IO.userError s!"emitted call-graph loop source is outside the fragment: {label}")
  ensure (file.print == source) s!"parsed call-graph loop source does not print back: {label}"
  ensure (file.opcodeAliases == primitiveAliases &&
      file.functions.length == plan.graph.helpers.length + 1 &&
      (file.functions.getLast?.map (·.name)) == some "sc_step" &&
      file.contract == CallGraphLoop.contractName)
    s!"call-graph loop file has other aliases, functions or contract: {label}"
  ensure (parseSource source).isNone
    s!"the loop-free grammar accepted a call-graph loop text: {label}"

/-- Every boundary input, the iteration counts three, six and seven, and every
input with a hand-known result agree with Core once the loop has one more unit
of fuel than iterations; less fuel has no meaning. A hand-known formula must
agree as well. Returns the emitted text. -/
private def checkPlan (label : String) (plan : CheckedPlan) (known : List (Nat × Nat) := [])
    (formula : Option (Nat → Nat) := none) : IO String := do
  let program ← emitted label plan
  checkReprint label plan program.source
  let inputs := known.map Prod.fst ++ Tests.SourceScalarMeaning.boundaryInputs ++ [3, 6, 7]
  for input in inputs do
    let expected ← coreWord label (plan.instantiate (Word.ofNatModulo input)).toCore
    let iterations := input &&& plan.mask
    for fuel in [iterations + 1, plan.mask + 1, 64] do
      ensure (loopSourceCall fuel program.source "run" [input] == some expected)
        s!"call-graph loop source meaning differs from Core: {label} at {input}, fuel {fuel}"
    ensure (loopSourceCall iterations program.source "run" [input] == none)
      s!"call-graph loop finished with fewer condition evaluations: {label} at {input}"
    ensure (sourceCall program.source "run" [input] == none)
      s!"the loop-free meaning gave a call-graph loop a result: {label} at {input}"
    if let some result := formula then
      ensure (expected == result input)
        s!"call-graph loop Core result differs from its formula: {label} at {input}"
  for (input, expected) in known do
    ensure (loopSourceCall (plan.mask + 1) program.source "run" [input] == some expected)
      s!"call-graph loop source differs from its hand-known result: {label} at {input}"
  ensure (loopSourceCall 64 program.source "run" [2 ^ 256] == none)
    s!"call-graph loop method accepted an argument outside uint256: {label}"
  return program.source

/-- Raw opcodes applied to helper results, with the hand-known results of one
application from `SourceAggregateCallGraphMeaning`. Under mask one, an odd input
applies the step once and an even input returns unchanged. -/
private def primitiveSteps : List (String × Wire.Expr × Nat × Nat) :=
  let c := call 1
  [("clz", .unary .wordClz (c (.var 0)), 0, 256),
    ("div", .binary .wordDiv (c (.var 0)) (c (word 2)), 5, 2),
    ("mod", .binary .wordMod (c (.var 0)) (c (word 0)), maximum, 0),
    ("shl", .binary .wordShl (c (word 1)) (c (.var 0)), 255, high),
    ("shr", .binary .wordShr (c (word maximum)) (c (.var 0)), 256, 0),
    ("sar", .binary .wordSar (c (word high)) (c (.var 0)), maximum, maximum),
    ("sdiv", .binary .wordSdiv (c (.var 0)) (c (word maximum)), high, high),
    ("smod", .binary .wordSmod (c (.var 0)) (c (word 2)), maximum - 6, maximum),
    ("sgt", .ifE (.binary .wordSgt (c (.var 0)) (c (word 0))) (word 1) (word 0), high - 1, 1),
    ("byte", .binary .wordByte (c (.var 0)) (c (word 0x1234)), 31, 0x34),
    ("pow", .binary .wordPow (c (word maximum)) (c (.var 0)), maximum, maximum),
    ("signextend", .binary .wordSignExtend (c (word 0)) (c (.var 0)), 0x80, maximum - 0x7f),
    ("addmod", .ternary .wordAddMod (c (.var 0)) (c (word 1)) (c (word maximum)), maximum, 1),
    ("mulmod", .ternary .wordMulMod (c (.var 0)) (c (word 2)) (c (word maximum)), high, 1)]

/-- Plans from the `runtime-call-graph-loops` generator, which together use
every generated mask. -/
private def checkGenerated : IO Nat := do
  let mut count := 0
  let mut masks : List Nat := []
  for budget in [128, 256, 512] do
    for seed in List.range 8 do
      match CallGraphLoop.generate {seed := Seed.ofNat seed, maxProgramNodes := budget} with
      | .error error => throw (IO.userError
          s!"call-graph loop generator failed at seed {seed}: {reprStr error}")
      | .ok generated =>
          let _ ← checkPlan s!"generated budget {budget} seed {seed}" generated.plan
          masks := (masks ++ [generated.plan.mask]).eraseDups
          count := count + 1
  ensure (CallGraphLoop.generatedMasks.all masks.contains)
    "generated call-graph loops missed a mask"
  return count

/-- On loop-free emitted texts, the loop grammar returns the same file and the
loop meaning is `sourceCall` for every fuel. -/
private def checkLoopFree : IO Nat := do
  let mut count := 0
  let some mixed := CheckedWordFunctionDAG.ofParts? Tests.SourceCallGraphEmitter.mixedHelpers
      Tests.SourceCallGraphEmitter.mixedEntry |
    throw (IO.userError "mixed call graph failed its checker")
  let some clz := CheckedWordFunctionDAG.ofParts? [.var 0] (.unary .wordClz (call 1 (.var 0))) |
    throw (IO.userError "clz call graph failed its checker")
  for graph in [mixed, clz] do
    let program ← match CallGraph.emit graph with
      | .ok value => pure value
      | .error error => throw (IO.userError s!"call-graph emission failed: {reprStr error}")
    let some file := parseSource program.source |
      throw (IO.userError "emitted call-graph source is outside the loop-free fragment")
    let some loopFile := parseLoopSource program.source |
      throw (IO.userError "the loop grammar rejected a loop-free text")
    ensure (loopFile.print == program.source && file.toLoop.print == program.source)
      "the loop grammar changed a loop-free file"
    for input in Tests.SourceScalarMeaning.boundaryInputs ++ [2 ^ 256] do
      for fuel in [0, 1, 64] do
        ensure (loopSourceCall fuel program.source "run" [input] ==
            sourceCall program.source "run" [input])
          s!"loop meaning differs from sourceCall on a loop-free text at {input}, fuel {fuel}"
    count := count + 1
  return count

/-- Altered loops lose their meaning or change their result. -/
private def checkAlterations (source : String) (plan : CheckedPlan) : IO Unit := do
  let core (input : Nat) : IO Nat := coreWord "altered"
    (plan.instantiate (Word.ofNatModulo input)).toCore
  let replace (old new : String) : IO String := do
    let changed := source.replace old new
    ensure (changed != source) s!"loop fixture has no {old}"
    pure changed
  let doubled ← replace "while (sc_limit > sc_counter) {" "while ((sc_limit > sc_counter)) {"
  ensure (parseLoopSource doubled).isNone "a loop condition in two parentheses was accepted"
  let endless ← replace "            sc_counter = (sc_counter + 1);\n" ""
  ensure ((parseLoopSource endless).isSome &&
      loopSourceCall 1000 endless "run" [0] == some (← core 0) &&
      loopSourceCall 1000 endless "run" [7] == none)
    "a loop without its counter step received a meaning"
  let shadowed ← replace "            sc_acc = sc_step(sc_acc);"
    "            let sc_acc: word = sc_step(sc_acc);"
  ensure (loopSourceCall 64 shadowed "run" [7] == some 7 && (← core 7) != 7)
    "a loop body declaration outlived its iteration"
  let reversed ← replace "while (sc_limit > sc_counter) {" "while (sc_counter > sc_limit) {"
  ensure (loopSourceCall 64 reversed "run" [7] == some 7)
    "a reversed loop condition still iterated"
  let wordCondition ← replace "while (sc_limit > sc_counter) {"
    "while (sc_limit + sc_counter) {"
  ensure ((parseLoopSource wordCondition).isSome &&
      loopSourceCall 64 wordCondition "run" [0] == none)
    "a loop condition of type word received a meaning"
  let undeclared ← replace "            sc_acc = sc_step(sc_acc);"
    "            sc_next = sc_step(sc_acc);"
  ensure ((parseLoopSource undeclared).isSome &&
      loopSourceCall 64 undeclared "run" [7] == none)
    "a loop assignment to an undeclared name received a meaning"
  let stride ← replace "sc_counter = (sc_counter + 1);" "sc_counter = (sc_counter + 2);"
  ensure (loopSourceCall 64 stride "run" [7] != some (← core 7))
    "a loop counting by two still agreed with Core"

def testSourceCallGraphLoopMeaning : IO Unit := do
  let doubled ← checkedPlan "doubled" [.binary .wordAdd (.var 0) (word 1)]
    (call 1 (.binary .wordMul (.var 0) (word 2))) 7
  -- 2x + 1 applied input & 7 times; the maximum Word is a fixed point.
  let doubledSource ← checkPlan "doubled" doubled
    [(0, 0), (1, 3), (3, 31), (7, 1023), (maximum, maximum), (high, high)]
    (some fun input => iterate (fun value => wrap (2 * value + 1)) (input &&& 7) input)
  -- ((2x) >> 4) applied input & 3 times.
  let shifted ← checkedPlan "shifted" [.binary .wordShl (.var 0) (word 1)]
    (.binary .wordShr (call 1 (.var 0)) (word 4)) 3
  let _ ← checkPlan "shifted" shifted [(0xF003, 120), (257, 32)]
    (some fun input => iterate (fun value => wrap (2 * value) / 16) (input &&& 3) input)
  for mask in [0, 1, 3, 7] do
    let identity ← checkedPlan s!"identity mask {mask}" [.var 0] (call 1 (.var 0)) mask
    let _ ← checkPlan s!"identity mask {mask}" identity (formula := some fun input => input)
  for mask in [1, 7] do
    let mixed ← checkedPlan s!"mixed mask {mask}" Tests.SourceCallGraphEmitter.mixedHelpers
      Tests.SourceCallGraphEmitter.mixedEntry mask
    let known := if mask == 1 then [(0, 0), (1, 6), (maximum, 1), (high, high)] else []
    let _ ← checkPlan s!"mixed mask {mask}" mixed known
  for (label, body, input, expected) in primitiveSteps do
    let plan ← checkedPlan label [.var 0] body 1
    let _ ← checkPlan label plan [(input, if input % 2 == 1 then expected else input)]
  let generated ← checkGenerated
  let loopFree ← checkLoopFree
  checkAlterations doubledSource doubled
  IO.println (s!"call-graph loop source meaning: 2 closed-form plans, 4 identity masks, " ++
    s!"2 mixed plans, {primitiveSteps.length} raw primitive steps and {generated} generated " ++
    s!"plans agree with Core at their exact fuel; {loopFree} loop-free texts keep sourceCall")

end Tests.SourceCallGraphLoopMeaning
end

section
-- leanmerge: from Solcore.Test.SourceGenericMeaning
/-! Executable checks of the generic source meaning on actual generic emitter
output. Each emitted text is lexed, parsed with the generic grammar and run
under the generic source semantics, then compared with the original Core
reference on the Core machine. `Generic.emit_source_meaning` covers every
successful emission; these checks exercise the same definitions on real texts.
They also observe the final Core store, which the theorem leaves existential:
it holds the cells that the two step calls allocated. Loop-free texts keep
their `sourceCall` meaning, and altered selectors lose or change their
meaning. -/
set_option autoImplicit false

namespace Tests.SourceGenericMeaning

open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.ScalarMeaning
open Solcore.Synthesis.Core.Generic (CheckedPlan Variant)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- The Word that Core returns and the number of cells in its final store,
each of which must be a Word. -/
private def coreRun (label : String) (program : Program) : IO (Nat × Nat) :=
  match program.runStateful 100000 with
  | .done (.word word) store => do
      ensure (store.all fun | .word _ => true | _ => false)
        s!"generic step allocated a cell that is not a Word: {label}"
      pure (word.val, store.length)
  | _ => throw (IO.userError s!"Core reference did not return a Word: {label}")

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def call (index : Nat) (argument : Wire.Expr) : Wire.Expr := .apply (.var index) argument
private def entry : Wire.Expr := call 1 (.var 0)
private def maximum : Nat := 2 ^ 256 - 1
private def high : Nat := 2 ^ 255

private def checkedPlan (label : String) (helpers : List Wire.Expr) (body : Wire.Expr)
    (variant : Variant) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? helpers body |
    throw (IO.userError s!"generic step failed the aggregate DAG checker: {label}")
  let some plan := CheckedPlan.ofParts? graph variant |
    throw (IO.userError s!"generic plan failed its checker: {label}")
  pure plan

private def emitted (label : String) (plan : CheckedPlan) : IO EmittedProgram :=
  match Generic.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"generic emission failed: {label}: {reprStr error}")

/-- The emitted text parses with the generic grammar to a file whose printing is
that text, with the selector, one function per helper and `sc_step`, and the
aliases exactly when a step body uses one. The loop-free grammar rejects it. -/
private def checkReprint (label : String) (plan : CheckedPlan) (source : String) : IO Unit := do
  let some file := parseGenericSource source |
    throw (IO.userError s!"emitted generic source is outside the fragment: {label}")
  ensure (file.print == source) s!"parsed generic source does not print back: {label}"
  ensure (file.opcodeAliases == aggregateAliases (plan.step.helpers ++ [plan.step.entry]) &&
      (file.generics.map (·.name)) == ["sc_select"] &&
      file.functions.length == plan.step.helpers.length + 1 &&
      (file.functions.getLast?.map (·.name)) == some "sc_step" &&
      file.contract == Generic.contractName)
    s!"generic file has other aliases, functions or contract: {label}"
  ensure (parseSource source).isNone s!"the loop-free grammar accepted a generic text: {label}"

/-- Every boundary input and every input with a hand-known result agrees with
Core, and the final Core store has the expected number of cells. Returns the
emitted text. -/
private def checkPlan (label : String) (plan : CheckedPlan) (known : List (Nat × Nat) := [])
    (cells : Option Nat := none) : IO String := do
  let program ← emitted label plan
  checkReprint label plan program.source
  for input in known.map Prod.fst ++ Tests.SourceScalarMeaning.boundaryInputs do
    let (expected, stored) ← coreRun label (plan.instantiate (Word.ofNatModulo input)).toCore
    ensure (genericSourceCall program.source "run" [input] == some expected)
      s!"generic source meaning differs from Core: {label} at {input}"
    ensure (sourceCall program.source "run" [input] == none)
      s!"the loop-free meaning gave a generic text a result: {label} at {input}"
    if let some count := cells then
      ensure (stored == count) s!"generic Core store has another number of cells: {label}"
  for (input, expected) in known do
    ensure (genericSourceCall program.source "run" [input] == some expected)
      s!"generic source differs from its hand-known result: {label} at {input}"
  ensure (genericSourceCall program.source "run" [2 ^ 256] == none)
    s!"generic method accepted an argument outside uint256: {label}"
  return program.source

/-- The regression steps of `SourceGenericEmitter` at each variant, with their
hand-known results at the inputs 0, 1, the maximum Word and `2^255`. The
identity step allocates one cell per call, so its store ends with two. -/
private def identityWithCell : Wire.Expr := .letE (.newCell .word (.var 0)) (.loadCell (.var 0))

private def identityExpected : Variant → List Nat
  | .word => [1, 1, maximum, high + 1]
  | .pair => [2, 2, maximum - 1, 2]
  | .sum => [2, 1, maximum, high + 2]

private def incrementExpected : Variant → List Nat
  | .word => [2, 2, 0, high + 2]
  | .pair => [3, 3, maximum, 3]
  | .sum => [3, 2, 0, high + 3]

private def regressionChecks : IO String := do
  let inputs := [0, 1, maximum, high]
  let mut identitySource := ""
  for variant in Variant.all do
    let identity ← checkedPlan s!"identity {variant.name}" [identityWithCell] entry variant
    let source ← checkPlan s!"identity {variant.name}" identity
      (inputs.zip (identityExpected variant)) (some 2)
    if variant == .word then identitySource := source
    let increment ← checkedPlan s!"increment {variant.name}"
      [.binary .wordAdd (.var 0) (word 2)] (.binary .wordSub entry (word 1)) variant
    let _ ← checkPlan s!"increment {variant.name}" increment
      (inputs.zip (incrementExpected variant)) (some 0)
  let constant ← checkedPlan "constant" [word 42] entry .word
  let _ ← checkPlan "constant" constant (inputs.map fun input => (input, 42)) (some 0)
  return identitySource

/-- Raw opcodes applied to a helper result as the step, at each variant. -/
private def primitiveSteps : List (String × Wire.Expr) :=
  let c := call 1
  [("clz", .unary .wordClz (c (.var 0))),
    ("div", .binary .wordDiv (c (.var 0)) (c (word 2))),
    ("mod", .binary .wordMod (c (.var 0)) (c (word 0))),
    ("shl", .binary .wordShl (c (word 1)) (c (.var 0))),
    ("shr", .binary .wordShr (c (word maximum)) (c (.var 0))),
    ("sar", .binary .wordSar (c (word high)) (c (.var 0))),
    ("sdiv", .binary .wordSdiv (c (.var 0)) (c (word maximum))),
    ("smod", .binary .wordSmod (c (.var 0)) (c (word 2))),
    ("sgt", .ifE (.binary .wordSgt (c (.var 0)) (c (word 0))) (word 1) (word 0)),
    ("byte", .binary .wordByte (c (.var 0)) (c (word 0x1234))),
    ("pow", .binary .wordPow (c (word maximum)) (c (.var 0))),
    ("signextend", .binary .wordSignExtend (c (word 0)) (c (.var 0))),
    ("addmod", .ternary .wordAddMod (c (.var 0)) (c (word 1)) (c (word maximum))),
    ("mulmod", .ternary .wordMulMod (c (.var 0)) (c (word 2)) (c (word maximum)))]

/-- Plans from the `runtime-generics` generator at two budgets, which together
use every variant. Seeds the generator rejects are skipped. -/
private def checkGenerated : IO Nat := do
  let mut count := 0
  let mut variants : List Variant := []
  for nodes in [256, 512] do
    for seed in List.range 12 do
      match Generic.generatedPlan (Seed.ofNat seed) nodes with
      | .error _ => pure ()
      | .ok (plan, _) =>
          let _ ← checkPlan s!"generated budget {nodes} seed {seed}" plan
          variants := (variants ++ [plan.variant]).eraseDups
          count := count + 1
  ensure (count ≥ 16) s!"the generic generator produced only {count} plans"
  ensure (Variant.all.all variants.contains) "generated generic plans missed a variant"
  return count

/-- Loop-free aggregate texts keep their `sourceCall` meaning when read as
generic programs. -/
private def checkLoopFree : IO Nat := do
  let mut count := 0
  for (helpers, body) in [([identityWithCell], entry),
      ([.binary .wordAdd (.var 0) (word 1)],
        .caseE (.inRight .word (call 1 (.var 0))) (word 0) (.var 0))] do
    let some graph := Aggregates.CheckedDAG.ofParts? helpers body |
      throw (IO.userError "loop-free aggregate fixture failed its checker")
    let program ← match Aggregate.emit graph with
      | .ok value => pure value
      | .error error => throw (IO.userError s!"aggregate emission failed: {reprStr error}")
    let some file := parseSource program.source |
      throw (IO.userError "emitted aggregate source is outside the loop-free fragment")
    ensure (file.toGeneric.print == program.source &&
        (parseGenericSource program.source).isSome)
      "the generic grammar changed a loop-free aggregate file"
    for input in Tests.SourceScalarMeaning.boundaryInputs ++ [2 ^ 256] do
      ensure (genericSourceCall program.source "run" [input] ==
          sourceCall program.source "run" [input])
        s!"generic meaning differs from sourceCall on a loop-free text at {input}"
    count := count + 1
  return count

/-- Altered selectors lose their meaning or change their result. -/
private def checkAlterations (source : String) : IO Unit := do
  let replace (old new : String) : IO String := do
    let changed := source.replace old new
    ensure (changed != source) s!"generic fixture has no {old}"
    pure changed
  let expected := genericSourceCall source "run" [1]
  let swapped ← replace "        return left;" "        return right;"
  ensure ((parseGenericSource swapped).isSome &&
      genericSourceCall swapped "run" [1] != expected)
    "a guard returning the other candidate kept its result"
  let unguarded ← replace "    if (flag) {\n        return left;\n    }\n" ""
  ensure ((parseGenericSource unguarded).isSome &&
      genericSourceCall unguarded "run" [1] != expected)
    "a selector without its guard kept its result"
  let wordFlag ← replace "flag: bool, left: a" "flag: word, left: a"
  ensure ((parseGenericSource wordFlag).isSome && genericSourceCall wordFlag "run" [1] == none)
    "a Boolean argument was admitted for a word parameter"
  let wordGuard ← replace "    if (flag) {" "    if (left) {"
  ensure ((parseGenericSource wordGuard).isSome && genericSourceCall wordGuard "run" [1] == none)
    "a guard on a word received a meaning"
  let twoOperators ← replace "sc_input + 1;" "sc_input + 1 + 1;"
  ensure (parseGenericSource twoOperators).isNone
    "two infix operations without parentheses were accepted"
  let stride ← replace "sc_input + 1;" "sc_input + 2;"
  ensure (genericSourceCall stride "run" [0] != genericSourceCall source "run" [0])
    "the right candidate ignored its input"

def testSourceGenericMeaning : IO Unit := do
  let identitySource ← regressionChecks
  let mut primitives := 0
  for (label, body) in primitiveSteps do
    for variant in Variant.all do
      let _ ← checkPlan s!"{label} {variant.name}" (← checkedPlan label [.var 0] body variant)
      primitives := primitives + 1
  let generated ← checkGenerated
  let loopFree ← checkLoopFree
  checkAlterations identitySource
  IO.println (s!"generic source meaning: 7 regression plans, {primitives} raw primitive " ++
    s!"plans and {generated} generated plans agree with Core; {loopFree} loop-free texts " ++
    "keep sourceCall")

end Tests.SourceGenericMeaning
end

section
-- leanmerge: from Solcore.Test.SourceKeyedMeaning
/-! Executable checks of the keyed source meaning on actual keyed-storage
emitter output. Each emitted text is lexed, parsed with the keyed grammar and
called under the keyed source semantics with a key and an input, one
transaction at a time, from the storage of the account that the committed
world holds. Each call is compared with the original Core contract's top-level
transaction: a returned call with the returned ABI bytes and the committed
slots, a reverted call with the reverted bytes and an unchanged account
storage. Histories include the keys zero and `2^256 - 1`, whose writes alias the
counter slot. `KeyedStorage.emit_source_meaning` covers every successful
emission and every installed account; these checks exercise the same
definitions on real texts and histories. Altered texts lose or change their
meaning. -/
set_option autoImplicit false

namespace Tests.SourceKeyedMeaning

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.ScalarMeaning
open Solcore.Synthesis.Core.KeyedStorage (CheckedPlan)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def call (index : Nat) (argument : Wire.Expr) : Wire.Expr := .apply (.var index) argument
private def entry : Wire.Expr := call 1 (.var 0)
private def maximum : Nat := 2 ^ 256 - 1
private def high : Nat := 2 ^ 255

private def checkedPlan (label : String) (helpers : List Wire.Expr) (body : Wire.Expr) :
    IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers body |
    throw (IO.userError s!"keyed step failed the aggregate DAG checker: {label}")
  let some plan := CheckedPlan.ofParts? step |
    throw (IO.userError s!"keyed plan failed the host checker: {label}")
  pure plan

private def emitted (label : String) (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.KeyedStorage.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"keyed emission failed: {label}: {reprStr error}")

/-- The emitted text parses with the keyed grammar to a file whose printing is
that text, with one function per helper and `sc_step`, and the aliases exactly
when a step body uses one. The loop-free, storage and rollback grammars reject
it. -/
private def checkReprint (label : String) (plan : CheckedPlan) (source : String) : IO Unit := do
  let some file := parseKeyedSource source |
    throw (IO.userError s!"emitted keyed source is outside the fragment: {label}")
  ensure (file.print == source) s!"parsed keyed source does not print back: {label}"
  ensure (file.opcodeAliases == aggregateAliases (plan.step.helpers ++ [plan.step.entry]) &&
      file.functions.length == plan.step.helpers.length + 1 &&
      (file.functions.getLast?.map (·.name)) == some "sc_step" &&
      file.contract == Solcore.Synthesis.Source.KeyedStorage.contractName)
    s!"keyed file has other aliases, functions or contract: {label}"
  ensure ((parseSource source).isNone && (parseStorageSource source).isNone &&
      (parseRollbackSource source).isNone)
    s!"the loop-free, storage or rollback grammar accepted a keyed text: {label}"

private def target : Address := ⟨100, by decide⟩
private def caller : Address := ⟨200, by decide⟩

/-- Fixed slots compared after each transaction, besides the key and its
successor. -/
private def fixedSlots : List Nat := [0, 1, 2, 5, 6, high, high + 1, maximum - 1, maximum]

/-- Two nonempty initial storages; the second fills the slots around zero and
the maximum. -/
private def initialStorages : List (List (Nat × Nat)) :=
  [[], [(0, 5), (1, 9), (5, 7), (high, 3)], [(0, maximum), (1, maximum), (maximum, 4)]]

/-- The source storage written in the keyed order, for the recurrence. -/
private def write (storage : Nat → Nat) (slot value : Nat) : Nat → Nat :=
  fun other => if other = slot then value else storage other

/-- Runs one history of `(key, input)` rows from an account holding `initial`.
Before each transaction the source storage is read from the account that the
committed world holds; the source call must settle as the Core transaction.
When `step` is given, the outcome's word and the written slots must also follow
the keyed recurrence. When `golden` is given, the outcomes must be those
hand-known words. Returns the numbers of returned and reverted transactions. -/
private def checkHistory (label : String) (plan : CheckedPlan) (source : String)
    (initial : List (Nat × Nat)) (rows : List (Nat × Nat))
    (step : Option (Word → Word) := none) (golden : List (Bool × Nat) := []) :
    IO (Nat × Nat) := do
  let registry : CheckedContractRegistry :=
    ⟨fun address => if address == target then some plan.contract else none⟩
  let installedAccount := initial.foldl (fun account (slot, value) =>
    account.storageWrite (Word.ofNatModulo slot) (Word.ofNatModulo value))
    (Account.empty.withCode plan.code)
  let mut world := WorldState.empty.putAccount target installedAccount
  let mut returned := 0
  let mut reverted := 0
  let mut index := 0
  for (key, input) in rows do
    let calldata := Solcore.Synthesis.Stateful.KeyedStorageExecution.inputData
      (Word.ofNatModulo key) (Word.ofNatModulo input)
    ensure (calldata.wordBE? (Word.ofNatModulo 4) == some (Word.ofNatModulo key) &&
        calldata.wordBE? (Word.ofNatModulo 36) == some (Word.ofNatModulo input))
      s!"canonical calldata does not carry its key and input words: {label}"
    let some ⟨contract, installed⟩ := registry.resolve? world target |
      throw (IO.userError s!"committed world no longer resolves the contract: {label}")
    let storage := accountStorage installed.account
    let invocation : TopLevelInvocation :=
      { target, caller, callValue := Word.zero, inputData := calldata }
    let some outcome := keyedSourceCall source storage "run" [key, input] |
      throw (IO.userError s!"keyed source call has no meaning: {label} at {key}, {input}")
    match TopLevelExecution.run contract invocation installed 0 with
    | .outOfFuel _ _ _ _ _ _ => pure ()
    | .completed _ => throw (IO.userError s!"zero fuel completed a keyed transaction: {label}")
    let result ← match TopLevelExecution.run contract invocation installed 100000 with
      | .outOfFuel _ _ _ _ _ _ =>
          throw (IO.userError s!"keyed transaction exhausted its fuel: {label}")
      | .completed result => pure result
    let some account := result.finalWorld.account? target |
      throw (IO.userError s!"committed storage account disappeared: {label}")
    let successor := (key + 1) % 2 ^ 256
    let compared := key :: successor :: fixedSlots
    let expected : Option (Nat × (Nat → Nat)) := step.map fun stepResult =>
      let old := storage key
      let count := storage 0
      let computed := (stepResult ((Word.ofNatModulo input).add (Word.ofNatModulo old))).val
      let written := write (write (write storage key computed) successor old) 0
        ((count + 1) % 2 ^ 256)
      ((written key + written successor + written 0) % 2 ^ 256, written)
    match outcome with
    | .returned value storage' =>
        ensure (input % 2 == 0) s!"an odd input returned: {label} at {key}, {input}"
        ensure (value < 2 ^ 256 &&
            result.outcome == .returned (encodeWordBytesBE (Word.ofNatModulo value)))
          s!"returned word differs from the Core transaction: {label} at {key}, {input}"
        ensure (compared.all fun slot =>
            (account.storageRead (Word.ofNatModulo slot)).val == storage' slot)
          s!"committed slots differ from the source storage: {label} at {key}, {input}"
        if let some (sum, written) := expected then
          ensure (value == sum && compared.all fun slot => storage' slot == written slot)
            s!"returned results differ from the keyed recurrence: {label} at {key}, {input}"
        if let some (odd, payload) := golden[index]? then
          ensure (!odd && value == payload) s!"keyed golden row changed: {label} row {index}"
        returned := returned + 1
    | .reverted data =>
        ensure (input % 2 == 1) s!"an even input reverted: {label} at {key}, {input}"
        ensure (data < 2 ^ 256 &&
            result.outcome == .reverted (encodeWordBytesBE (Word.ofNatModulo data)))
          s!"reverted word differs from the Core transaction: {label} at {key}, {input}"
        ensure (compared.all fun slot =>
            (account.storageRead (Word.ofNatModulo slot)).val == storage slot)
          s!"a reverted transaction changed the committed slots: {label} at {key}, {input}"
        if let some (sum, _) := expected then
          ensure (data == sum) s!"reverted word differs from the keyed recurrence: {label}"
        if let some (odd, payload) := golden[index]? then
          ensure (odd && data == payload) s!"keyed golden row changed: {label} row {index}"
        reverted := reverted + 1
    world := result.finalWorld
    index := index + 1
  let some ⟨_, installed⟩ := registry.resolve? world target |
    throw (IO.userError s!"committed world no longer resolves the contract: {label}")
  ensure (keyedSourceCall source (accountStorage installed.account) "run" [2 ^ 256, 0]).isNone
    s!"keyed method accepted a key outside uint256: {label}"
  ensure (keyedSourceCall source (accountStorage installed.account) "run" [0]).isNone
    s!"keyed method accepted a missing argument: {label}"
  return (returned, reverted)

/-- Every history of a plan, from each initial storage. -/
private def checkPlan (label : String) (plan : CheckedPlan) (rows : List (Nat × Nat))
    (step : Option (Word → Word) := none) : IO (String × Nat × Nat) := do
  let program ← emitted label plan
  checkReprint label plan program.source
  let mut returned := 0
  let mut reverted := 0
  for initial in initialStorages do
    let (more, fewer) ← checkHistory label plan program.source initial rows step
    returned := returned + more
    reverted := reverted + fewer
  return (program.source, returned, reverted)

/-- Keys around zero, the maximum and the middle, with inputs of both
parities. -/
private def regressionRows : List (Nat × Nat) :=
  [(5, 2), (0, 4), (maximum, 3), (maximum - 1, 0), (maximum, 2), (maximum - 1, 6),
    (high, 7), (high, 2), (1, 1), (0, 0), (2, maximum)]

private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)

private def privateStep : Wire.Expr :=
  .letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))

/-- The golden histories of `SourceKeyedStorageEmitter`, from empty storage. -/
private def goldenChecks : IO Unit := do
  let identity ← checkedPlan "identity" [.var 0] entry
  let identitySource := (← emitted "identity" identity).source
  let _ ← checkHistory "golden aliasing" identity identitySource []
    [(5, 2), (0, 4), (maximum, 3)] (some id) [(false, 3), (false, 5), (true, 9)]
  let _ ← checkHistory "golden wrapping" identity identitySource []
    [(maximum - 1, 0), (maximum, 2), (maximum - 1, 6)] (some id)
    [(false, 1), (false, 6), (false, 9)]
  let constant ← checkedPlan "constant" [.var 0] (word 0)
  let _ ← checkHistory "golden deletion" constant (← emitted "constant" constant).source []
    [(1, 0), (0, 0), (1, 1)] (some fun _ => Word.zero) [(false, 1), (false, 5), (true, 4)]
  let cell ← checkedPlan "private cell" [privateStep] (.binary .wordSub entry (word 1))
  let _ ← checkHistory "golden cell" cell (← emitted "private cell" cell).source []
    [(high, 7), (high, 2)] (some fun input => input.add (Word.ofNatModulo 1))
    [(true, 9), (false, 4)]

/-- The regression plans of `SourceKeyedStorageEmitter`, with their step
functions. Returns the identity plan's text and the transaction counts. -/
private def regressionChecks : IO (String × Nat × Nat) := do
  let plus (amount : Nat) (input : Word) : Word := input.add (Word.ofNatModulo amount)
  let mut returned := 0
  let mut reverted := 0
  let (identitySource, more, fewer) ← checkPlan "identity"
    (← checkedPlan "identity" [.var 0] entry) regressionRows (some id)
  returned := returned + more
  reverted := reverted + fewer
  for (label, helpers, body, step) in [
      ("increment", [increment], entry, plus 1),
      ("private cell", [privateStep], .binary .wordSub entry (word 1), plus 1),
      ("constant", [.var 0], word 0, fun _ => Word.zero),
      ("division", [.binary .wordDiv (.var 0) (word 1)], entry, id)] do
    let (_, more, fewer) ← checkPlan label (← checkedPlan label helpers body) regressionRows
      (some step)
    returned := returned + more
    reverted := reverted + fewer
  return (identitySource, returned, reverted)

/-- Raw opcodes applied to a helper result as the step. -/
private def primitiveSteps : List (String × Wire.Expr) :=
  let c := call 1
  [("clz", .unary .wordClz (c (.var 0))),
    ("div", .binary .wordDiv (c (.var 0)) (c (word 2))),
    ("mod", .binary .wordMod (c (.var 0)) (c (word 0))),
    ("shl", .binary .wordShl (c (word 1)) (c (.var 0))),
    ("shr", .binary .wordShr (c (word maximum)) (c (.var 0))),
    ("sar", .binary .wordSar (c (word high)) (c (.var 0))),
    ("sdiv", .binary .wordSdiv (c (.var 0)) (c (word maximum))),
    ("smod", .binary .wordSmod (c (.var 0)) (c (word 2))),
    ("sgt", .ifE (.binary .wordSgt (c (.var 0)) (c (word 0))) (word 1) (word 0)),
    ("byte", .binary .wordByte (c (.var 0)) (c (word 0x1234))),
    ("pow", .binary .wordPow (c (word maximum)) (c (.var 0))),
    ("signextend", .binary .wordSignExtend (c (word 0)) (c (.var 0))),
    ("addmod", .ternary .wordAddMod (c (.var 0)) (c (word 1)) (c (word maximum))),
    ("mulmod", .ternary .wordMulMod (c (.var 0)) (c (word 2)) (c (word maximum)))]

/-- Generated keyed scenarios at two budgets, with their generated rows and
two more. Seeds the generator rejects are skipped. -/
private def checkGenerated : IO (Nat × Nat × Nat) := do
  let mut plans := 0
  let mut returned := 0
  let mut reverted := 0
  for nodes in [256, 512] do
    for seed in List.range 12 do
      match Solcore.Synthesis.Source.KeyedStorage.generatedScenario (Seed.ofNat seed) nodes with
      | .error _ => pure ()
      | .ok (scenario, _) =>
          let rows := scenario.transactions.map fun transaction =>
            (transaction.key.val, transaction.input.val)
          let (_, more, fewer) ← checkPlan s!"generated budget {nodes} seed {seed}"
            scenario.plan (rows ++ [(0, 1), (maximum, 2)])
          plans := plans + 1
          returned := returned + more
          reverted := reverted + fewer
  ensure (plans ≥ 16) s!"the keyed generator produced only {plans} plans"
  return (plans, returned, reverted)

/-- The outcome of one call from a nonempty storage. -/
private def observed (source : String) (key input : Nat) : Option String :=
  let storage : Storage := fun slot =>
    if slot = 0 then 5 else if slot = 1 then 9 else if slot = 2 then 11 else 7
  (keyedSourceCall source storage "run" [key, input]).map fun
    | .returned value storage' =>
        s!"returned {value} {storage' 0} {storage' 1} {storage' 2} {storage' 3}"
    | .reverted data => s!"reverted {data}"

/-- Altered keyed programs lose their meaning or change their outcome. -/
private def checkAlterations (source : String) : IO Unit := do
  let replace (old new : String) : IO String := do
    let changed := source.replace old new
    ensure (changed != source) s!"keyed fixture has no {old}"
    pure changed
  let atOne := observed source 1 2
  let atZero := observed source 0 2
  ensure (atOne.isSome && atZero.isSome) "the keyed fixture has no meaning"
  let farther ← replace "sstore(sc_key + 1, sc_old);" "sstore(sc_key + 2, sc_old);"
  ensure ((parseKeyedSource farther).isSome && observed farther 1 2 != atOne)
    "a write two slots on kept the result"
  let reordered ← replace
    "        sstore(sc_key, sc_computed);\n        sstore(sc_key + 1, sc_old);\n        sstore(0, sc_count + 1);\n"
    "        sstore(0, sc_count + 1);\n        sstore(sc_key, sc_computed);\n        sstore(sc_key + 1, sc_old);\n"
  ensure ((parseKeyedSource reordered).isSome && observed reordered 0 2 != atZero &&
      observed reordered 1 2 == atOne)
    "reordered writes kept the aliased result or changed an unaliased one"
  let swappedKey ← replace "let sc_key: word = Typedef.rep(key);"
    "let sc_key: word = Typedef.rep(input);"
  ensure ((parseKeyedSource swappedKey).isSome && observed swappedKey 1 2 != atOne)
    "a key read from the input kept the result"
  let nested ← replace "sc_final_key + sc_final_next + sc_final_count;"
    "(sc_final_key + sc_final_next) + sc_final_count;"
  ensure ((parseKeyedSource nested).isSome && observed nested 1 2 == atOne &&
      observed nested 0 2 == atZero)
    "a parenthesized sum changed the result"
  let wrapped ← replace "sload(sc_key + 1);" "sload((sc_key + 1));"
  ensure ((parseKeyedSource wrapped).isSome && observed wrapped 1 2 == atOne)
    "a parenthesized load argument changed the result"
  let fourTerms ← replace "sc_final_key + sc_final_next + sc_final_count;"
    "sc_final_key + sc_final_next + sc_final_count + 0;"
  ensure (parseKeyedSource fourTerms).isNone "a sum of four terms was accepted"
  let mixed ← replace "sc_final_key + sc_final_next + sc_final_count;"
    "sc_final_key + sc_final_next * sc_final_count;"
  ensure (parseKeyedSource mixed).isNone "a mixed chain without parentheses was accepted"

def testSourceKeyedMeaning : IO Unit := do
  goldenChecks
  let (identitySource, regressionReturned, regressionReverted) ← regressionChecks
  let mut primitivesReturned := 0
  let mut primitivesReverted := 0
  for (label, body) in primitiveSteps do
    let (_, more, fewer) ← checkPlan label (← checkedPlan label [.var 0] body)
      [(0, 0), (1, 1), (maximum, high), (high, maximum)]
    primitivesReturned := primitivesReturned + more
    primitivesReverted := primitivesReverted + fewer
  let (generated, generatedReturned, generatedReverted) ← checkGenerated
  checkAlterations identitySource
  IO.println (s!"keyed source meaning: 4 golden histories, 5 regression plans " ++
    s!"({regressionReturned} returned, {regressionReverted} reverted), 14 raw primitive plans " ++
    s!"({primitivesReturned} returned, {primitivesReverted} reverted) and {generated} generated " ++
    s!"plans ({generatedReturned} returned, {generatedReverted} reverted) settle as Core from " ++
    "3 initial storages")

end Tests.SourceKeyedMeaning
end

section
-- leanmerge: from Solcore.Test.SourceLogMeaning
/-! Executable checks of the log source meaning on actual event-log emitter
output. Each emitted text is lexed, parsed with the log grammar and called
under the log source semantics with flags and an input, one transaction at a
time, from the storage of the account that the committed world holds and from a
dispatcher memory whose free-memory pointer word at 64 holds a buffer pointer.
Each call is compared with the original Core contract's top-level transaction:
a returned call with the returned ABI bytes, the committed slots and the
committed journal, which must be the framing of the source logs and decode to
them; a reverted call with the reverted bytes, an unchanged account storage
and an empty committed journal. Buffer pointers include 64, whose buffer
overlaps the pointer word, and the last pointer whose buffer lies below
`2^256`. `EventLog.emit_source_meaning` covers every successful emission,
every installed account and every such memory; these checks exercise the same
definitions on real texts and histories. Altered texts lose or change their
meaning. -/
set_option autoImplicit false

namespace Tests.SourceLogMeaning

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.ScalarMeaning
open Solcore.Synthesis.Core.EventLog (CheckedPlan Site)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def call (index : Nat) (argument : Wire.Expr) : Wire.Expr := .apply (.var index) argument
private def entry : Wire.Expr := call 1 (.var 0)
private def maximum : Nat := 2 ^ 256 - 1
private def high : Nat := 2 ^ 255

private def checkedPlan (label : String) (helpers : List Wire.Expr) (body : Wire.Expr)
    (sites : List Site) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers body |
    throw (IO.userError s!"log step failed the aggregate DAG checker: {label}")
  let some plan := CheckedPlan.ofParts? step sites |
    throw (IO.userError s!"log plan failed the host checker: {label}")
  pure plan

private def emitted (label : String) (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.EventLog.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"log emission failed: {label}: {reprStr error}")

/-- The emitted text parses with the log grammar to a file whose printing is
that text, with the wrappers of the used topic counts before the raw aliases,
one function per helper and `sc_step`. The loop-free, storage, rollback and
keyed grammars reject it. -/
private def checkReprint (label : String) (plan : CheckedPlan) (source : String) : IO Unit := do
  let some file := parseLogSource source |
    throw (IO.userError s!"emitted log source is outside the fragment: {label}")
  ensure (file.print == source) s!"parsed log source does not print back: {label}"
  ensure (file.opcodeAliases ==
        logAliases plan.sites ++ aggregateAliases (plan.step.helpers ++ [plan.step.entry]) &&
      file.functions.length == plan.step.helpers.length + 1 &&
      (file.functions.getLast?.map (·.name)) == some "sc_step" &&
      file.contract == Solcore.Synthesis.Source.EventLog.contractName &&
      file.method.body.length == plan.sites.length + 10)
    s!"log file has other aliases, functions, contract or body: {label}"
  ensure ((parseSource source).isNone && (parseStorageSource source).isNone &&
      (parseRollbackSource source).isNone && (parseKeyedSource source).isNone)
    s!"the loop-free, storage, rollback or keyed grammar accepted a log text: {label}"

private def target : Address := ⟨100, by decide⟩
private def caller : Address := ⟨200, by decide⟩

/-- Slots compared after each transaction. -/
private def comparedSlots : List Nat := [0, 1, 2, 5, high, maximum]

/-- Initial storages; the last fills slot zero with the maximum, so the first
step argument wraps. -/
private def initialStorages : List (List (Nat × Nat)) :=
  [[], [(0, 5), (1, 9), (5, 7)], [(0, maximum), (1, maximum), (maximum, 4)]]

/-- Buffer pointers the dispatcher may leave at 64: the usual 128, one whose
buffer overlaps the pointer word, and the last whose buffer lies below
`2^256`. -/
private def pointers : List Nat := [128, 64, 2 ^ 256 - 64]

/-- A dispatcher memory: only the free-memory pointer word is known. -/
private def dispatcherMemory (pointer : Nat) : Memory :=
  fun offset => if offset = 64 then some pointer else none

/-- The logs and the result the event-log recurrence gives from slot zero. -/
private def recurrence (step : Word → Word) (sites : List Site) (slot0 flags input : Nat) :
    Nat × List SourceLog :=
  let result := step ((Word.ofNatModulo input).add (Word.ofNatModulo slot0))
  let logs := sites.filterMap fun site =>
    if flags / 2 ^ site.guard % 2 = 1 then
      let value := step (result.add (Word.ofNatModulo site.guard))
      some ⟨(List.range site.topics).map fun index => (value.val + index + 1) % 2 ^ 256,
        [value.val, result.val].take site.dataWords⟩
    else none
  (result.val, logs)

/-- Runs one history of `(flags, input)` rows from an account holding
`initial`, with the dispatcher leaving `pointer`. Before each transaction the
source storage is read from the account that the committed world holds; the
source call must settle as the Core transaction with the framing of its logs.
When `step` is given, the outcome must also follow the event-log recurrence.
When `golden` is given, the rows must be those hand-known outcomes. Returns the
numbers of returned and reverted transactions and of committed logs. -/
private def checkHistory (label : String) (plan : CheckedPlan) (source : String)
    (initial : List (Nat × Nat)) (pointer : Nat) (rows : List (Nat × Nat))
    (step : Option (Word → Word) := none)
    (golden : List (Bool × Nat × List (List Nat × List Nat)) := []) :
    IO (Nat × Nat × Nat) := do
  let registry : CheckedContractRegistry :=
    ⟨fun address => if address == target then some plan.contract else none⟩
  let installedAccount := initial.foldl (fun account (slot, value) =>
    account.storageWrite (Word.ofNatModulo slot) (Word.ofNatModulo value))
    (Account.empty.withCode plan.code)
  let mut world := WorldState.empty.putAccount target installedAccount
  let mut returned := 0
  let mut reverted := 0
  let mut committed := 0
  let mut index := 0
  for (flags, input) in rows do
    let calldata := Solcore.Synthesis.Stateful.EventLogExecution.inputData
      (Word.ofNatModulo flags) (Word.ofNatModulo input)
    ensure (calldata.wordBE? (Word.ofNatModulo 4) == some (Word.ofNatModulo flags) &&
        calldata.wordBE? (Word.ofNatModulo 36) == some (Word.ofNatModulo input))
      s!"canonical calldata does not carry its flags and input words: {label}"
    let some ⟨contract, installed⟩ := registry.resolve? world target |
      throw (IO.userError s!"committed world no longer resolves the contract: {label}")
    let storage := accountStorage installed.account
    let invocation : TopLevelInvocation :=
      { target, caller, callValue := Word.zero, inputData := calldata }
    let some outcome := logSourceCall source storage (dispatcherMemory pointer) "run"
        [flags, input] |
      throw (IO.userError s!"log source call has no meaning: {label} at {flags}, {input}")
    match TopLevelExecution.run contract invocation installed 0 with
    | .outOfFuel _ _ _ _ _ _ => pure ()
    | .completed _ => throw (IO.userError s!"zero fuel completed a log transaction: {label}")
    let result ← match TopLevelExecution.run contract invocation installed 100000 with
      | .outOfFuel _ _ _ _ _ _ =>
          throw (IO.userError s!"log transaction exhausted its fuel: {label}")
      | .completed result => pure result
    let some account := result.finalWorld.account? target |
      throw (IO.userError s!"committed storage account disappeared: {label}")
    let expected := step.map fun stepResult =>
      recurrence stepResult plan.sites (storage 0) flags input
    let records := result.committedJournal.logList
    match outcome with
    | .returned value storage' logs =>
        ensure (flags % 2 == 0) s!"odd flags returned: {label} at {flags}, {input}"
        ensure (value < 2 ^ 256 &&
            result.outcome == .returned (encodeWordBytesBE (Word.ofNatModulo value)))
          s!"returned word differs from the Core transaction: {label} at {flags}, {input}"
        ensure (comparedSlots.all fun slot =>
            (account.storageRead (Word.ofNatModulo slot)).val == storage' slot)
          s!"committed slots differ from the source storage: {label} at {flags}, {input}"
        ensure (records == logs.flatMap (logFrame target))
          s!"committed journal is not the framing of the source logs: {label} at {flags}"
        match Solcore.Synthesis.Stateful.EventLogExecution.decodeJournal records with
        | .ok events =>
            ensure (events.map (fun event =>
                (event.emitter, event.topics.map (·.val), event.data.map (·.val))) ==
              logs.map fun log => (target, log.topics, log.data))
              s!"decoded journal differs from the source logs: {label} at {flags}"
        | .error error => throw (IO.userError s!"committed journal did not decode: {error}")
        if let some (sum, expectedLogs) := expected then
          ensure (value == sum && logs == expectedLogs)
            s!"returned results differ from the log recurrence: {label} at {flags}, {input}"
        if let some (odd, payload, shapes) := golden[index]? then
          ensure (!odd && value == payload &&
              logs.map (fun log => (log.topics, log.data)) == shapes)
            s!"log golden row changed: {label} row {index}"
        returned := returned + 1
        committed := committed + logs.length
    | .reverted data =>
        ensure (flags % 2 == 1) s!"even flags reverted: {label} at {flags}, {input}"
        ensure (data < 2 ^ 256 &&
            result.outcome == .reverted (encodeWordBytesBE (Word.ofNatModulo data)))
          s!"reverted word differs from the Core transaction: {label} at {flags}, {input}"
        ensure (comparedSlots.all fun slot =>
            (account.storageRead (Word.ofNatModulo slot)).val == storage slot)
          s!"a reverted transaction changed the committed slots: {label} at {flags}"
        ensure records.isEmpty s!"a reverted transaction committed logs: {label} at {flags}"
        if let some (sum, _) := expected then
          ensure (data == sum) s!"reverted word differs from the log recurrence: {label}"
        if let some (odd, payload, _) := golden[index]? then
          ensure (odd && data == payload) s!"log golden row changed: {label} row {index}"
        reverted := reverted + 1
    world := result.finalWorld
    index := index + 1
  let some ⟨_, installed⟩ := registry.resolve? world target |
    throw (IO.userError s!"committed world no longer resolves the contract: {label}")
  let storage := accountStorage installed.account
  ensure (logSourceCall source storage (dispatcherMemory pointer) "run" [2 ^ 256, 0]).isNone
    s!"log method accepted flags outside uint256: {label}"
  ensure (logSourceCall source storage (fun _ => none) "run" [0, 0]).isNone
    s!"log method ran without a free-memory pointer: {label}"
  return (returned, reverted, committed)

/-- Every history of a plan, from each initial storage and buffer pointer. -/
private def checkPlan (label : String) (plan : CheckedPlan) (rows : List (Nat × Nat))
    (step : Option (Word → Word) := none) : IO (String × Nat × Nat × Nat) := do
  let program ← emitted label plan
  checkReprint label plan program.source
  let mut returned := 0
  let mut reverted := 0
  let mut committed := 0
  for initial in initialStorages do
    for pointer in pointers do
      let (more, fewer, logs) ← checkHistory label plan program.source initial pointer rows step
      returned := returned + more
      reverted := reverted + fewer
      committed := committed + logs
  return (program.source, returned, reverted, committed)

/-- Flags enabling no site, each site, every site and high noise bits, with
both parities and boundary inputs. -/
private def regressionRows : List (Nat × Nat) :=
  [(0, 5), (2, 0), (4, maximum), (8, 1), (14, 7), (15, 2), (14 + high, maximum),
    (7, high), (2, maximum), (8, 3)]

private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)

private def privateStep : Wire.Expr :=
  .letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))

/-- Site layouts covering guards one to three, zero to four topics and zero to
two data Words. -/
private def layouts : List (List Site) :=
  [[⟨1, 2, 1⟩, ⟨3, 0, 2⟩], [⟨1, 0, 0⟩, ⟨2, 1, 1⟩, ⟨3, 4, 2⟩], [⟨2, 3, 2⟩],
    [⟨1, 4, 0⟩, ⟨3, 2, 1⟩], []]

/-- The golden histories of `SourceEventLogEmitter`, from empty storage. -/
private def goldenChecks : IO Unit := do
  let identity ← checkedPlan "identity" [.var 0] entry [⟨1, 2, 1⟩, ⟨3, 0, 2⟩]
  let identitySource := (← emitted "identity" identity).source
  let _ ← checkHistory "golden sites" identity identitySource [] 128
    [(2, 5), (9, 1), (8, 0)] (some id)
    [(false, 5, [([7, 8], [6])]), (true, 6, []), (false, 5, [([], [8, 5])])]
  let incremented ← checkedPlan "increment" [increment] entry [⟨2, 4, 0⟩]
  let _ ← checkHistory "golden wrapping" incremented (← emitted "increment" incremented).source
    [] 128 [(4, maximum), (5, 3), (high + 6, 2)]
    (some fun input => input.add (Word.ofNatModulo 1))
    [(false, 0, [([4, 5, 6, 7], [])]), (true, 4, []), (false, 3, [([7, 8, 9, 10], [])])]
  let bare ← checkedPlan "no site" [.var 0] entry []
  let _ ← checkHistory "golden completion" bare (← emitted "no site" bare).source [] 128
    [(14, 7), (15, 1)] (some id) [(false, 7, []), (true, 8, [])]

/-- The regression steps with their step functions, over every layout. -/
private def regressionChecks : IO (String × Nat × Nat × Nat) := do
  let plus (amount : Nat) (input : Word) : Word := input.add (Word.ofNatModulo amount)
  let mut returned := 0
  let mut reverted := 0
  let mut committed := 0
  let mut fixture := ""
  for sites in layouts do
    for (label, helpers, body, step) in [
        ("identity", [.var 0], entry, fun input : Word => input),
        ("increment", [increment], entry, plus 1),
        ("private cell", [privateStep], .binary .wordSub entry (word 1), plus 1),
        ("constant", [.var 0], word 0, fun _ => Word.zero),
        ("division", [.binary .wordDiv (.var 0) (word 1)], entry, id)] do
      let (source, more, fewer, logs) ← checkPlan s!"{label} {sites.length} sites"
        (← checkedPlan label helpers body sites) regressionRows (some step)
      if label == "identity" && sites.length == 3 then fixture := source
      returned := returned + more
      reverted := reverted + fewer
      committed := committed + logs
  return (fixture, returned, reverted, committed)

/-- Raw opcodes applied to a helper result as the step. -/
private def primitiveSteps : List (String × Wire.Expr) :=
  let c := call 1
  [("clz", .unary .wordClz (c (.var 0))),
    ("div", .binary .wordDiv (c (.var 0)) (c (word 2))),
    ("mod", .binary .wordMod (c (.var 0)) (c (word 0))),
    ("shl", .binary .wordShl (c (word 1)) (c (.var 0))),
    ("shr", .binary .wordShr (c (word maximum)) (c (.var 0))),
    ("sar", .binary .wordSar (c (word high)) (c (.var 0))),
    ("sdiv", .binary .wordSdiv (c (.var 0)) (c (word maximum))),
    ("smod", .binary .wordSmod (c (.var 0)) (c (word 2))),
    ("sgt", .ifE (.binary .wordSgt (c (.var 0)) (c (word 0))) (word 1) (word 0)),
    ("byte", .binary .wordByte (c (.var 0)) (c (word 0x1234))),
    ("pow", .binary .wordPow (c (word maximum)) (c (.var 0))),
    ("signextend", .binary .wordSignExtend (c (word 0)) (c (.var 0))),
    ("addmod", .ternary .wordAddMod (c (.var 0)) (c (word 1)) (c (word maximum))),
    ("mulmod", .ternary .wordMulMod (c (.var 0)) (c (word 2)) (c (word maximum)))]

/-- Generated event-log scenarios at two budgets, with their generated rows and
two more. Seeds the generator rejects are skipped. -/
private def checkGenerated : IO (Nat × Nat × Nat × Nat) := do
  let mut plans := 0
  let mut returned := 0
  let mut reverted := 0
  let mut committed := 0
  for nodes in [256, 512] do
    for seed in List.range 12 do
      match Solcore.Synthesis.Source.EventLog.generatedScenario (Seed.ofNat seed) nodes with
      | .error _ => pure ()
      | .ok (scenario, _) =>
          let rows := scenario.transactions.map fun transaction =>
            (transaction.flags.val, transaction.input.val)
          let (_, more, fewer, logs) ← checkPlan s!"generated budget {nodes} seed {seed}"
            scenario.plan (rows ++ [(14, maximum), (15, 0)])
          plans := plans + 1
          returned := returned + more
          reverted := reverted + fewer
          committed := committed + logs
  ensure (plans ≥ 16) s!"the event-log generator produced only {plans} plans"
  return (plans, returned, reverted, committed)

/-- The outcome of one call from a nonempty storage and the usual buffer. -/
private def observed (source : String) (flags input : Nat) : Option String :=
  let storage : Storage := fun slot => if slot = 0 then 5 else if slot = 1 then 9 else 7
  (logSourceCall source storage (dispatcherMemory 128) "run" [flags, input]).map fun
    | .returned value storage' logs =>
        s!"returned {value} {storage' 0} {storage' 1} " ++
          toString (logs.map fun log => (log.topics, log.data))
    | .reverted data => s!"reverted {data}"

/-- Altered log programs lose their meaning or change their outcome. The
fixture has sites with guards one, two and three, the last with four topics and
two data Words. -/
private def checkAlterations (source : String) : IO Unit := do
  let replace (old new : String) : IO String := do
    let changed := source.replace old new
    ensure (changed != source) s!"log fixture has no {old}"
    pure changed
  let all := observed source 14 2
  ensure all.isSome "the log fixture has no meaning"
  let otherPointer ← replace "mload(64);" "mload(96);"
  ensure ((parseLogSource otherPointer).isSome && observed otherPointer 14 2 == none)
    "a pointer read from unknown memory kept a meaning"
  let farther ← replace "mstore(sc_ptr + 32, sc_result);" "mstore(sc_ptr + 64, sc_result);"
  ensure ((parseLogSource farther).isSome && observed farther 14 2 == none)
    "a second data Word stored past the buffer kept a meaning"
  let unstored ← replace "            mstore(sc_ptr, sc_value3);\n" ""
  ensure ((parseLogSource unstored).isSome && observed unstored 8 2 == none)
    "a log over a Word that no site stored kept a meaning"
  let shorter ← replace "sc_log4(sc_ptr, 64," "sc_log4(sc_ptr, 33,"
  ensure ((parseLogSource shorter).isSome && observed shorter 8 2 == none)
    "a log size that is no multiple of 32 kept a meaning"
  let wrongArity ← replace "sc_log4(sc_ptr, 64, sc_value3 + 1, sc_value3 + 2, sc_value3 + 3, "
    "sc_log4(sc_ptr, 64, sc_value3 + 1, sc_value3 + 2, "
  ensure ((parseLogSource wrongArity).isSome && observed wrongArity 8 2 == none)
    "a logger called with the wrong topic count kept a meaning"
  let reordered ← replace "sc_value3 + 1, sc_value3 + 2" "sc_value3 + 2, sc_value3 + 1"
  ensure ((parseLogSource reordered).isSome && observed reordered 8 2 != observed source 8 2 &&
      observed reordered 2 2 == observed source 2 2)
    "reordered topics kept the log or changed another site"
  let otherGuard ← replace "if ((sc_flags & 8) == 8) {" "if ((sc_flags & 4) == 4) {"
  ensure ((parseLogSource otherGuard).isSome && observed otherGuard 8 2 != observed source 8 2)
    "a site moved to another guard bit kept its outcome"
  let withElse ← replace "sc_value3 + 4);\n        }\n"
    "sc_value3 + 4);\n        } else {\n        }\n"
  ensure (parseLogSource withElse).isNone "a log block followed by else was accepted"

def testSourceLogMeaning : IO Unit := do
  goldenChecks
  let (fixture, regressionReturned, regressionReverted, regressionLogs) ← regressionChecks
  let mut primitivesReturned := 0
  let mut primitivesReverted := 0
  let mut primitivesLogs := 0
  for (label, body) in primitiveSteps do
    let (_, more, fewer, logs) ← checkPlan label
      (← checkedPlan label [.var 0] body [⟨1, 2, 2⟩, ⟨3, 4, 1⟩])
      [(0, 0), (2, 1), (10, maximum), (11, high)]
    primitivesReturned := primitivesReturned + more
    primitivesReverted := primitivesReverted + fewer
    primitivesLogs := primitivesLogs + logs
  let (generated, generatedReturned, generatedReverted, generatedLogs) ← checkGenerated
  checkAlterations fixture
  IO.println (s!"log source meaning: 3 golden histories, 25 regression plans " ++
    s!"({regressionReturned} returned, {regressionReverted} reverted, {regressionLogs} logs), " ++
    s!"14 raw primitive plans ({primitivesReturned} returned, {primitivesReverted} reverted, " ++
    s!"{primitivesLogs} logs) and {generated} generated plans ({generatedReturned} returned, " ++
    s!"{generatedReverted} reverted, {generatedLogs} logs) settle as Core from 3 initial " ++
    "storages and 3 buffer pointers")

end Tests.SourceLogMeaning
end

section
-- leanmerge: from Solcore.Test.SourceLoopMeaning
/-! Executable checks of the loop meaning on actual aggregate loop emitter
output. Each emitted text is lexed, parsed with the loop grammar and run under
the fuel-indexed source semantics, then compared with the original Core
bounded loop on the Core machine. `Loop.emit_source_meaning` covers every
successful emission; these checks exercise the same definitions on real texts.
They also observe the exact fuel each loop needs and the final Core store,
which the theorem leaves existential: the accumulator cell comes first and
holds the result, followed by the cells the step allocated. -/
set_option autoImplicit false

namespace Tests.SourceLoopMeaning

open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.ScalarMeaning
open Solcore.Synthesis.Core.BoundedLoop (CheckedPlan)
open Tests.SourceLoopEmitter (entry increment mutableStep arbitraryEntry)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- The Word that Core returns and the length of its final store. The first
location must be the accumulator cell holding the result, and every cell a
Word. -/
private def coreRun (label : String) (program : Program) : IO (Nat × Nat) :=
  match program.runStateful 100000 with
  | .done (.word word) store => do
      match store with
      | .word accumulator :: cells =>
          ensure (accumulator == word) s!"loop accumulator differs from its result: {label}"
          ensure (cells.all fun | .word _ => true | _ => false)
            s!"loop step allocated a cell that is not a Word: {label}"
      | _ => throw (IO.userError s!"Core loop lost its accumulator cell: {label}")
      pure (word.val, store.length)
  | _ => throw (IO.userError s!"Core loop did not return a Word: {label}")

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def call (index : Nat) (argument : Wire.Expr) : Wire.Expr := .apply (.var index) argument
private def wrap (value : Nat) : Nat := value % 2 ^ 256
private def maximum : Nat := 2 ^ 256 - 1
private def high : Nat := 2 ^ 255

private def checkedPlan (label : String) (helpers : List Wire.Expr) (body : Wire.Expr)
    (mask : Nat) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? helpers body |
    throw (IO.userError s!"loop step failed the aggregate DAG checker: {label}")
  let some plan := CheckedPlan.ofParts? graph mask |
    throw (IO.userError s!"loop plan failed its checker: {label}")
  pure plan

private def emitted (label : String) (plan : CheckedPlan) : IO EmittedProgram :=
  match Loop.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"loop emission failed: {label}: {reprStr error}")

/-- The emitted text parses with the loop grammar to a file whose printing is
that text. It imports the raw aliases exactly when a step body uses one and
declares `sc_step` after one function per helper. The loop-free grammar rejects
it. -/
private def checkReprint (label : String) (plan : CheckedPlan) (source : String) : IO Unit := do
  let some file := parseLoopSource source |
    throw (IO.userError s!"emitted loop source is outside the fragment: {label}")
  ensure (file.print == source) s!"parsed loop source does not print back: {label}"
  ensure (file.opcodeAliases == aggregateAliases (plan.step.helpers ++ [plan.step.entry]) &&
      file.functions.length == plan.step.helpers.length + 1 &&
      (file.functions.getLast?.map (·.name)) == some "sc_step" &&
      file.contract == Loop.contractName)
    s!"loop file has other aliases, functions or contract: {label}"
  ensure (parseSource source).isNone s!"the loop-free grammar accepted a loop text: {label}"

/-- Every boundary input, the inputs three, six and seven, and every input with
a hand-known result agree with Core once the loop has one more unit of fuel
than iterations; less fuel has no meaning. A hand-known formula and a
hand-known final store length, from the iteration count, must agree as well.
Returns the emitted text. -/
private def checkPlan (label : String) (plan : CheckedPlan) (known : List (Nat × Nat) := [])
    (formula : Option (Nat → Nat) := none) (cells : Option (Nat → Nat) := none) :
    IO String := do
  let program ← emitted label plan
  checkReprint label plan program.source
  let inputs := known.map Prod.fst ++ Tests.SourceScalarMeaning.boundaryInputs ++ [3, 6, 7]
  for input in inputs do
    let (expected, stored) ← coreRun label (plan.instantiate (Word.ofNatModulo input)).toCore
    let iterations := input &&& plan.mask
    for fuel in [iterations + 1, plan.mask + 1, 64] do
      ensure (loopSourceCall fuel program.source "run" [input] == some expected)
        s!"loop source meaning differs from Core: {label} at {input}, fuel {fuel}"
    ensure (loopSourceCall iterations program.source "run" [input] == none)
      s!"loop finished with fewer condition evaluations: {label} at {input}"
    ensure (sourceCall program.source "run" [input] == none)
      s!"the loop-free meaning gave a loop a result: {label} at {input}"
    if let some result := formula then
      ensure (expected == result input)
        s!"loop Core result differs from its formula: {label} at {input}"
    if let some length := cells then
      ensure (stored == length iterations)
        s!"loop Core store has another number of cells: {label} at {input}"
  for (input, expected) in known do
    ensure (loopSourceCall (plan.mask + 1) program.source "run" [input] == some expected)
      s!"loop source differs from its hand-known result: {label} at {input}"
  ensure (loopSourceCall 64 program.source "run" [2 ^ 256] == none)
    s!"loop method accepted an argument outside uint256: {label}"
  return program.source

/-- The regression steps of `SourceLoopEmitter` and two steps through a
projected pair and a sum payload, with their hand-known results and cell
counts: the step runs `count` times and the store holds the accumulator and one
cell per call of the private-cell step. -/
private def fixedSteps :
    List (String × List Wire.Expr × Wire.Expr × (Nat → Nat → Nat) × (Nat → Nat)) := [
  ("increment", [increment], entry, fun input count => wrap (input + count), fun _ => 1),
  ("arbitrary entry", [increment], arbitraryEntry, fun input count => wrap (input + 11 * count),
    fun _ => 1),
  ("private cell", [mutableStep], entry, fun input count => wrap (input + 2 * count),
    fun count => 1 + count),
  ("mixed", [increment, mutableStep], .apply (.var 1) (.apply (.var 2) (.var 0)),
    fun input count => wrap (input + 3 * count), fun count => 1 + count),
  ("identity entry", [increment], .var 0, fun input _ => input, fun _ => 1),
  ("constant entry", [increment], word 42, fun input count => if count == 0 then input else 42,
    fun _ => 1),
  ("projected pair", [increment], .first (.pair (call 1 (.var 0)) (.var 0)),
    fun input count => wrap (input + count), fun _ => 1),
  ("sum payload", [increment], .caseE (.inRight .word (call 1 (.var 0))) (word 0) (.var 0),
    fun input count => wrap (input + count), fun _ => 1)]

/-- Raw opcodes applied to helper results, with the hand-known results of one
application from `SourceAggregateCallGraphMeaning`. Under mask one, an odd input
applies the step once and an even input returns unchanged. -/
private def primitiveSteps : List (String × Wire.Expr × Nat × Nat) :=
  let c := call 1
  [("clz", .unary .wordClz (c (.var 0)), 0, 256),
    ("div", .binary .wordDiv (c (.var 0)) (c (word 2)), 5, 2),
    ("mod", .binary .wordMod (c (.var 0)) (c (word 0)), maximum, 0),
    ("shl", .binary .wordShl (c (word 1)) (c (.var 0)), 255, high),
    ("shr", .binary .wordShr (c (word maximum)) (c (.var 0)), 256, 0),
    ("sar", .binary .wordSar (c (word high)) (c (.var 0)), maximum, maximum),
    ("sdiv", .binary .wordSdiv (c (.var 0)) (c (word maximum)), high, high),
    ("smod", .binary .wordSmod (c (.var 0)) (c (word 2)), maximum - 6, maximum),
    ("sgt", .ifE (.binary .wordSgt (c (.var 0)) (c (word 0))) (word 1) (word 0), high - 1, 1),
    ("byte", .binary .wordByte (c (.var 0)) (c (word 0x1234)), 31, 0x34),
    ("pow", .binary .wordPow (c (word maximum)) (c (.var 0)), maximum, maximum),
    ("signextend", .binary .wordSignExtend (c (word 0)) (c (.var 0)), 0x80, maximum - 0x7f),
    ("addmod", .ternary .wordAddMod (c (.var 0)) (c (word 1)) (c (word maximum)), maximum, 1),
    ("mulmod", .ternary .wordMulMod (c (.var 0)) (c (word 2)) (c (word maximum)), high, 1)]

/-- Plans from the `runtime-loops` generator at two budgets, which together
use every generated mask. Seeds the generator rejects are skipped. -/
private def checkGenerated : IO Nat := do
  let mut count := 0
  let mut masks : List Nat := []
  for nodes in [256, 512] do
    for seed in List.range 12 do
      match Loop.generatedPlan (Seed.ofNat seed) nodes with
      | .error _ => pure ()
      | .ok (plan, _) =>
          let _ ← checkPlan s!"generated budget {nodes} seed {seed}" plan
          masks := (masks ++ [plan.mask]).eraseDups
          count := count + 1
  ensure (count ≥ 16) s!"the loop generator produced only {count} plans"
  ensure ([1, 3, 7].all masks.contains) "generated loops missed a mask"
  return count

/-- On loop-free aggregate texts, with pairs, sums, matches and private cells,
the loop grammar returns the same file and the loop meaning is `sourceCall`
for every fuel. -/
private def checkLoopFree : IO Nat := do
  let mut count := 0
  let steps := [([mutableStep], entry),
    ([increment], .caseE (.inRight .word (call 1 (.var 0))) (word 0) (.var 0))]
  for (helpers, body) in steps do
    let some graph := Aggregates.CheckedDAG.ofParts? helpers body |
      throw (IO.userError "loop-free aggregate fixture failed its checker")
    let program ← match Aggregate.emit graph with
      | .ok value => pure value
      | .error error => throw (IO.userError s!"aggregate emission failed: {reprStr error}")
    let some file := parseSource program.source |
      throw (IO.userError "emitted aggregate source is outside the loop-free fragment")
    let some loopFile := parseLoopSource program.source |
      throw (IO.userError "the loop grammar rejected a loop-free aggregate text")
    ensure (loopFile.print == program.source && file.toLoop.print == program.source)
      "the loop grammar changed a loop-free aggregate file"
    for input in Tests.SourceScalarMeaning.boundaryInputs ++ [2 ^ 256] do
      for fuel in [0, 1, 64] do
        ensure (loopSourceCall fuel program.source "run" [input] ==
            sourceCall program.source "run" [input])
          s!"loop meaning differs from sourceCall on a loop-free text at {input}, fuel {fuel}"
    count := count + 1
  return count

/-- Altered loops lose their meaning or change their result. -/
private def checkAlterations (source : String) (plan : CheckedPlan) : IO Unit := do
  let core (input : Nat) : IO Nat := do
    pure (← coreRun "altered" (plan.instantiate (Word.ofNatModulo input)).toCore).1
  let replace (old new : String) : IO String := do
    let changed := source.replace old new
    ensure (changed != source) s!"loop fixture has no {old}"
    pure changed
  let doubled ← replace "while (sc_limit > sc_counter) {" "while ((sc_limit > sc_counter)) {"
  ensure (parseLoopSource doubled).isNone "a loop condition in two parentheses was accepted"
  let endless ← replace "            sc_counter = (sc_counter + 1);\n" ""
  ensure ((parseLoopSource endless).isSome &&
      loopSourceCall 1000 endless "run" [0] == some (← core 0) &&
      loopSourceCall 1000 endless "run" [7] == none)
    "a loop without its counter step received a meaning"
  let shadowed ← replace "            sc_acc = sc_step(sc_acc);"
    "            let sc_acc: word = sc_step(sc_acc);"
  ensure (loopSourceCall 64 shadowed "run" [7] == some 7 && (← core 7) != 7)
    "a loop body declaration outlived its iteration"
  let reused ← replace "    let sc_c0: word = sc_arg;" "    sc_c0 = sc_arg;"
  ensure ((parseLoopSource reused).isSome && loopSourceCall 64 reused "run" [7] == none)
    "a step reused a cell it never declared"

def testSourceLoopMeaning : IO Unit := do
  let mut privateSource := ""
  let mut privatePlan : Option CheckedPlan := none
  for (label, helpers, body, formula, cells) in fixedSteps do
    for mask in [0, 1, 3, 7] do
      let plan ← checkedPlan s!"{label} mask {mask}" helpers body mask
      let source ← checkPlan s!"{label} mask {mask}" plan
        (formula := some fun input => formula input (input &&& mask)) (cells := some cells)
      if label == "private cell" && mask == 7 then
        privateSource := source
        privatePlan := some plan
  -- Seven iterations of x + 2 from seven, with one fresh cell per call.
  let some sevenfold := privatePlan | throw (IO.userError "private-cell plan missing")
  let _ ← checkPlan "private cell sevenfold" sevenfold [(7, 21), (0, 0), (high, high)]
  for (label, body, input, expected) in primitiveSteps do
    let plan ← checkedPlan label [.var 0] body 1
    let _ ← checkPlan label plan [(input, if input % 2 == 1 then expected else input)]
  let generated ← checkGenerated
  let loopFree ← checkLoopFree
  checkAlterations privateSource sevenfold
  IO.println (s!"aggregate loop source meaning: {fixedSteps.length} fixed steps " ++
    s!"under 4 masks, {primitiveSteps.length} raw primitive steps and {generated} generated " ++
    s!"plans agree with Core at their exact fuel; {loopFree} loop-free texts keep sourceCall")

end Tests.SourceLoopMeaning
end

section
-- leanmerge: from Solcore.Test.SourceRollbackMeaning
/-! Executable checks of the rollback source meaning on actual rollback emitter
output. Each emitted text is lexed, parsed with the rollback grammar and called
under the rollback source semantics, one transaction at a time, from the
storage of the account that the committed world holds. Each call is compared
with the original Core contract's top-level transaction: a returned call with
the returned ABI bytes and the committed slots, a reverted call with the
reverted bytes and an unchanged account storage. `StorageRollback.emit_source_meaning`
covers every successful emission and every installed account; these checks
exercise the same definitions on real texts and histories that mix even and
odd inputs. Altered texts lose or change their meaning. -/
set_option autoImplicit false

namespace Tests.SourceRollbackMeaning

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.ScalarMeaning
open Solcore.Synthesis.Core.StorageRollback (CheckedPlan)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def call (index : Nat) (argument : Wire.Expr) : Wire.Expr := .apply (.var index) argument
private def entry : Wire.Expr := call 1 (.var 0)
private def maximum : Nat := 2 ^ 256 - 1
private def high : Nat := 2 ^ 255

private def checkedPlan (label : String) (helpers : List Wire.Expr) (body : Wire.Expr) :
    IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers body |
    throw (IO.userError s!"rollback step failed the aggregate DAG checker: {label}")
  let some plan := CheckedPlan.ofParts? step |
    throw (IO.userError s!"rollback plan failed the host checker: {label}")
  pure plan

private def emitted (label : String) (plan : CheckedPlan) : IO EmittedProgram :=
  match StorageRollback.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"rollback emission failed: {label}: {reprStr error}")

/-- The emitted text parses with the rollback grammar to a file whose printing
is that text, with one function per helper and `sc_step`, and the aliases
exactly when a step body uses one. The loop-free and storage grammars reject
it. -/
private def checkReprint (label : String) (plan : CheckedPlan) (source : String) : IO Unit := do
  let some file := parseRollbackSource source |
    throw (IO.userError s!"emitted rollback source is outside the fragment: {label}")
  ensure (file.print == source) s!"parsed rollback source does not print back: {label}"
  ensure (file.opcodeAliases == aggregateAliases (plan.step.helpers ++ [plan.step.entry]) &&
      file.functions.length == plan.step.helpers.length + 1 &&
      (file.functions.getLast?.map (·.name)) == some "sc_step" &&
      file.contract == StorageRollback.contractName)
    s!"rollback file has other aliases, functions or contract: {label}"
  ensure ((parseSource source).isNone && (parseStorageSource source).isNone)
    s!"the loop-free or storage grammar accepted a rollback text: {label}"

private def target : Address := ⟨100, by decide⟩
private def caller : Address := ⟨200, by decide⟩

/-- The slots compared after each transaction. -/
private def comparedSlots : List Nat := [0, 1, 2, 3, high, maximum]

/-- Two nonempty initial storages; the second makes slot 1 wrap to zero. -/
private def initialStorages : List (List (Nat × Nat)) :=
  [[], [(0, 5), (1, 9), (2, 7), (high, 3)], [(0, maximum), (1, maximum), (3, 1)]]

/-- Runs one history from an account holding `initial`. Before each
transaction the source storage is read from the account that the committed
world holds; the source call must settle as the Core transaction. When `step`
is given, the outcome's word and the written slots must also follow the
two-slot recurrence. Returns the numbers of returned and reverted
transactions. -/
private def checkHistory (label : String) (plan : CheckedPlan) (source : String)
    (initial : List (Nat × Nat)) (inputs : List Nat)
    (step : Option (Word → Word) := none) : IO (Nat × Nat) := do
  let registry : CheckedContractRegistry :=
    ⟨fun address => if address == target then some plan.contract else none⟩
  let installedAccount := initial.foldl (fun account (slot, value) =>
    account.storageWrite (Word.ofNatModulo slot) (Word.ofNatModulo value))
    (Account.empty.withCode plan.code)
  let mut world := WorldState.empty.putAccount target installedAccount
  let mut returned := 0
  let mut reverted := 0
  for input in inputs do
    let calldata := Solcore.Synthesis.Stateful.StorageExecution.inputData (Word.ofNatModulo input)
    ensure (calldata.wordBE? (Word.ofNatModulo 4) == some (Word.ofNatModulo input))
      s!"canonical calldata does not carry its input word: {label}"
    let some ⟨contract, installed⟩ := registry.resolve? world target |
      throw (IO.userError s!"committed world no longer resolves the contract: {label}")
    let storage := accountStorage installed.account
    let invocation : TopLevelInvocation :=
      { target, caller, callValue := Word.zero, inputData := calldata }
    let some outcome := rollbackSourceCall source storage "run" [input] |
      throw (IO.userError s!"rollback source call has no meaning: {label} at {input}")
    match TopLevelExecution.run contract invocation installed 0 with
    | .outOfFuel _ _ _ _ _ _ => pure ()
    | .completed _ => throw (IO.userError s!"zero fuel completed a rollback transaction: {label}")
    let result ← match TopLevelExecution.run contract invocation installed 100000 with
      | .outOfFuel _ _ _ _ _ _ =>
          throw (IO.userError s!"rollback transaction exhausted its fuel: {label}")
      | .completed result => pure result
    let some account := result.finalWorld.account? target |
      throw (IO.userError s!"committed storage account disappeared: {label}")
    let expected : Option (Nat × Nat × Nat) := step.map fun stepResult =>
      let computed := stepResult ((Word.ofNatModulo input).add (Word.ofNatModulo (storage 0)))
      let second := (Word.ofNatModulo (storage 1)).add (Word.ofNatModulo 1)
      ((computed.add second).val, computed.val, second.val)
    match outcome with
    | .returned value storage' =>
        ensure (input % 2 == 0) s!"an odd input returned: {label} at {input}"
        ensure (value < 2 ^ 256 &&
            result.outcome == .returned (encodeWordBytesBE (Word.ofNatModulo value)))
          s!"returned word differs from the Core transaction: {label} at {input}"
        ensure (comparedSlots.all fun slot =>
            (account.storageRead (Word.ofNatModulo slot)).val == storage' slot)
          s!"committed slots differ from the source storage: {label} at {input}"
        if let some (sum, first, second) := expected then
          ensure (value == sum && storage' 0 == first && storage' 1 == second)
            s!"returned results differ from the two-slot recurrence: {label} at {input}"
        returned := returned + 1
    | .reverted data =>
        ensure (input % 2 == 1) s!"an even input reverted: {label} at {input}"
        ensure (data < 2 ^ 256 &&
            result.outcome == .reverted (encodeWordBytesBE (Word.ofNatModulo data)))
          s!"reverted word differs from the Core transaction: {label} at {input}"
        ensure (comparedSlots.all fun slot =>
            (account.storageRead (Word.ofNatModulo slot)).val == storage slot)
          s!"a reverted transaction changed the committed slots: {label} at {input}"
        if let some (sum, _, _) := expected then
          ensure (data == sum) s!"reverted word differs from the two-slot recurrence: {label}"
        reverted := reverted + 1
    world := result.finalWorld
  let some ⟨_, installed⟩ := registry.resolve? world target |
    throw (IO.userError s!"committed world no longer resolves the contract: {label}")
  ensure (rollbackSourceCall source (accountStorage installed.account) "run" [2 ^ 256]).isNone
    s!"rollback method accepted an argument outside uint256: {label}"
  return (returned, reverted)

/-- Every history of a plan, from each initial storage. -/
private def checkPlan (label : String) (plan : CheckedPlan) (inputs : List Nat)
    (step : Option (Word → Word) := none) : IO (String × Nat × Nat) := do
  let program ← emitted label plan
  checkReprint label plan program.source
  let mut returned := 0
  let mut reverted := 0
  for initial in initialStorages do
    let (more, fewer) ← checkHistory label plan program.source initial inputs step
    returned := returned + more
    reverted := reverted + fewer
  return (program.source, returned, reverted)

private def regressionInputs : List Nat := [2, 3, 4, 1, maximum, high, high + 1, 0, 7]

private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)

private def privateStep : Wire.Expr :=
  .letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))

private def pairStep : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.pair (.loadCell (.var 0))
      (.letE (.storeCell (.var 0) (word 2)) (.loadCell (.var 1))))
      (.binary .wordAdd (.first (.var 0)) (.second (.var 0))))

/-- The regression plans of `SourceStorageRollbackEmitter`, with their step
functions. Returns the identity plan's text and the transaction counts. -/
private def regressionChecks : IO (String × Nat × Nat) := do
  let plus (amount : Nat) (input : Word) : Word := input.add (Word.ofNatModulo amount)
  let clearOne (input : Word) : Word := if input == Word.ofNatModulo 1 then Word.zero else input
  let mut returned := 0
  let mut reverted := 0
  let (identitySource, more, fewer) ← checkPlan "identity"
    (← checkedPlan "identity" [.var 0] entry) regressionInputs (some id)
  returned := returned + more
  reverted := reverted + fewer
  for (label, helpers, body, step) in [
      ("clears", [.ifE (.binary .wordEq (.var 0) (word 1)) (word 0) (.var 0)], entry, clearOne),
      ("private cell", [privateStep], .binary .wordSub entry (word 1), plus 1),
      ("mixed", [increment, pairStep], call 1 (call 2 (.var 0)), plus 3),
      ("constant", [.var 0], word 0, fun _ => Word.zero),
      ("division", [.binary .wordDiv (.var 0) (word 1)], entry, id)] do
    let (_, more, fewer) ← checkPlan label (← checkedPlan label helpers body) regressionInputs
      (some step)
    returned := returned + more
    reverted := reverted + fewer
  return (identitySource, returned, reverted)

/-- Raw opcodes applied to a helper result as the step. -/
private def primitiveSteps : List (String × Wire.Expr) :=
  let c := call 1
  [("clz", .unary .wordClz (c (.var 0))),
    ("div", .binary .wordDiv (c (.var 0)) (c (word 2))),
    ("mod", .binary .wordMod (c (.var 0)) (c (word 0))),
    ("shl", .binary .wordShl (c (word 1)) (c (.var 0))),
    ("shr", .binary .wordShr (c (word maximum)) (c (.var 0))),
    ("sar", .binary .wordSar (c (word high)) (c (.var 0))),
    ("sdiv", .binary .wordSdiv (c (.var 0)) (c (word maximum))),
    ("smod", .binary .wordSmod (c (.var 0)) (c (word 2))),
    ("sgt", .ifE (.binary .wordSgt (c (.var 0)) (c (word 0))) (word 1) (word 0)),
    ("byte", .binary .wordByte (c (.var 0)) (c (word 0x1234))),
    ("pow", .binary .wordPow (c (word maximum)) (c (.var 0))),
    ("signextend", .binary .wordSignExtend (c (word 0)) (c (.var 0))),
    ("addmod", .ternary .wordAddMod (c (.var 0)) (c (word 1)) (c (word maximum))),
    ("mulmod", .ternary .wordMulMod (c (.var 0)) (c (word 2)) (c (word maximum)))]

/-- Generated rollback scenarios at two budgets, with their generated inputs
and two more. Seeds the generator rejects are skipped. -/
private def checkGenerated : IO (Nat × Nat × Nat) := do
  let mut plans := 0
  let mut returned := 0
  let mut reverted := 0
  for nodes in [256, 512] do
    for seed in List.range 12 do
      match StorageRollback.generatedScenario (Seed.ofNat seed) nodes with
      | .error _ => pure ()
      | .ok (scenario, _) =>
          let inputs := scenario.transactions.map (·.input.val)
          let (_, more, fewer) ← checkPlan s!"generated budget {nodes} seed {seed}"
            scenario.plan (inputs ++ [1, maximum - 1])
          plans := plans + 1
          returned := returned + more
          reverted := reverted + fewer
  ensure (plans ≥ 16) s!"the rollback generator produced only {plans} plans"
  return (plans, returned, reverted)

/-- Storage texts are outside the rollback grammar. -/
private def checkStorageTexts : IO Nat := do
  let mut count := 0
  for (helpers, body) in [([privateStep], entry), ([.binary .wordDiv (.var 0) (word 1)], entry)] do
    let some step := Aggregates.CheckedDAG.ofParts? helpers body |
      throw (IO.userError "storage fixture failed the aggregate DAG checker")
    let some plan := Solcore.Synthesis.Core.StorageContract.CheckedPlan.ofParts? step |
      throw (IO.userError "storage fixture failed the host checker")
    let program ← match Storage.emit plan with
      | .ok value => pure value
      | .error error => throw (IO.userError s!"storage emission failed: {reprStr error}")
    ensure ((parseStorageSource program.source).isSome &&
        (parseRollbackSource program.source).isNone)
      "the rollback grammar accepted a storage text"
    count := count + 1
  return count

/-- The outcome of one call from a nonempty storage. -/
private def observed (source : String) (input : Nat) : Option String :=
  let storage : Storage := fun slot => if slot = 0 then 5 else if slot = 1 then 9 else 7
  (rollbackSourceCall source storage "run" [input]).map fun
    | .returned value storage' => s!"returned {value} {storage' 0} {storage' 1}"
    | .reverted data => s!"reverted {data}"

/-- Altered rollback programs lose their meaning or change their outcome. -/
private def checkAlterations (source : String) : IO Unit := do
  let replace (old new : String) : IO String := do
    let changed := source.replace old new
    ensure (changed != source) s!"rollback fixture has no {old}"
    pure changed
  let even := observed source 2
  let odd := observed source 3
  ensure (even.isSome && odd.isSome) "the rollback fixture has no meaning"
  let longer ← replace "revert_(0, 32);" "revert_(0, 64);"
  ensure ((parseRollbackSource longer).isSome && observed longer 3 == none &&
      observed longer 2 == even)
    "a revert of other bytes received a meaning"
  let elsewhere ← replace "revert_(0, 32);" "revert_(32, 32);"
  ensure ((parseRollbackSource elsewhere).isSome && observed elsewhere 3 == none)
    "a revert from another offset received a meaning"
  let otherWord ← replace "mstore(0, sc_result);" "mstore(0, sc_final0);"
  ensure ((parseRollbackSource otherWord).isSome && observed otherWord 3 != odd &&
      observed otherWord 2 == even)
    "storing another word kept the reverted word"
  let flipped ← replace "if ((sc_input & 1) == 1) {" "if ((sc_input & 1) == 0) {"
  ensure ((parseRollbackSource flipped).isSome && observed flipped 2 != even &&
      observed flipped 3 != odd)
    "a flipped condition kept the outcomes"
  let noRevert ← replace
    "        if ((sc_input & 1) == 1) {\n            mstore(0, sc_result);\n            revert_(0, 32);\n        }\n" ""
  ensure ((parseRollbackSource noRevert).isSome && observed noRevert 3 != odd)
    "a program without its revert block kept the odd outcome"
  let doubled ← replace "if ((sc_input & 1) == 1) {" "if (((sc_input & 1) == 1)) {"
  ensure (parseRollbackSource doubled).isNone
    "a revert condition in two pairs of parentheses was accepted"
  let twoOperators ← replace "sc_final0 + sc_final1;" "sc_final0 + sc_final1 + 0;"
  ensure (parseRollbackSource twoOperators).isNone
    "two infix operations without parentheses were accepted"
  let booleanStore ← replace "mstore(0, sc_result);" "mstore(0, true);"
  ensure ((parseRollbackSource booleanStore).isSome && observed booleanStore 3 == none)
    "a Boolean was stored in memory"

def testSourceRollbackMeaning : IO Unit := do
  let (identitySource, regressionReturned, regressionReverted) ← regressionChecks
  let mut primitivesReturned := 0
  let mut primitivesReverted := 0
  for (label, body) in primitiveSteps do
    let (_, more, fewer) ← checkPlan label (← checkedPlan label [.var 0] body)
      [0, 1, maximum, high]
    primitivesReturned := primitivesReturned + more
    primitivesReverted := primitivesReverted + fewer
  let (generated, generatedReturned, generatedReverted) ← checkGenerated
  let storageTexts ← checkStorageTexts
  checkAlterations identitySource
  IO.println (s!"rollback source meaning: 6 regression plans " ++
    s!"({regressionReturned} returned, {regressionReverted} reverted), 14 raw primitive plans " ++
    s!"({primitivesReturned} returned, {primitivesReverted} reverted) and {generated} generated " ++
    s!"plans ({generatedReturned} returned, {generatedReverted} reverted) settle as Core from " ++
    s!"3 initial storages; {storageTexts} storage texts are outside the rollback grammar")

end Tests.SourceRollbackMeaning
end

section
-- leanmerge: from Solcore.Test.SourceStorageMeaning
/-! Executable checks of the storage source meaning on actual storage emitter
output. Each emitted text is lexed, parsed with the storage grammar and called
under the storage source semantics, one transaction at a time, from the storage
of the account that the committed world holds. Each call is compared with the
original Core contract's top-level transaction: the returned word, its ABI
bytes and the committed account storage. `Storage.emit_source_meaning` covers
every successful emission and every installed account; these checks exercise
the same definitions on real texts and histories, from empty and from nonempty
storage. Altered texts lose or change their meaning. -/
set_option autoImplicit false

namespace Tests.SourceStorageMeaning

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.ScalarMeaning
open Solcore.Synthesis.Core.StorageContract (CheckedPlan)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def call (index : Nat) (argument : Wire.Expr) : Wire.Expr := .apply (.var index) argument
private def entry : Wire.Expr := call 1 (.var 0)
private def maximum : Nat := 2 ^ 256 - 1
private def high : Nat := 2 ^ 255

private def checkedPlan (label : String) (helpers : List Wire.Expr) (body : Wire.Expr) :
    IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers body |
    throw (IO.userError s!"storage step failed the aggregate DAG checker: {label}")
  let some plan := CheckedPlan.ofParts? step |
    throw (IO.userError s!"storage plan failed the host checker: {label}")
  pure plan

private def emitted (label : String) (plan : CheckedPlan) : IO EmittedProgram :=
  match Storage.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"storage emission failed: {label}: {reprStr error}")

/-- The emitted text parses with the storage grammar to a file whose printing is
that text, with one function per helper and `sc_step`, and the aliases exactly
when a step body uses one. The loop-free grammar rejects it. -/
private def checkReprint (label : String) (plan : CheckedPlan) (source : String) : IO Unit := do
  let some file := parseStorageSource source |
    throw (IO.userError s!"emitted storage source is outside the fragment: {label}")
  ensure (file.print == source) s!"parsed storage source does not print back: {label}"
  ensure (file.opcodeAliases == aggregateAliases (plan.step.helpers ++ [plan.step.entry]) &&
      file.functions.length == plan.step.helpers.length + 1 &&
      (file.functions.getLast?.map (·.name)) == some "sc_step" &&
      file.contract == Storage.contractName)
    s!"storage file has other aliases, functions or contract: {label}"
  ensure (parseSource source).isNone s!"the loop-free grammar accepted a storage text: {label}"

private def target : Address := ⟨100, by decide⟩
private def caller : Address := ⟨200, by decide⟩

/-- The slots compared after each transaction: both written slots, untouched
ones and the highest. -/
private def comparedSlots : List Nat := [0, 1, 2, 3, high, maximum]

/-- Two nonempty initial storages; the second makes slot 1 wrap to zero. -/
private def initialStorages : List (List (Nat × Nat)) :=
  [[], [(0, 5), (1, 9), (2, 7), (high, 3)], [(0, maximum), (1, maximum), (3, 1)]]

/-- Runs one history from an account holding `initial`. Before each
transaction the source storage is read from the account that the committed
world holds; the source call must give the transaction's word and committed
slots. When `step` is given, the results must also follow the two-slot
recurrence. Returns the number of transactions. -/
private def checkHistory (label : String) (plan : CheckedPlan) (source : String)
    (initial : List (Nat × Nat)) (inputs : List Nat)
    (step : Option (Word → Word) := none) : IO Nat := do
  let registry : CheckedContractRegistry :=
    ⟨fun address => if address == target then some plan.contract else none⟩
  let installedAccount := initial.foldl (fun account (slot, value) =>
    account.storageWrite (Word.ofNatModulo slot) (Word.ofNatModulo value))
    (Account.empty.withCode plan.code)
  let mut world := WorldState.empty.putAccount target installedAccount
  let mut previous : Option Storage := none
  let mut count := 0
  for input in inputs do
    let calldata := Solcore.Synthesis.Stateful.StorageExecution.inputData (Word.ofNatModulo input)
    ensure (calldata.wordBE? (Word.ofNatModulo 4) == some (Word.ofNatModulo input))
      s!"canonical calldata does not carry its input word: {label}"
    let some ⟨contract, installed⟩ := registry.resolve? world target |
      throw (IO.userError s!"committed world no longer resolves the contract: {label}")
    let storage := accountStorage installed.account
    if let some committed := previous then
      ensure (comparedSlots.all fun slot => storage slot == committed slot)
        s!"committed account storage differs from the source storage: {label}"
    let invocation : TopLevelInvocation :=
      { target, caller, callValue := Word.zero, inputData := calldata }
    let some (value, storage') := storageSourceCall source storage "run" [input] |
      throw (IO.userError s!"storage source call has no meaning: {label} at {input}")
    match TopLevelExecution.run contract invocation installed 0 with
    | .outOfFuel _ _ _ _ _ _ => pure ()
    | .completed _ => throw (IO.userError s!"zero fuel completed a storage transaction: {label}")
    match TopLevelExecution.run contract invocation installed 100000 with
    | .outOfFuel _ _ _ _ _ _ =>
        throw (IO.userError s!"storage transaction exhausted its fuel: {label}")
    | .completed result =>
        ensure (value < 2 ^ 256 && result.coreValue == .word (Word.ofNatModulo value) &&
            result.outcome == .returned (encodeWordBytesBE (Word.ofNatModulo value)))
          s!"storage source result differs from the Core transaction: {label} at {input}"
        let some account := result.finalWorld.account? target |
          throw (IO.userError s!"committed storage account disappeared: {label}")
        ensure (comparedSlots.all fun slot =>
            (account.storageRead (Word.ofNatModulo slot)).val == storage' slot)
          s!"committed slots differ from the source storage: {label} at {input}"
        if let some stepResult := step then
          let first := Word.ofNatModulo (storage 0)
          let second := (Word.ofNatModulo (storage 1)).add (Word.ofNatModulo 1)
          let computed := stepResult ((Word.ofNatModulo input).add first)
          ensure (storage' 0 == computed.val && storage' 1 == second.val &&
              value == (computed.add second).val)
            s!"storage results differ from the two-slot recurrence: {label} at {input}"
        world := result.finalWorld
        previous := some storage'
    count := count + 1
  let some ⟨_, installed⟩ := registry.resolve? world target |
    throw (IO.userError s!"committed world no longer resolves the contract: {label}")
  ensure (storageSourceCall source (accountStorage installed.account) "run" [2 ^ 256]).isNone
    s!"storage method accepted an argument outside uint256: {label}"
  return count

/-- Every history of a plan, from each initial storage. -/
private def checkPlan (label : String) (plan : CheckedPlan) (inputs : List Nat)
    (step : Option (Word → Word) := none) : IO (String × Nat) := do
  let program ← emitted label plan
  checkReprint label plan program.source
  let mut count := 0
  for initial in initialStorages do
    count := count + (← checkHistory label plan program.source initial inputs step)
  return (program.source, count)

private def regressionInputs : List Nat := [0, 1, 3, maximum, 0, high, 7]

private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)

private def privateStep : Wire.Expr :=
  .letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))

private def pairStep : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.pair (.loadCell (.var 0))
      (.letE (.storeCell (.var 0) (word 2)) (.loadCell (.var 1))))
      (.binary .wordAdd (.first (.var 0)) (.second (.var 0))))

/-- The regression plans of `SourceStorageEmitter`, with their step functions.
Returns the increment plan's text and the number of transactions. -/
private def regressionChecks : IO (String × Nat) := do
  let plus (amount : Nat) (input : Word) : Word := input.add (Word.ofNatModulo amount)
  let (incrementSource, first) ← checkPlan "increment" (← checkedPlan "increment" [increment] entry)
    regressionInputs (some (plus 1))
  let (_, second) ← checkPlan "private cell"
    (← checkedPlan "private cell" [privateStep] (.binary .wordSub entry (word 1)))
    regressionInputs (some (plus 1))
  let (_, third) ← checkPlan "mixed"
    (← checkedPlan "mixed" [increment, pairStep] (call 1 (call 2 (.var 0))))
    regressionInputs (some (plus 3))
  let (_, fourth) ← checkPlan "identity" (← checkedPlan "identity" [increment] (.var 0))
    [5, 2 ^ 256 - 5, 0] (some id)
  let (_, fifth) ← checkPlan "constant" (← checkedPlan "constant" [increment] (word 0))
    regressionInputs (some fun _ => Word.zero)
  let (_, sixth) ← checkPlan "division" (← checkedPlan "division"
    [.binary .wordDiv (.var 0) (word 1)] entry) regressionInputs (some id)
  return (incrementSource, first + second + third + fourth + fifth + sixth)

/-- Raw opcodes applied to a helper result as the step. -/
private def primitiveSteps : List (String × Wire.Expr) :=
  let c := call 1
  [("clz", .unary .wordClz (c (.var 0))),
    ("div", .binary .wordDiv (c (.var 0)) (c (word 2))),
    ("mod", .binary .wordMod (c (.var 0)) (c (word 0))),
    ("shl", .binary .wordShl (c (word 1)) (c (.var 0))),
    ("shr", .binary .wordShr (c (word maximum)) (c (.var 0))),
    ("sar", .binary .wordSar (c (word high)) (c (.var 0))),
    ("sdiv", .binary .wordSdiv (c (.var 0)) (c (word maximum))),
    ("smod", .binary .wordSmod (c (.var 0)) (c (word 2))),
    ("sgt", .ifE (.binary .wordSgt (c (.var 0)) (c (word 0))) (word 1) (word 0)),
    ("byte", .binary .wordByte (c (.var 0)) (c (word 0x1234))),
    ("pow", .binary .wordPow (c (word maximum)) (c (.var 0))),
    ("signextend", .binary .wordSignExtend (c (word 0)) (c (.var 0))),
    ("addmod", .ternary .wordAddMod (c (.var 0)) (c (word 1)) (c (word maximum))),
    ("mulmod", .ternary .wordMulMod (c (.var 0)) (c (word 2)) (c (word maximum)))]

/-- Generated storage scenarios at two budgets, each with its own generated
inputs. Seeds the generator rejects are skipped. -/
private def checkGenerated : IO (Nat × Nat) := do
  let mut plans := 0
  let mut transactions := 0
  for nodes in [256, 512] do
    for seed in List.range 12 do
      match Storage.generatedScenario (Seed.ofNat seed) nodes with
      | .error _ => pure ()
      | .ok (scenario, _) =>
          let inputs := scenario.transactions.map (·.input.val)
          let (_, count) ← checkPlan s!"generated budget {nodes} seed {seed}" scenario.plan
            (inputs ++ [0, maximum])
          plans := plans + 1
          transactions := transactions + count
  ensure (plans ≥ 16) s!"the storage generator produced only {plans} plans"
  return (plans, transactions)

/-- Loop-free aggregate texts are outside the storage grammar. -/
private def checkLoopFree : IO Nat := do
  let mut count := 0
  for (helpers, body) in [([privateStep], entry), ([.binary .wordDiv (.var 0) (word 1)], entry)] do
    let some graph := Aggregates.CheckedDAG.ofParts? helpers body |
      throw (IO.userError "loop-free aggregate fixture failed its checker")
    let program ← match Aggregate.emit graph with
      | .ok value => pure value
      | .error error => throw (IO.userError s!"aggregate emission failed: {reprStr error}")
    ensure ((parseSource program.source).isSome && (parseStorageSource program.source).isNone)
      "the storage grammar accepted a loop-free aggregate text"
    count := count + 1
  return count

/-- The result and the first slots after one call from a nonempty storage. -/
private def observed (source : String) : Option (Nat × Nat × Nat × Nat) :=
  let storage : Storage := fun slot => if slot = 0 then 5 else if slot = 1 then 9 else 7
  (storageSourceCall source storage "run" [1]).map fun (value, storage') =>
    (value, storage' 0, storage' 1, storage' 2)

/-- Altered storage programs lose their meaning or change their result. -/
private def checkAlterations (source : String) : IO Unit := do
  let replace (old new : String) : IO String := do
    let changed := source.replace old new
    ensure (changed != source) s!"storage fixture has no {old}"
    pure changed
  let expected := observed source
  ensure expected.isSome "the storage fixture has no meaning"
  let swappedSlot ← replace "        sstore(0, sc_computed);" "        sstore(2, sc_computed);"
  ensure ((parseStorageSource swappedSlot).isSome && observed swappedSlot != expected)
    "a store to another slot kept its result"
  let otherLoad ← replace "        let sc_old0: word = sload(0);"
    "        let sc_old0: word = sload(2);"
  ensure ((parseStorageSource otherLoad).isSome && observed otherLoad != expected)
    "a load of another slot kept its result"
  let dropped ← replace "        sstore(1, sc_old1 + 1);\n" ""
  ensure ((parseStorageSource dropped).isSome && observed dropped != expected)
    "a program without its second store kept its result"
  let parenthesized ← replace "sc_step(sc_input + sc_old0)" "sc_step((sc_input + sc_old0))"
  ensure ((parseStorageSource parenthesized).isSome && observed parenthesized == expected)
    "a parenthesized step argument changed the result"
  let twoOperators ← replace "sstore(1, sc_old1 + 1);" "sstore(1, sc_old1 + 1 + 1);"
  ensure (parseStorageSource twoOperators).isNone
    "two infix operations without parentheses were accepted"
  let helperLoad ← replace "    let sc_v0: word = 1;\n" "    let sc_v0: word = sload(1);\n"
  ensure ((parseStorageSource helperLoad).isSome && observed helperLoad == none)
    "a free function that reads storage received a meaning"
  let booleanStore ← replace "        sstore(0, sc_computed);" "        sstore(0, true);"
  ensure ((parseStorageSource booleanStore).isSome && observed booleanStore == none)
    "a Boolean was stored"
  let noStoreImport ← replace "import {sload, sstore} from std.opcodes;"
    "import {sload} from std.opcodes;"
  ensure (parseStorageSource noStoreImport).isNone "an import line without sstore was accepted"

def testSourceStorageMeaning : IO Unit := do
  let (incrementSource, regression) ← regressionChecks
  let mut primitives := 0
  for (label, body) in primitiveSteps do
    let (_, count) ← checkPlan label (← checkedPlan label [.var 0] body) [0, 1, maximum, high]
    primitives := primitives + count
  let (generated, generatedTransactions) ← checkGenerated
  let loopFree ← checkLoopFree
  checkAlterations incrementSource
  IO.println (s!"storage source meaning: 6 regression plans ({regression} transactions), " ++
    s!"14 raw primitive plans ({primitives} transactions) and {generated} generated plans " ++
    s!"({generatedTransactions} transactions) agree with Core from 3 initial storages; " ++
    s!"{loopFree} loop-free texts are outside the storage grammar")

end Tests.SourceStorageMeaning
end
