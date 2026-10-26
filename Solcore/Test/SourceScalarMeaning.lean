import Solcore.Synthesis.Core.Generator
import Solcore.Synthesis.Source.ScalarMeaning.FunctionEmitter
import Solcore.Synthesis.Source.ScalarMeaning.PrimitiveEmitter
import Solcore.Test.SourceFunctionEmitter
import Solcore.Test.SourceInputEmitter
import Solcore.Test.SourcePrimitiveEmitter
import Solcore.Test.SourceSynthesisEmitter

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
  checkRejections
  let (checked, excluded) ← checkGenerated
  ensure (checked ≥ 16) s!"too few generated programs reached the source meaning: {checked}"
  let closed := Tests.SourceSynthesisEmitter.fixtures.length
  let inputs := Tests.SourceInputEmitter.fixtures.length
  let graphs := Tests.SourceFunctionEmitter.fixtures.length
  let primitives := Tests.SourcePrimitiveEmitter.fixtures.length + primitiveBoundaries.length
  IO.println (s!"scalar source meaning: {closed} closed fixtures, {inputs} input fixtures, " ++
    s!"{graphs} named-helper graphs and {primitives} raw primitive bodies x at least " ++
    s!"{boundaryInputs.length} inputs, {checked} generated programs ({excluded} excluded) " ++
    s!"agree with Core")

end Tests.SourceScalarMeaning
