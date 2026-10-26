import Solcore.Synthesis.Core.Generator
import Solcore.Synthesis.Source.ScalarMeaning.FunctionEmitter
import Solcore.Test.SourceFunctionEmitter
import Solcore.Test.SourceInputEmitter
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
    | .error error => throw (IO.userError s!"named-helper emission failed: {label}: {reprStr error}")
  checkReprint label emitted.source
  for input in boundaryInputs do
    let expected ← coreWord (graph.instantiate (Word.ofNatModulo input)).toCore
    ensure (sourceCall emitted.source "run" [input] == some expected)
      s!"named-helper source meaning differs from Core: {label} at {input}"
  let undeclared := emitted.source.replace "= sc_fn0(" "= sc_fnx("
  ensure (undeclared != emitted.source) s!"named-helper fixture has no call to sc_fn0: {label}"
  ensure ((parseSource undeclared).isSome && sourceCall undeclared "run" [1] == none)
    s!"a call to an undeclared helper received a meaning: {label}"

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
  checkRejections
  let (checked, excluded) ← checkGenerated
  ensure (checked ≥ 16) s!"too few generated programs reached the source meaning: {checked}"
  let closed := Tests.SourceSynthesisEmitter.fixtures.length
  let inputs := Tests.SourceInputEmitter.fixtures.length
  let graphs := Tests.SourceFunctionEmitter.fixtures.length
  IO.println (s!"scalar source meaning: {closed} closed fixtures, {inputs} input fixtures and " ++
    s!"{graphs} named-helper graphs x {boundaryInputs.length} inputs, {checked} generated " ++
    s!"programs ({excluded} excluded) agree with Core")

end Tests.SourceScalarMeaning
