import Solcore.Synthesis.CoreV3.Fragment

/-! Focused regressions for the checked Core v3 synthesis fragment. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Core.Wire
open Solcore.Synthesis.CoreV3

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def zero : V3.Expr :=
  .word Word.zero

private def literalProgram : V3.Program := {
  resultType := .word
  dataDefinitions := []
  body := zero
}

private def boolResultProgram : V3.Program := {
  resultType := .bool
  dataDefinitions := []
  body := .bool true
}

private def definitionProgram : V3.Program := {
  resultType := .word
  dataDefinitions := [{ constructorPayloadTypes := [] }]
  body := zero
}

private def hostProgram : V3.Program := {
  resultType := .word
  dataDefinitions := []
  body := .apply (.var 0) zero
}

example : accepts .word zero = true := by
  decide

example : accepts .bool (.bool false) = true := by
  decide

example : accepts .word (.var 0) = false := by
  decide

example : acceptsAt 1 .word (.var 0) = true := by
  decide

example : acceptsAt 1 .word (.var 1) = false := by
  decide

example : accepts .bool zero = false := by
  decide

example : accepts .word (.pair zero zero) = false := by
  decide

example : literalProgram.check = true := by
  native_decide

private def featureWitness : Feature → Nat × Target × V3.Expr
  | .wordLiteral => (0, .word, zero)
  | .local => (1, .word, .var 0)
  | .boolLiteral => (0, .bool, .bool true)
  | .letE => (0, .word, .letE zero (.var 0))
  | .ifE => (0, .word, .ifE (.bool true) zero zero)
  | .unary op =>
      let operand := match Target.unaryOperand op with
        | .word => zero
        | .bool => .bool true
      (0, Target.unaryResult op, .unary op operand)
  | .binary op =>
      (0, Target.binaryResult op, .binary op zero zero)
  | .ternary op =>
      (0, .word, .ternary op zero zero zero)

private def featureHasBasicWitness (feature : Feature) : Bool :=
  let (depth, target, expression) := featureWitness feature
  acceptsAt depth target expression && (features expression).contains feature

private def catalogHasNoDuplicates : Bool :=
  Feature.catalog.toList.eraseDups.length == Feature.catalog.size

def testCoreV3SynthesisFragment : IO Unit := do
  assertTrue (accepts .word zero)
    "the synthesis fragment rejected a Word literal"
  assertTrue (accepts .bool (.bool true))
    "the synthesis fragment rejected a Bool literal"
  assertTrue (acceptsAt 1 .word (.var 0))
    "the synthesis fragment rejected an in-scope Word local"
  assertTrue (!accepts .word (.var 0))
    "the synthesis fragment admitted the first root host variable"
  assertTrue (!acceptsAt 1 .word (.var 1))
    "the synthesis fragment admitted a host variable after a local binder"
  assertTrue (!accepts .bool zero && !accepts .word (.bool true))
    "the synthesis fragment accepted a literal at the wrong target type"
  assertTrue
    (!accepts .word (.unary .boolNot (.bool true)) &&
      !accepts .bool (.binary .wordAdd zero zero))
    "the synthesis fragment accepted an operator at the wrong result type"
  assertTrue
    (!accepts .word (.unit) &&
      !accepts .word (.pair zero zero) &&
      !accepts .word (.apply (.var 0) zero))
    "a constructor outside the synthesis fragment was admitted"
  assertTrue (Feature.catalog.size == 29)
    "the frozen synthesis feature catalog changed size"
  assertTrue catalogHasNoDuplicates
    "the frozen synthesis feature catalog contains a duplicate"
  assertTrue (Feature.catalog.all featureHasBasicWitness)
    "a catalog feature lacks an accepted expression witness"
  match CheckedWordProgram.ofProgram? literalProgram with
  | none =>
      throw (IO.userError "the checked fragment rejected its basic program")
  | some code =>
      assertTrue (code.program.check && accepts .word code.program.body)
        "checked fragment evidence did not retain the admitted program"
  assertTrue (CheckedWordProgram.ofProgram? boolResultProgram).isNone
    "checked fragment admission accepted a non-Word program"
  assertTrue (CheckedWordProgram.ofProgram? definitionProgram).isNone
    "checked fragment admission accepted named-data definitions"
  assertTrue (CheckedWordProgram.ofProgram? hostProgram).isNone
    "checked fragment admission accepted a host expression"

end Tests
