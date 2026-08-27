import Solcore.Core.Check
import Solcore.Core.DerivedComparisonEval
import Solcore.Core.Machine

/-! Semantic regressions for the derived boolean word comparisons. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def allocatingWritingWord
    (initial written result : Word) : Expr :=
  .letE
    (.newCell .word (.word initial))
    (.letE
      (.storeCell (.var 0) (.word written))
      (.word result))

private def zero : Word := Word.zero
private def one : Word := Word.ofNatModulo 1

example : HasType [] (Expr.wordNe (.word zero) (.word one)) .bool :=
  HasType.wordNe .word .word

example : HasType [] (Expr.wordLt (.word zero) (.word one)) .bool :=
  HasType.wordLt .word .word

example : HasType [] (Expr.wordLe (.word zero) (.word one)) .bool :=
  HasType.wordLe .word .word

example : HasType [] (Expr.wordGe (.word zero) (.word one)) .bool :=
  HasType.wordGe .word .word

example : infer? [] (Expr.wordNe (.word zero) (.word one)) = some .bool :=
  infer_wordNe rfl rfl

example : infer? [] (Expr.wordLt (.word zero) (.word one)) = some .bool :=
  infer_wordLt rfl rfl

example : infer? [] (Expr.wordLe (.word zero) (.word one)) = some .bool :=
  infer_wordLe rfl rfl

example : infer? [] (Expr.wordGe (.word zero) (.word one)) = some .bool :=
  infer_wordGe rfl rfl

example : Evaluates [] [] (Expr.wordNe (.word zero) (.word one)) (.bool true) [] :=
  Evaluates.wordNe_ne (by decide) .word .word

example : Evaluates [] [] (Expr.wordLe (.word zero) (.word one)) (.bool true) [] :=
  Evaluates.wordLe_not_gt (by decide) .word .word

example : Evaluates [] [] (Expr.wordLt (.word zero) (.word one)) (.bool true) [] :=
  Evaluates.wordLt_lt (definitions := [])
    (by decide) .word .word .word .word .nil .nil

example : Evaluates [] [] (Expr.wordGe (.word one) (.word zero)) (.bool true) [] :=
  Evaluates.wordGe_not_lt (definitions := [])
    (by decide) .word .word .word .word .nil .nil

private def booleanProgram (body : Expr) : Program := {
  resultType := .bool
  body
}

private def testValuesTypesAndFuel : IO Unit := do
  let zero := Word.zero
  let maximum := Word.maximum
  let cases : List (String × Program × Nat × Value) := [
    ("wordNe false", booleanProgram
      (Expr.wordNe (.word maximum) (.word maximum)), 7, .bool false),
    ("wordNe true", booleanProgram
      (Expr.wordNe (.word zero) (.word maximum)), 7, .bool true),
    ("wordLt true", booleanProgram
      (Expr.wordLt (.word zero) (.word maximum)), 11, .bool true),
    ("wordLt false", booleanProgram
      (Expr.wordLt (.word maximum) (.word zero)), 11, .bool false),
    ("wordLe true", booleanProgram
      (Expr.wordLe (.word zero) (.word maximum)), 7, .bool true),
    ("wordLe false", booleanProgram
      (Expr.wordLe (.word maximum) (.word zero)), 7, .bool false),
    ("wordGe true", booleanProgram
      (Expr.wordGe (.word maximum) (.word zero)), 13, .bool true),
    ("wordGe false", booleanProgram
      (Expr.wordGe (.word zero) (.word maximum)), 13, .bool false)
  ]
  for (name, program, exactFuel, expected) in cases do
    assertTrue program.check s!"{name} failed to type-check"
    assertTrue (program.run (exactFuel - 1) == .outOfFuel)
      s!"{name} finished below its exact fuel boundary"
    assertTrue (program.run exactFuel == .done expected)
      s!"{name} failed at its exact fuel boundary"

  for body in [
      Expr.wordNe .unit (.word zero), Expr.wordLt .unit (.word zero),
      Expr.wordLe (.word zero) .unit, Expr.wordGe (.word zero) .unit
    ] do
    let program : Program := { resultType := .bool, body }
    assertTrue (!program.check)
      s!"derived comparison accepted a non-word operand: {reprStr body}"

private def testLeftFirstFaults : IO Unit := do
  let one := Word.ofNatModulo 1
  let rightWithEffect := allocatingWritingWord Word.zero one Word.zero
  let neFault : Program := {
    resultType := .bool
    body := Expr.wordNe (.var 99) rightWithEffect
  }
  match neFault.runStateful 2 with
  | .fault (.unboundVariable 99) state =>
      assertTrue state.store.isEmpty
        "wordNe evaluated its right operand after a left fault"
  | result =>
      throw (IO.userError s!"wordNe exposed the wrong fault: {reprStr result}")

  let leFault : Program := {
    resultType := .bool
    body := Expr.wordLe (.var 99) rightWithEffect
  }
  match leFault.runStateful 2 with
  | .fault (.unboundVariable 99) state =>
      assertTrue state.store.isEmpty
        "wordLe evaluated its right operand after a left fault"
  | result =>
      throw (IO.userError s!"wordLe exposed the wrong fault: {reprStr result}")

  let ltFault : Program := {
    resultType := .bool
    body := Expr.wordLt (.var 99) rightWithEffect
  }
  match ltFault.runStateful 2 with
  | .fault (.unboundVariable 99) state =>
      assertTrue state.store.isEmpty
        "wordLt evaluated its right operand after a left fault"
  | result =>
      throw (IO.userError s!"wordLt exposed the wrong fault: {reprStr result}")

  let geFault : Program := {
    resultType := .bool
    body := Expr.wordGe (.var 99) rightWithEffect
  }
  match geFault.runStateful 3 with
  | .fault (.unboundVariable 99) state =>
      assertTrue state.store.isEmpty
        "wordGe evaluated its right operand after a left fault"
  | result =>
      throw (IO.userError s!"wordGe exposed the wrong fault: {reprStr result}")

private def testEffectOrder : IO Unit := do
  let one := Word.ofNatModulo 1
  let two := Word.ofNatModulo 2
  let left := allocatingWritingWord Word.zero one Word.maximum
  let right := allocatingWritingWord Word.zero two Word.zero
  let ne : Program := {
    resultType := .bool
    body := Expr.wordNe left right
  }
  let le : Program := {
    resultType := .bool
    body := Expr.wordLe left right
  }
  let lt : Program := {
    resultType := .bool
    body := Expr.wordLt left right
  }
  let ge : Program := {
    resultType := .bool
    body := Expr.wordGe left right
  }
  for (name, program) in [("wordNe", ne), ("wordLe", le),
      ("wordLt", lt), ("wordGe", ge)] do
    assertTrue program.check s!"effectful {name} failed to type-check"
  assertTrue
    (ne.runStateful 31 ==
      .done (.bool true) [.word one, .word two])
    "wordNe must evaluate and write left then right exactly once"
  assertTrue
    (le.runStateful 31 ==
      .done (.bool false) [.word one, .word two])
    "wordLe must evaluate and write left then right exactly once"
  assertTrue
    (lt.runStateful 35 ==
      .done (.bool false) [.word one, .word two])
    "wordLt must evaluate and write left then right exactly once"
  assertTrue
    (ge.runStateful 37 ==
      .done (.bool true) [.word one, .word two])
    "wordGe must evaluate and write left then right exactly once"

/-- Cover values, types, theorem interfaces, faults, effects, and exact fuel. -/
def testCoreDerivedComparisons : IO Unit := do
  testValuesTypesAndFuel
  testLeftFirstFaults
  testEffectOrder

end Tests
