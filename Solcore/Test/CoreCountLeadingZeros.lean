import Solcore.Core.CountLeadingZeros
import Solcore.Core.Check
import Solcore.Core.Machine

/-! Focused proof and runtime regressions for internal word count-leading-zeros. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def zero : Word := Word.zero
private def one : Word := Word.ofNatModulo 1
private def two : Word := Word.ofNatModulo 2
private def highBit : Word := Word.ofNatModulo (2 ^ 255)
private def count256 : Word := Word.ofNatModulo 256
private def count255 : Word := Word.ofNatModulo 255
private def count254 : Word := Word.ofNatModulo 254

example : zero.clz = count256 := Word.clz_zero
example (value : Word) (nonzero : value.val ≠ 0) :
    value.clz = Word.ofNatModulo (255 - Nat.log2 value.val) :=
  Word.clz_nonzero value nonzero
example : one.clz = count255 := Word.clz_one
example : highBit.clz = zero := Word.clz_highBit
example : Word.maximum.clz = zero := Word.clz_maximum

example : UnaryOp.wordClz.apply (.word two) = some (.word two.clz) :=
  UnaryOp.apply_wordClz two
example : Evaluates [] [] (.unary .wordClz (.word two)) (.word two.clz) [] :=
  Evaluates.wordClz .word
example : Evaluates [] [] (.unary .wordClz (.word zero))
    (.word count256) [] :=
  Evaluates.wordClz_zero .word
example : Evaluates [] [] (.unary .wordClz (.word one))
    (.word count255) [] :=
  Evaluates.wordClz_one .word
example : Evaluates [] [] (.unary .wordClz (.word highBit)) (.word zero) [] :=
  Evaluates.wordClz_highBit .word
example : Evaluates [] [] (.unary .wordClz (.word Word.maximum))
    (.word zero) [] :=
  Evaluates.wordClz_maximum .word

private def wordProgram (body : Expr) : Program := {
  resultType := .word
  body
}

private def allocatingWritingWord
    (initial written result : Word) : Expr :=
  .letE
    (.newCell .word (.word initial))
    (.letE
      (.storeCell (.var 0) (.word written))
      (.word result))

private def testValuesTypesAndLiteralFuel : IO Unit := do
  let cases : List (String × Word × Word) := [
    ("zero", zero, count256),
    ("one", one, count255),
    ("two", two, count254),
    ("high bit", highBit, zero),
    ("maximum", Word.maximum, zero)
  ]
  for (name, input, expected) in cases do
    let witness := wordProgram (.unary .wordClz (.word input))
    assertTrue witness.check s!"wordClz {name} failed to type-check as word"
    assertTrue (witness.run 2 == .outOfFuel)
      s!"wordClz {name} finished below the literal fuel boundary"
    assertTrue (witness.run 3 == .done (.word expected))
      s!"wordClz {name} failed at the literal fuel boundary"

  let validBody : Expr := .unary .wordClz (.word two)
  let wrongResult : Program := { resultType := .bool, body := validBody }
  assertTrue (!wrongResult.check) "wordClz accepted a boolean result type"

  let wrongOperand : Expr := .unary .wordClz (.bool true)
  assertTrue (!(wordProgram wrongOperand).check)
    "wordClz accepted a boolean operand"
  assertTrue
    ((wordProgram wrongOperand).run 2 ==
      .fault (.invalidUnaryOperand .wordClz (.bool true)))
    "raw wordClz did not expose its invalid boolean operand"

private def testEffectfulOperand : IO Unit := do
  let operand := allocatingWritingWord zero one highBit
  let witness := wordProgram (.unary .wordClz operand)
  assertTrue witness.check "effectful wordClz failed to type-check"
  assertTrue (witness.run 14 == .outOfFuel)
    "effectful wordClz finished below exact fuel"
  assertTrue
    (witness.runStateful 15 == .done (.word zero) [.word one])
    "wordClz did not evaluate its operand exactly once or retain the final store"

/-- Cover all eleven theorems plus values, types, fault, effect, store, and fuel. -/
def testCoreCountLeadingZeros : IO Unit := do
  testValuesTypesAndLiteralFuel
  testEffectfulOperand

end Tests
