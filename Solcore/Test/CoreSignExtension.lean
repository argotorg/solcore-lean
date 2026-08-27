import Solcore.Core.SignExtension
import Solcore.Core.Check
import Solcore.Core.Machine

/-! Focused proof and runtime regressions for internal word sign extension. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Word := Word.ofNatModulo value
private def zero : Word := Word.zero
private def one : Word := word 1
private def two : Word := word 2

example : (word 0).signExtend (word 0x7f) = word 0x7f :=
  Word.signExtend_clear (word 0) (word 0x7f) (by decide) (by decide)
example : (word 0).signExtend (word 0x80) = word (wordModulus - 128) :=
  Word.signExtend_set (word 0) (word 0x80) (by decide) (by decide)
example : (word 32).signExtend (word 0x1122) = word 0x1122 :=
  Word.signExtend_ge_32 (word 32) (word 0x1122) (by decide)
example : (word 7).signExtend zero = zero := Word.signExtend_zero (word 7)
example : (word 31).signExtend (word 0x1122) = word 0x1122 :=
  Word.signExtend_index31 (word 0x1122)

example : BinaryOp.wordSignExtend.apply (.word (word 0)) (.word (word 0x80)) =
    some (.word ((word 0).signExtend (word 0x80))) :=
  BinaryOp.apply_wordSignExtend (word 0) (word 0x80)
example : Evaluates [] []
    (.binary .wordSignExtend (.word (word 0)) (.word (word 0x80)))
    (.word ((word 0).signExtend (word 0x80))) [] :=
  Evaluates.wordSignExtend .word .word
example : Evaluates [] []
    (.binary .wordSignExtend (.word (word 0)) (.word (word 0x7f)))
    (.word (word 0x7f)) [] :=
  Evaluates.wordSignExtend_clear (by decide) (by decide) .word .word
example : Evaluates [] []
    (.binary .wordSignExtend (.word (word 0)) (.word (word 0x80)))
    (.word (word (wordModulus - 128))) [] :=
  Evaluates.wordSignExtend_set (by decide) (by decide) .word .word
example : Evaluates [] []
    (.binary .wordSignExtend (.word (word 32)) (.word (word 0x1122)))
    (.word (word 0x1122)) [] :=
  Evaluates.wordSignExtend_ge_32 (by decide) .word .word

private def wordProgram (body : Expr) : Program := { resultType := .word, body }

private def allocatingWritingWord (initial written result : Word) : Expr :=
  .letE (.newCell .word (.word initial))
    (.letE (.storeCell (.var 0) (.word written)) (.word result))

private def testValuesTypesAndFuel : IO Unit := do
  let arbitrary := word 0x123456
  let cases : List (String × Word × Word × Word) := [
    ("index 0 clear", word 0, word 0x7f, word 0x7f),
    ("index 0 set", word 0, word 0x80, word (wordModulus - 128)),
    ("index 0 ff", word 0, word 0xff, Word.maximum),
    ("index 0 truncates clear", word 0, word 0x1234, word 0x34),
    ("index 0 truncates set", word 0, word 0x1280, word (wordModulus - 128)),
    ("index 1 clear", word 1, word 0x7fff, word 0x7fff),
    ("index 1 set", word 1, word 0x8000, word (wordModulus - 32768)),
    ("index 31 zero", word 31, zero, zero),
    ("index 31 maximum", word 31, Word.maximum, Word.maximum),
    ("index 31 arbitrary", word 31, arbitrary, arbitrary),
    ("index 32 identity", word 32, arbitrary, arbitrary),
    ("maximum index identity", Word.maximum, arbitrary, arbitrary)
  ]
  for (name, index, value, expected) in cases do
    let witness := wordProgram (.binary .wordSignExtend (.word index) (.word value))
    assertTrue witness.check s!"wordSignExtend {name} failed to type-check"
    assertTrue (witness.run 4 == .outOfFuel)
      s!"wordSignExtend {name} finished below exact fuel"
    assertTrue (witness.run 5 == .done (.word expected))
      s!"wordSignExtend {name} failed at exact fuel"

  let validBody : Expr :=
    .binary .wordSignExtend (.word (word 0)) (.word (word 0x80))
  let wrongResult : Program := { resultType := .bool, body := validBody }
  assertTrue (!wrongResult.check) "wordSignExtend accepted bool result"
  let wrongLeft : Expr := .binary .wordSignExtend .unit (.word (word 0x80))
  let wrongRight : Expr := .binary .wordSignExtend (.word zero) .unit
  assertTrue (!(wordProgram wrongLeft).check) "wordSignExtend accepted bad index"
  assertTrue (!(wordProgram wrongRight).check) "wordSignExtend accepted bad value"
  assertTrue ((wordProgram wrongLeft).run 5 ==
    .fault (.invalidBinaryOperands .wordSignExtend .unit (.word (word 0x80))))
    "wordSignExtend invalid left payload changed"
  assertTrue ((wordProgram wrongRight).run 5 ==
    .fault (.invalidBinaryOperands .wordSignExtend (.word zero) .unit))
    "wordSignExtend invalid right payload changed"

private def testFaultOrder : IO Unit := do
  let effectfulValue := allocatingWritingWord zero one (word 0x80)
  match (wordProgram (.binary .wordSignExtend (.var 99) effectfulValue)).runStateful 8 with
  | .fault (.unboundVariable 99) state =>
      assertTrue state.store.isEmpty "wordSignExtend evaluated value after index fault"
  | result => throw (IO.userError s!"wordSignExtend wrong index fault: {reprStr result}")

  let effectfulIndex := allocatingWritingWord zero one zero
  match (wordProgram (.binary .wordSignExtend effectfulIndex (.var 100))).runStateful 64 with
  | .fault (.unboundVariable 100) state =>
      assertTrue (state.store == [.word one])
        "wordSignExtend value fault did not retain index store"
  | result => throw (IO.userError s!"wordSignExtend wrong value fault: {reprStr result}")

private def testEffects : IO Unit := do
  let index := allocatingWritingWord zero one zero
  let value := allocatingWritingWord zero two (word 0x80)
  let witness := wordProgram (.binary .wordSignExtend index value)
  assertTrue witness.check "effectful wordSignExtend failed to type-check"
  assertTrue (witness.run 28 == .outOfFuel)
    "effectful wordSignExtend finished below exact fuel"
  assertTrue (witness.runStateful 29 ==
    .done (.word (word (wordModulus - 128))) [.word one, .word two])
    "wordSignExtend did not evaluate index then value once or retain final store"

/-- Cover all ten theorems plus values, types, faults, effects, store, and fuel. -/
def testCoreSignExtension : IO Unit := do
  testValuesTypesAndFuel
  testFaultOrder
  testEffects

end Tests
