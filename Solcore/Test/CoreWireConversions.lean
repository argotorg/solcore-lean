import Solcore.Core.Wire.Conversions

/-! Independent executable consumers of the canonical Core wire projection. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def dataType : Wire.DataTypeId := ⟨0⟩
private def constructor : Wire.ConstructorId := ⟨dataType, 0⟩

private def types : Array Wire.Ty := #[
  .unit,
  .bool,
  .word,
  .product .word .bool,
  .function .word .word,
  .sum .unit .word,
  .cell (.product .word .word),
  .namedData dataType
]

private def expressions : Array Wire.Expr := #[
  .unit,
  .bool true,
  .word Word.zero,
  .var 14,
  .pair (.word Word.zero) (.bool false),
  .first (.var 0),
  .second (.var 0),
  .lambda .word .word (.var 0),
  .apply (.var 0) (.word Word.zero),
  .inLeft .word .unit,
  .inRight .unit (.word Word.zero),
  .caseE (.var 0) (.var 0) (.var 0),
  .newCell .word (.word Word.zero),
  .loadCell (.var 0),
  .storeCell (.var 0) (.word Word.zero),
  .construct constructor (.word Word.zero),
  .matchData dataType .word (.var 0) [(.var 0), (.word Word.zero)],
  .unary .wordClz (.word Word.zero),
  .binary .wordSdiv (.word Word.zero) (.word Word.zero),
  .ternary .wordAddMod (.word Word.zero) (.word Word.zero) (.word Word.zero),
  .letE (.word Word.zero) (.var 0),
  .ifE (.bool true) (.word Word.zero) (.word Word.zero)
]

private def unaryOps : Array Wire.UnaryOp := #[
  .boolNot, .wordNot, .wordClz
]

private def binaryOps : Array Wire.BinaryOp := #[
  .wordAdd, .wordSub, .wordMul, .wordDiv, .wordMod,
  .wordEq, .wordGt, .wordSgt, .wordAnd, .wordOr, .wordXor,
  .wordShl, .wordShr, .wordByte, .wordSar, .wordPow,
  .wordSignExtend, .wordSdiv, .wordSmod
]

private def ternaryOps : Array Wire.TernaryOp := #[
  .wordAddMod, .wordMulMod
]

private def program : Wire.Program := {
  resultType := .namedData dataType
  dataDefinitions := [⟨[.word, .product .word .bool]⟩]
  body := .construct constructor (.word Word.zero)
}

private theorem compileTimeProgramRoundTrip :
    Wire.Program.ofCore? program.toCore = some program := by
  simp

private def allRoundTrips : Bool :=
  (types.all fun type => Wire.Ty.ofCore? type.toCore == some type) &&
  (expressions.all fun expression =>
    Wire.Expr.ofCore? expression.toCore == some expression) &&
  (unaryOps.all fun op => Wire.UnaryOp.ofCore? op.toCore == some op) &&
  (binaryOps.all fun op => Wire.BinaryOp.ofCore? op.toCore == some op) &&
  (ternaryOps.all fun op => Wire.TernaryOp.ofCore? op.toCore == some op) &&
  (Wire.Program.ofCore? program.toCore == some program)

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

def testCoreWireConversions : IO Unit := do
  assertTrue allRoundTrips
    "Core wire stopped round-tripping a published constructor"

end Tests
