import Solcore.Core.IntegerPrimitives
import Solcore.Core.Syntax

set_option autoImplicit false

namespace Solcore.Core

namespace Word

def maximum : Word :=
  ⟨wordModulus - 1, by decide⟩

def ofNatModulo (value : Nat) : Word :=
  ⟨value % wordModulus, Nat.mod_lt value (by decide)⟩

/-- Canonical projection of an arbitrary signed integer into an unsigned EVM
word.  Negative values use the same nonnegative remainder convention as
mathematical reduction modulo `2^256`; in particular, `-1` maps to
`Word.maximum`. -/
def ofIntModulo : Int → Word
  | .ofNat value => ofNatModulo value
  | .negSucc value =>
      ofNatModulo (wordModulus - ((value + 1) % wordModulus))

def add (left right : Word) : Word :=
  left + right

def sub (left right : Word) : Word :=
  left - right

def mul (left right : Word) : Word :=
  left * right

def addMod (left right modulus : Word) : Word :=
  if modulus.val = 0 then zero
  else ofNatModulo ((left.val + right.val) % modulus.val)

def mulMod (left right modulus : Word) : Word :=
  if modulus.val = 0 then zero
  else ofNatModulo ((left.val * right.val) % modulus.val)

def modularPowLoop (base accumulator exponent : Nat) : Nat :=
  if zero : exponent = 0 then
    accumulator % wordModulus
  else
    let accumulator :=
      if exponent % 2 = 1 then
        (accumulator * base) % wordModulus
      else
        accumulator % wordModulus
    modularPowLoop
      ((base * base) % wordModulus)
      accumulator
      (exponent / 2)
termination_by exponent
decreasing_by
  exact Nat.div_lt_self (Nat.zero_lt_of_ne_zero zero) (by decide)

def pow (base exponent : Word) : Word :=
  ofNatModulo (modularPowLoop base.val 1 exponent.val)

def udiv (left right : Word) : Word :=
  if right.val = 0 then zero else left / right

def umod (left right : Word) : Word :=
  if right.val = 0 then zero else left % right

def signedGt (left right : Word) : Bool :=
  if left.val < 2 ^ 255 then
    if right.val < 2 ^ 255 then decide (left > right)
    else true
  else
    if right.val < 2 ^ 255 then false
    else decide (left > right)

def bitAnd (left right : Word) : Word :=
  left &&& right

def bitOr (left right : Word) : Word :=
  left ||| right

def bitXor (left right : Word) : Word :=
  left ^^^ right

def bitNot (value : Word) : Word :=
  maximum - value

def clz (value : Word) : Word :=
  if value.val = 0 then ofNatModulo 256
  else ofNatModulo (255 - Nat.log2 value.val)

def shiftLeft (value shift : Word) : Word :=
  if shift.val < 256 then value <<< shift else zero

def shiftRight (value shift : Word) : Word :=
  if shift.val < 256 then value >>> shift else zero

def shiftArithmeticRight (value shift : Word) : Word :=
  if shift.val < 256 then
    if value.val < 2 ^ 255 then
      ofNatModulo (value.val / 2 ^ shift.val)
    else
      ofNatModulo
        (wordModulus - 1 -
          ((wordModulus - 1 - value.val) / 2 ^ shift.val))
  else if value.val < 2 ^ 255 then
    zero
  else
    maximum

def byteAt (index value : Word) : Word :=
  if index.val < 32 then
    ofNatModulo ((value.val / 2 ^ (8 * (31 - index.val))) % 256)
  else
    zero

def signExtend (index value : Word) : Word :=
  if index.val < 32 then
    let width := 8 * (index.val + 1)
    let low := value.val % 2 ^ width
    let sign := 2 ^ (width - 1)
    if low < sign then
      ofNatModulo low
    else
      ofNatModulo (wordModulus - 2 ^ width + low)
  else
    value

def signedNegative (value : Word) : Bool :=
  decide (2 ^ 255 ≤ value.val)

def signedMagnitude (value : Word) : Nat :=
  if value.signedNegative then wordModulus - value.val else value.val

def ofSignedMagnitude (negative : Bool) (magnitude : Nat) : Word :=
  if negative then ofNatModulo (wordModulus - magnitude)
  else ofNatModulo magnitude

def sdiv (dividend divisor : Word) : Word :=
  if divisor.val = 0 then
    zero
  else
    ofSignedMagnitude
      (dividend.signedNegative != divisor.signedNegative)
      (dividend.signedMagnitude / divisor.signedMagnitude)

def smod (dividend divisor : Word) : Word :=
  if divisor.val = 0 then
    zero
  else
    ofSignedMagnitude dividend.signedNegative
      (dividend.signedMagnitude % divisor.signedMagnitude)

end Word

namespace UnaryOp

def apply : UnaryOp → Value → Option Value
  | .boolNot, .bool value => some (.bool (!value))
  | .wordNot, .word value => some (.word value.bitNot)
  | .wordClz, .word value => some (.word value.clz)
  | .integerNot, .integer value => some (.integer (~~~value))
  | .integerToWord, .integer value => some (.word (Word.ofIntModulo value))
  | .wordToInteger, .word value => some (.integer (Int.ofNat value.val))
  | _, _ => none

theorem apply_total_of_type
    (op : UnaryOp)
    (operand : Value)
    (operandType : operand.type = op.operandType) :
    ∃ result,
      op.apply operand = some result ∧
      result.type = op.resultType := by
  cases op <;> cases operand <;>
    simp_all [apply, UnaryOp.operandType, UnaryOp.resultType, Value.type]

theorem apply_result_type
    {op : UnaryOp}
    {operand result : Value}
    (applied : op.apply operand = some result) :
    result.type = op.resultType := by
  cases op <;> cases operand <;>
    simp [apply] at applied <;>
    cases applied <;> rfl

end UnaryOp

namespace BinaryOp

def apply : BinaryOp → Value → Value → Option Value
  | .wordAdd, .word left, .word right => some (.word (left.add right))
  | .wordSub, .word left, .word right => some (.word (left.sub right))
  | .wordMul, .word left, .word right => some (.word (left.mul right))
  | .wordDiv, .word left, .word right => some (.word (left.udiv right))
  | .wordMod, .word left, .word right => some (.word (left.umod right))
  | .wordEq, .word left, .word right => some (.bool (left == right))
  | .wordGt, .word left, .word right => some (.bool (decide (left > right)))
  | .wordSgt, .word left, .word right => some (.bool (left.signedGt right))
  | .wordAnd, .word left, .word right => some (.word (left.bitAnd right))
  | .wordOr, .word left, .word right => some (.word (left.bitOr right))
  | .wordXor, .word left, .word right => some (.word (left.bitXor right))
  | .wordShl, .word value, .word shift => some (.word (value.shiftLeft shift))
  | .wordShr, .word value, .word shift => some (.word (value.shiftRight shift))
  | .wordByte, .word index, .word value => some (.word (index.byteAt value))
  | .wordSar, .word value, .word shift =>
      some (.word (value.shiftArithmeticRight shift))
  | .wordPow, .word base, .word exponent => some (.word (base.pow exponent))
  | .wordSignExtend, .word index, .word value =>
      some (.word (index.signExtend value))
  | .wordSdiv, .word dividend, .word divisor =>
      some (.word (dividend.sdiv divisor))
  | .wordSmod, .word dividend, .word divisor =>
      some (.word (dividend.smod divisor))
  | .integerAdd, .integer left, .integer right => some (.integer (left + right))
  | .integerSub, .integer left, .integer right => some (.integer (left - right))
  | .integerMul, .integer left, .integer right => some (.integer (left * right))
  | .integerDiv, .integer left, .integer right => some (.integer (Integer.divide left right))
  | .integerMod, .integer left, .integer right => some (.integer (Integer.modulo left right))
  | .integerAnd, .integer left, .integer right => some (.integer (Integer.bitAnd left right))
  | .integerOr, .integer left, .integer right => some (.integer (Integer.bitOr left right))
  | .integerXor, .integer left, .integer right => some (.integer (Integer.bitXor left right))
  | .integerEq, .integer left, .integer right => some (.bool (left == right))
  | .integerLt, .integer left, .integer right => some (.bool (decide (left < right)))
  | _, _, _ => none

theorem apply_total_of_types
    (op : BinaryOp)
    (left right : Value)
    (leftType : left.type = op.leftType)
    (rightType : right.type = op.rightType) :
    ∃ result,
      op.apply left right = some result ∧
      result.type = op.resultType := by
  cases op <;> cases left <;> cases right <;>
    simp_all [
      apply,
      BinaryOp.leftType,
      BinaryOp.rightType,
      BinaryOp.resultType,
      Value.type
    ]

theorem apply_result_type
    {op : BinaryOp}
    {left right result : Value}
    (applied : op.apply left right = some result) :
    result.type = op.resultType := by
  cases op <;> cases left <;> cases right <;>
    simp [apply] at applied <;>
    cases applied <;> rfl

end BinaryOp

namespace TernaryOp

def apply : TernaryOp → Value → Value → Value → Option Value
  | .wordAddMod, .word left, .word right, .word modulus =>
      some (.word (left.addMod right modulus))
  | .wordMulMod, .word left, .word right, .word modulus =>
      some (.word (left.mulMod right modulus))
  | _, _, _, _ => none

theorem apply_total_of_types
    (op : TernaryOp)
    (first second third : Value)
    (firstType : first.type = op.firstType)
    (secondType : second.type = op.secondType)
    (thirdType : third.type = op.thirdType) :
    ∃ result,
      op.apply first second third = some result ∧
      result.type = op.resultType := by
  cases op <;> cases first <;> cases second <;> cases third <;>
    simp_all [apply, TernaryOp.firstType, TernaryOp.secondType,
      TernaryOp.thirdType, TernaryOp.resultType, Value.type]

theorem apply_result_type
    {op : TernaryOp}
    {first second third result : Value}
    (applied : op.apply first second third = some result) :
    result.type = op.resultType := by
  cases op <;> cases first <;> cases second <;> cases third <;>
    simp [apply] at applied <;>
    cases applied <;> rfl

end TernaryOp

namespace Expr

def weakenAt (expr : Expr) (cutoff : Nat) : Expr :=
  match expr with
  | .unit => .unit
  | .bool value => .bool value
  | .word value => .word value
  | .integer value => .integer value
  | .var index =>
      if cutoff ≤ index then .var (index + 1) else .var index
  | .pair left right =>
      .pair (left.weakenAt cutoff) (right.weakenAt cutoff)
  | .first operand => .first (operand.weakenAt cutoff)
  | .second operand => .second (operand.weakenAt cutoff)
  | .lambda parameterType resultType body =>
      .lambda parameterType resultType (body.weakenAt (cutoff + 1))
  | .apply function argument =>
      .apply (function.weakenAt cutoff) (argument.weakenAt cutoff)
  | .inLeft rightType payload =>
      .inLeft rightType (payload.weakenAt cutoff)
  | .inRight leftType payload =>
      .inRight leftType (payload.weakenAt cutoff)
  | .caseE scrutinee leftBranch rightBranch =>
      .caseE
        (scrutinee.weakenAt cutoff)
        (leftBranch.weakenAt (cutoff + 1))
        (rightBranch.weakenAt (cutoff + 1))
  | .newCell elementType initializer =>
      .newCell elementType (initializer.weakenAt cutoff)
  | .loadCell reference => .loadCell (reference.weakenAt cutoff)
  | .storeCell reference value =>
      .storeCell (reference.weakenAt cutoff) (value.weakenAt cutoff)
  | .construct constructor payload =>
      .construct constructor (payload.weakenAt cutoff)
  | .matchData dataType resultType scrutinee branches =>
      .matchData
        dataType
        resultType
        (scrutinee.weakenAt cutoff)
        (branches.map fun branch => branch.weakenAt (cutoff + 1))
  | .unary op operand => .unary op (operand.weakenAt cutoff)
  | .binary op left right =>
      .binary op (left.weakenAt cutoff) (right.weakenAt cutoff)
  | .ternary op firstExpr secondExpr thirdExpr =>
      .ternary op (firstExpr.weakenAt cutoff) (secondExpr.weakenAt cutoff)
        (thirdExpr.weakenAt cutoff)
  | .letE value body =>
      .letE (value.weakenAt cutoff) (body.weakenAt (cutoff + 1))
  | .ifE condition thenBranch elseBranch =>
      .ifE
        (condition.weakenAt cutoff)
        (thenBranch.weakenAt cutoff)
        (elseBranch.weakenAt cutoff)

private def wordGtWithSwappedValues (left right : Expr) : Expr :=
  .letE left
    (.letE (right.weakenAt 0)
      (.binary .wordGt (.var 0) (.var 1)))

private def wordSgtWithSwappedValues (left right : Expr) : Expr :=
  .letE left
    (.letE (right.weakenAt 0)
      (.binary .wordSgt (.var 0) (.var 1)))

def wordNe (left right : Expr) : Expr :=
  .unary .boolNot (.binary .wordEq left right)

def boolToWord (value : Expr) : Expr :=
  .ifE value (.word (Word.ofNatModulo 1)) (.word Word.zero)

def wordToBool (value : Expr) : Expr :=
  wordNe value (.word Word.zero)

def wordIsZero (value : Expr) : Expr :=
  boolToWord (.binary .wordEq value (.word Word.zero))

def wordIsNonzero (value : Expr) : Expr :=
  boolToWord (wordToBool value)

def wordEqFlag (left right : Expr) : Expr :=
  boolToWord (.binary .wordEq left right)

def wordGtFlag (left right : Expr) : Expr :=
  boolToWord (.binary .wordGt left right)

def wordSgtFlag (left right : Expr) : Expr :=
  boolToWord (.binary .wordSgt left right)

def wordLt (left right : Expr) : Expr :=
  wordGtWithSwappedValues left right

def wordSlt (left right : Expr) : Expr :=
  wordSgtWithSwappedValues left right

def wordSle (left right : Expr) : Expr :=
  .unary .boolNot (.binary .wordSgt left right)

def wordSge (left right : Expr) : Expr :=
  .unary .boolNot (wordSlt left right)

def wordLe (left right : Expr) : Expr :=
  .unary .boolNot (.binary .wordGt left right)

def wordGe (left right : Expr) : Expr :=
  .unary .boolNot (wordGtWithSwappedValues left right)

def wordNeFlag (left right : Expr) : Expr :=
  boolToWord (wordNe left right)

def wordLtFlag (left right : Expr) : Expr :=
  boolToWord (wordLt left right)

def wordSltFlag (left right : Expr) : Expr :=
  boolToWord (wordSlt left right)

def wordSleFlag (left right : Expr) : Expr :=
  boolToWord (wordSle left right)

def wordSgeFlag (left right : Expr) : Expr :=
  boolToWord (wordSge left right)

def wordLeFlag (left right : Expr) : Expr :=
  boolToWord (wordLe left right)

def wordGeFlag (left right : Expr) : Expr :=
  boolToWord (wordGe left right)

end Expr

end Solcore.Core
