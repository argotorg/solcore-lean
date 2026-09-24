import Solcore.Core.Wire.Codec.ExprEncoding

/-! Exact typed-node demand for Wire expressions. -/

set_option autoImplicit false

namespace Solcore.Core.Wire

private def max3 (first second third : Nat) : Nat :=
  Nat.max first (Nat.max second third)

mutual

  def exprDepth : Expr → Nat
    | .unit | .bool _ | .word _ | .var _ => 1
    | .pair left right | .apply left right | .storeCell left right |
        .binary _ left right | .letE left right =>
        Nat.max (exprDepth left) (exprDepth right) + 1
    | .first operand | .second operand | .loadCell operand |
        .construct _ operand | .unary _ operand =>
        exprDepth operand + 1
    | .lambda parameterType resultType body =>
        max3 (typeDepth parameterType) (typeDepth resultType) (exprDepth body) + 1
    | .inLeft rightType payload | .inRight rightType payload |
        .newCell rightType payload =>
        Nat.max (typeDepth rightType) (exprDepth payload) + 1
    | .caseE scrutinee leftBranch rightBranch =>
        max3 (exprDepth scrutinee) (exprDepth leftBranch)
          (exprDepth rightBranch) + 1
    | .matchData _ resultType scrutinee branches =>
        max3 (typeDepth resultType) (exprDepth scrutinee)
          (exprListDepth branches) + 1
    | .ternary _ first second third | .ifE first second third =>
        max3 (exprDepth first) (exprDepth second) (exprDepth third) + 1
  termination_by expression => sizeOf expression

  def exprListDepth : List Expr → Nat
    | [] => 0
    | expression :: rest =>
        Nat.max (exprDepth expression) (exprListDepth rest)
  termination_by expressions => sizeOf expressions

end

mutual

  def exprNodes : Expr → Nat
    | .unit | .bool _ | .word _ | .var _ => 1
    | .pair left right | .apply left right | .storeCell left right |
        .binary _ left right | .letE left right =>
        1 + exprNodes left + exprNodes right
    | .first operand | .second operand | .loadCell operand |
        .construct _ operand | .unary _ operand =>
        1 + exprNodes operand
    | .lambda parameterType resultType body =>
        1 + typeNodes parameterType + typeNodes resultType + exprNodes body
    | .inLeft rightType payload | .inRight rightType payload |
        .newCell rightType payload =>
        1 + typeNodes rightType + exprNodes payload
    | .caseE scrutinee leftBranch rightBranch =>
        1 + exprNodes scrutinee + exprNodes leftBranch + exprNodes rightBranch
    | .matchData _ resultType scrutinee branches =>
        1 + typeNodes resultType + exprNodes scrutinee + exprListNodes branches
    | .ternary _ first second third | .ifE first second third =>
        1 + exprNodes first + exprNodes second + exprNodes third
  termination_by expression => sizeOf expression

  def exprListNodes : List Expr → Nat
    | [] => 0
    | expression :: rest => exprNodes expression + exprListNodes rest
  termination_by expressions => sizeOf expressions

end

@[simp] theorem exprDepth_positive (expression : Expr) :
    0 < exprDepth expression := by
  cases expression <;> simp [exprDepth]

@[simp] theorem exprNodes_positive (expression : Expr) :
  0 < exprNodes expression := by
  cases expression <;> simp [exprNodes] <;> omega

end Solcore.Core.Wire
