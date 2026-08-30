import Solcore.Core.Wire.V3.Codec.DataDefinition

/-! Canonical JSON encoding for every closed Wire v3 expression. -/

set_option autoImplicit false

namespace Solcore.Core.Wire.V3

def encodeExpr : Expr → Lean.Json
  | .unit => .mkObj [("tag", "unit")]
  | .bool value => .mkObj [("tag", "bool"), ("value", value)]
  | .word value =>
      .mkObj [("tag", "word"), ("value", encodeWord value)]
  | .var index => .mkObj [("tag", "var"), ("index", index)]
  | .pair left right =>
      .mkObj [
        ("tag", "pair"),
        ("left", encodeExpr left),
        ("right", encodeExpr right)
      ]
  | .first operand =>
      .mkObj [("tag", "first"), ("operand", encodeExpr operand)]
  | .second operand =>
      .mkObj [("tag", "second"), ("operand", encodeExpr operand)]
  | .lambda parameterType resultType body =>
      .mkObj [
        ("tag", "lambda"),
        ("parameterType", encodeType parameterType),
        ("resultType", encodeType resultType),
        ("body", encodeExpr body)
      ]
  | .apply function argument =>
      .mkObj [
        ("tag", "apply"),
        ("function", encodeExpr function),
        ("argument", encodeExpr argument)
      ]
  | .inLeft rightType payload =>
      .mkObj [
        ("tag", "inLeft"),
        ("rightType", encodeType rightType),
        ("payload", encodeExpr payload)
      ]
  | .inRight leftType payload =>
      .mkObj [
        ("tag", "inRight"),
        ("leftType", encodeType leftType),
        ("payload", encodeExpr payload)
      ]
  | .caseE scrutinee leftBranch rightBranch =>
      .mkObj [
        ("tag", "case"),
        ("scrutinee", encodeExpr scrutinee),
        ("leftBranch", encodeExpr leftBranch),
        ("rightBranch", encodeExpr rightBranch)
      ]
  | .newCell elementType initializer =>
      .mkObj [
        ("tag", "newCell"),
        ("elementType", encodeType elementType),
        ("initializer", encodeExpr initializer)
      ]
  | .loadCell reference =>
      .mkObj [("tag", "loadCell"), ("reference", encodeExpr reference)]
  | .storeCell reference value =>
      .mkObj [
        ("tag", "storeCell"),
        ("reference", encodeExpr reference),
        ("value", encodeExpr value)
      ]
  | .construct constructor payload =>
      .mkObj [
        ("tag", "construct"),
        ("constructor", encodeConstructorId constructor),
        ("payload", encodeExpr payload)
      ]
  | .matchData dataType resultType scrutinee branches =>
      .mkObj [
        ("tag", "matchData"),
        ("dataType", encodeDataTypeId dataType),
        ("resultType", encodeType resultType),
        ("scrutinee", encodeExpr scrutinee),
        ("branches", .arr (branches.map encodeExpr).toArray)
      ]
  | .unary op operand =>
      .mkObj [
        ("tag", "unary"),
        ("op", encodeUnaryOp op),
        ("operand", encodeExpr operand)
      ]
  | .binary op left right =>
      .mkObj [
        ("tag", "binary"),
        ("op", encodeBinaryOp op),
        ("left", encodeExpr left),
        ("right", encodeExpr right)
      ]
  | .ternary op first second third =>
      .mkObj [
        ("tag", "ternary"),
        ("op", encodeTernaryOp op),
        ("first", encodeExpr first),
        ("second", encodeExpr second),
        ("third", encodeExpr third)
      ]
  | .letE initializer body =>
      .mkObj [
        ("tag", "let"),
        ("initializer", encodeExpr initializer),
        ("body", encodeExpr body)
      ]
  | .ifE condition thenBranch elseBranch =>
      .mkObj [
        ("tag", "if"),
        ("condition", encodeExpr condition),
        ("thenBranch", encodeExpr thenBranch),
        ("elseBranch", encodeExpr elseBranch)
      ]
termination_by expression => sizeOf expression

end Solcore.Core.Wire.V3
