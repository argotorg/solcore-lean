import Solcore.Frontend.SourceCorePrimitive
import Solcore.Core.TaggedFunction

/-! Native Integer expressions and monomorphic builtin closures are ordinary
Core code. Arithmetic preserves source operand order; reversed comparisons
swap the already evaluated payloads. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreInteger

def binaryResultType : Syntax.BinaryOp → Core.Ty
  | .multiply | .divide | .modulo | .add | .subtract | .bitAnd | .bitXor | .bitOr => .integer
  | _ => .bool

def strictBinaryBody : Syntax.BinaryOp → Core.Expr
  | .multiply => .binary .integerMul (.var 1) (.var 0)
  | .divide => .binary .integerDiv (.var 1) (.var 0)
  | .modulo => .binary .integerMod (.var 1) (.var 0)
  | .add => .binary .integerAdd (.var 1) (.var 0)
  | .subtract => .binary .integerSub (.var 1) (.var 0)
  | .bitAnd => .binary .integerAnd (.var 1) (.var 0)
  | .bitXor => .binary .integerXor (.var 1) (.var 0)
  | .bitOr => .binary .integerOr (.var 1) (.var 0)
  | .less => .binary .integerLt (.var 1) (.var 0)
  | .equal => .binary .integerEq (.var 1) (.var 0)
  | .greater => .binary .integerLt (.var 0) (.var 1)
  | .greaterEqual => .unary .boolNot (.binary .integerLt (.var 1) (.var 0))
  | .lessEqual => .unary .boolNot (.binary .integerLt (.var 0) (.var 1))
  | .notEqual => .unary .boolNot (.binary .integerEq (.var 1) (.var 0))
  | .logicalAnd => .ifE (.var 1) (.var 0) (.bool false)
  | .logicalOr => .ifE (.var 1) (.bool true) (.var 0)

def binaryOperandType : Syntax.BinaryOp → Core.Ty
  | .logicalAnd | .logicalOr => .bool
  | _ => .integer

def binary (operator : Syntax.BinaryOp) (left right : Core.Expr) : Core.Expr :=
  match operator with
  | .logicalAnd => Core.LocalPrimitiveResults.logicalAnd left right
  | .logicalOr => Core.LocalPrimitiveResults.logicalOr left right
  | _ => Core.LocalPrimitiveResults.binaryWith (binaryResultType operator) left right
      (strictBinaryBody operator)

theorem strictBinaryBody_hasType {definitions : Core.DataEnvironment} {scope : Core.Context}
    (operator : Syntax.BinaryOp) :
    Core.HasType (binaryOperandType operator :: binaryOperandType operator :: scope)
      (strictBinaryBody operator) (binaryResultType operator) definitions := by
  cases operator <;> first
    | exact .binary (.var rfl) (.var rfl)
    | exact .unary (.binary (.var rfl) (.var rfl))
    | exact .ifE (.var rfl) (.var rfl) .bool
    | exact .ifE (.var rfl) .bool (.var rfl)

theorem binary_hasType {definitions : Core.DataEnvironment} {scope : Core.Context}
    {operator : Syntax.BinaryOp} {left right : Core.Expr}
    (leftTyped : Core.HasType scope left (Core.LanguageResult.resultType (binaryOperandType operator)) definitions)
    (rightTyped : Core.HasType scope right (Core.LanguageResult.resultType (binaryOperandType operator)) definitions) :
    Core.HasType scope (binary operator left right)
      (Core.LanguageResult.resultType (binaryResultType operator)) definitions := by
  cases operator <;> first
    | exact Core.LocalPrimitiveResults.logicalAnd_hasType leftTyped rightTyped
    | exact Core.LocalPrimitiveResults.logicalOr_hasType leftTyped rightTyped
    | exact Core.LocalPrimitiveResults.binaryWith_hasType (by constructor) leftTyped rightTyped
        (strictBinaryBody_hasType _)

def builtinParameter : BuiltinFunctionId → Core.Ty
  | .wordToInteger => .word
  | .wordFromInteger => .integer
  | _ => .product .integer .integer

def builtinResult : BuiltinFunctionId → Core.Ty
  | .wordFromInteger => .word
  | .integerEq | .integerLt => .bool
  | _ => .integer

def builtinBody : BuiltinFunctionId → Core.Expr
  | .integerSub => .binary .integerSub (.first (.var 0)) (.second (.var 0))
  | .integerAdd => .binary .integerAdd (.first (.var 0)) (.second (.var 0))
  | .integerMul => .binary .integerMul (.first (.var 0)) (.second (.var 0))
  | .integerEq => .binary .integerEq (.first (.var 0)) (.second (.var 0))
  | .integerLt => .binary .integerLt (.first (.var 0)) (.second (.var 0))
  | .wordFromInteger => .unary .integerToWord (.var 0)
  | .wordToInteger => .unary .wordToInteger (.var 0)

def builtinClosure (function : BuiltinFunctionId) : Core.Expr :=
  .lambda (builtinParameter function) (Core.LanguageResult.resultType (builtinResult function))
    (Core.LanguageResult.success (builtinBody function))

theorem builtinClosure_hasType {definitions : Core.DataEnvironment} {scope : Core.Context}
    (function : BuiltinFunctionId) : Core.HasType scope (builtinClosure function)
      (.function (builtinParameter function) (Core.LanguageResult.resultType (builtinResult function))) definitions := by
  cases function <;>
    apply Core.HasType.lambda (by repeat constructor) (by repeat constructor) <;>
      apply Core.LanguageResult.success_hasType <;> first
        | exact .binary (.first (.var rfl)) (.second (.var rfl))
        | exact .unary (.var rfl)

end Solcore.Frontend.SourceCoreInteger
