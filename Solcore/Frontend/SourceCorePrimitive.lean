import Solcore.Frontend.SourceCoreBasic
import Solcore.Core.LocalPrimitiveResults

/-! Word/Bool primitive expressions over optional local cells. Integer literals
use the shared exact Word-evidence validator. Other primitive nodes retain the
empty requirement/coercion boundary; user methods and Integer-valued runtime
operations remain explicit rejections. No source evaluator is imported. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCorePrimitive

open SourceInference

abbrev Error := SourceCoreBasic.Error
abbrev Scope := SourceCoreBasic.Scope
abbrev LoweredExpr := SourceCoreBasic.LoweredExpr

/-- Supplied from the canonical specialized function at the entry boundary.
Literal lowering still authenticates the exact matching retained obligation. -/
structure Context where
  solvedRequirements : List SolvedRequirement
  deriving Repr

def unaryOperator : Syntax.UnaryOp → Core.UnaryOp
  | .logicalNot => .boolNot
  | .bitNot => .wordNot

def binaryOperandType : Syntax.BinaryOp → Core.Ty
  | .logicalAnd | .logicalOr => .bool
  | _ => .word

def binaryResultType : Syntax.BinaryOp → Core.Ty
  | .multiply | .divide | .modulo | .add | .subtract | .bitAnd | .bitXor | .bitOr => .word
  | _ => .bool

/-- Comparisons swap already evaluated payloads, so operand side effects keep
their original order. Boolean short circuit is handled separately below. -/
def strictBinaryBody : Syntax.BinaryOp → Core.Expr
  | .multiply => .binary .wordMul (.var 1) (.var 0)
  | .divide => .binary .wordDiv (.var 1) (.var 0)
  | .modulo => .binary .wordMod (.var 1) (.var 0)
  | .add => .binary .wordAdd (.var 1) (.var 0)
  | .subtract => .binary .wordSub (.var 1) (.var 0)
  | .bitAnd => .binary .wordAnd (.var 1) (.var 0)
  | .bitXor => .binary .wordXor (.var 1) (.var 0)
  | .bitOr => .binary .wordOr (.var 1) (.var 0)
  | .greater => .binary .wordGt (.var 1) (.var 0)
  | .equal => .binary .wordEq (.var 1) (.var 0)
  | .less => .binary .wordGt (.var 0) (.var 1)
  | .lessEqual => .unary .boolNot (.binary .wordGt (.var 1) (.var 0))
  | .greaterEqual => .unary .boolNot (.binary .wordGt (.var 0) (.var 1))
  | .notEqual => .unary .boolNot (.binary .wordEq (.var 1) (.var 0))
  | .logicalAnd => .ifE (.var 1) (.var 0) (.bool false)
  | .logicalOr => .ifE (.var 1) (.bool true) (.var 0)

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

/-- Conditional/group/tuple children use this same policy recursively, so an
operator can occur at any expression position without losing read reasons. -/
def lowerExpressionWithReasons : Nat → Context → TypedSource → Scope → ExpressionId →
    (ExpressionId → Core.Word) → Except Error LoweredExpr
  | 0, _, _, _, id, _ => .error (.traversalExhausted (.occurrence id.occurrence))
  | fuel + 1, context, source, scope, id, reasonAt => do
      if id.occurrence.owner ≠ source.owner then
        throw (.ownerMismatch source.owner id.occurrence.owner)
      let node ← match source.lookupExpression? id with
        | some node => pure node
        | none => .error (.missingExpression id)
      match node.form with
      | .integerLiteral literal resolution =>
          let validated ← (SourceCoreElaboration.validateWordIntegerLiteral context.solvedRequirements
            node literal resolution).mapError SourceCoreBasic.Error.literalEvidence
          pure ⟨.word, Core.LanguageResult.success (.word validated.value)⟩
      | _ =>
          let (node, type) ← SourceCoreBasic.readExpression source id
          let site := SourceCoreElaboration.ErrorSite.occurrence id.occurrence
          match node.form with
          | .unary operator operand =>
              let operand ← lowerExpressionWithReasons fuel context source scope operand reasonAt
              let coreOperator := unaryOperator operator
              SourceCoreBasic.ensureType site coreOperator.operandType operand.type
              SourceCoreBasic.ensureType site coreOperator.resultType type
              pure ⟨type, Core.LocalPrimitiveResults.unary coreOperator operand.expression⟩
          | .binary left operator right =>
              let left ← lowerExpressionWithReasons fuel context source scope left reasonAt
              let right ← lowerExpressionWithReasons fuel context source scope right reasonAt
              SourceCoreBasic.ensureType site (binaryOperandType operator) left.type
              SourceCoreBasic.ensureType site (binaryOperandType operator) right.type
              SourceCoreBasic.ensureType site (binaryResultType operator) type
              pure ⟨type, binary operator left.expression right.expression⟩
          | .conditional condition thenBranch elseBranch =>
              let condition ← lowerExpressionWithReasons fuel context source scope condition reasonAt
              SourceCoreBasic.ensureType site .bool condition.type
              let thenBranch ← lowerExpressionWithReasons fuel context source scope thenBranch reasonAt
              let elseBranch ← lowerExpressionWithReasons fuel context source scope elseBranch reasonAt
              SourceCoreBasic.ensureType site type thenBranch.type
              SourceCoreBasic.ensureType site type elseBranch.type
              pure ⟨type, Core.LocalControl.choose type condition.expression thenBranch.expression elseBranch.expression⟩
          | .group inner =>
              let inner ← lowerExpressionWithReasons fuel context source scope inner reasonAt
              SourceCoreBasic.ensureType site type inner.type
              pure inner
          | .tuple [left, right] =>
              let left ← lowerExpressionWithReasons fuel context source scope left reasonAt
              let right ← lowerExpressionWithReasons fuel context source scope right reasonAt
              SourceCoreBasic.ensureType site type (.product left.type right.type)
              pure ⟨type, Core.LocalSequence.pair left.type right.type left.expression right.expression⟩
          | _ => SourceCoreBasic.lowerExpression (fuel + 1) source scope id (reasonAt id)

def lowerExpression (fuel : Nat) (context : Context) (source : TypedSource) (scope : Scope)
    (id : ExpressionId) (reason : Core.Word) : Except Error LoweredExpr :=
  lowerExpressionWithReasons fuel context source scope id (fun _ => reason)

end Solcore.Frontend.SourceCorePrimitive
