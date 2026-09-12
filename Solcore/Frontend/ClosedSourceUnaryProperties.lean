import Solcore.Frontend.ClosedSourceEvaluation
import Solcore.Frontend.ClosedSourceEvaluator

/- Exact original unary decomposition and predecessor-depth computation. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem closedSourceExpressionEvaluates_logicalNot_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore finalStore : List RuntimeValue}
    {span operatorSpan : Syntax.SourceSpan}
    {operand : Syntax.Expr} {value : RuntimeValue} :
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .unary ⟨operatorSpan, .logicalNot⟩ operand⟩ value finalStore ↔
    ∃ operandValue : Bool,
      ClosedSourceExpressionEvaluates owner names captured initialStore
        operand (.bool operandValue) finalStore ∧
      value = .bool (!operandValue) := by
  constructor
  · intro evaluated
    cases evaluated with
    | creation shape => cases shape
    | logicalNot child => exact ⟨_, child, rfl⟩
  · rintro ⟨operandValue, child, rfl⟩
    exact .logicalNot child

theorem closedSourceExpressionEvaluates_bitNot_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore finalStore : List RuntimeValue}
    {span operatorSpan : Syntax.SourceSpan}
    {operand : Syntax.Expr} {value : RuntimeValue} :
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .unary ⟨operatorSpan, .bitNot⟩ operand⟩ value finalStore ↔
    ∃ operandValue : Core.Word,
      ClosedSourceExpressionEvaluates owner names captured initialStore
        operand (.word operandValue) finalStore ∧
      value = .word operandValue.bitNot := by
  constructor
  · intro evaluated
    cases evaluated with
    | creation shape => cases shape
    | bitNot child => exact ⟨_, child, rfl⟩
  · rintro ⟨operandValue, child, rfl⟩
    exact .bitNot child

theorem evaluateClosedSourceExpression?_logicalNot
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue)
    (span operatorSpan : Syntax.SourceSpan) (operand : Syntax.Expr) :
    evaluateClosedSourceExpression? (budget + 1) owner names captured initialStore
      ⟨span, .unary ⟨operatorSpan, .logicalNot⟩ operand⟩ =
    (do
      let (.bool value, finalStore) ←
        evaluateClosedSourceExpression? budget owner names captured initialStore operand | none
      return (.bool (!value), finalStore)) := by
  rw [evaluateClosedSourceExpression?]
  rfl

theorem evaluateClosedSourceExpression?_bitNot
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue)
    (span operatorSpan : Syntax.SourceSpan) (operand : Syntax.Expr) :
    evaluateClosedSourceExpression? (budget + 1) owner names captured initialStore
      ⟨span, .unary ⟨operatorSpan, .bitNot⟩ operand⟩ =
    (do
      let (.word value, finalStore) ←
        evaluateClosedSourceExpression? budget owner names captured initialStore operand | none
      return (.word value.bitNot, finalStore)) := by
  rw [evaluateClosedSourceExpression?]
  rfl

end Solcore.Frontend
