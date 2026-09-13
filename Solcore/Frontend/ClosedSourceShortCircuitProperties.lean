import Solcore.Frontend.ClosedSourceEvaluation
import Solcore.Frontend.ClosedSourceEvaluator

/- Exact short-circuit decomposition; actual right values and stores
remain unrestricted, and skipped operands have no evaluation premise. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem closedSourceExpressionEvaluates_logicalAnd_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore finalStore : List RuntimeValue}
    {span operatorSpan : Syntax.SourceSpan}
    {left right : Syntax.Expr} {value : RuntimeValue} :
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ value finalStore ↔
    (value = .bool false ∧
      ClosedSourceExpressionEvaluates owner names captured initialStore
        left (.bool false) finalStore) ∨
    (∃ middleStore,
      ClosedSourceExpressionEvaluates owner names captured initialStore
        left (.bool true) middleStore ∧
      ClosedSourceExpressionEvaluates owner names captured middleStore
        right value finalStore) := by
  constructor
  · intro evaluated
    cases evaluated with
    | creation shape => cases shape
    | andTrue leftEvaluation rightEvaluation => exact .inr ⟨_, leftEvaluation, rightEvaluation⟩
    | andFalse leftEvaluation => exact .inl ⟨rfl, leftEvaluation⟩
  · rintro (⟨rfl, leftEvaluation⟩ | ⟨middleStore, leftEvaluation, rightEvaluation⟩)
    · exact .andFalse leftEvaluation
    · exact .andTrue leftEvaluation rightEvaluation

theorem closedSourceExpressionEvaluates_logicalOr_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore finalStore : List RuntimeValue}
    {span operatorSpan : Syntax.SourceSpan}
    {left right : Syntax.Expr} {value : RuntimeValue} :
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ value finalStore ↔
    (value = .bool true ∧
      ClosedSourceExpressionEvaluates owner names captured initialStore
        left (.bool true) finalStore) ∨
    (∃ middleStore,
      ClosedSourceExpressionEvaluates owner names captured initialStore
        left (.bool false) middleStore ∧
      ClosedSourceExpressionEvaluates owner names captured middleStore
        right value finalStore) := by
  constructor
  · intro evaluated
    cases evaluated with
    | creation shape => cases shape
    | orTrue leftEvaluation => exact .inl ⟨rfl, leftEvaluation⟩
    | orFalse leftEvaluation rightEvaluation => exact .inr ⟨_, leftEvaluation, rightEvaluation⟩
  · rintro (⟨rfl, leftEvaluation⟩ | ⟨middleStore, leftEvaluation, rightEvaluation⟩)
    · exact .orTrue leftEvaluation
    · exact .orFalse leftEvaluation rightEvaluation

theorem evaluateClosedSourceExpression?_logicalAnd
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue)
    (span operatorSpan : Syntax.SourceSpan) (left right : Syntax.Expr) :
    evaluateClosedSourceExpression? (budget + 1) owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ =
    (do
      let (.bool choice, middleStore) ←
        evaluateClosedSourceExpression? budget owner names captured initialStore left | none
      if choice then evaluateClosedSourceExpression? budget owner names captured middleStore right
      else return (.bool false, middleStore)) := by
  rw [evaluateClosedSourceExpression?]
  rfl

theorem evaluateClosedSourceExpression?_logicalOr
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue)
    (span operatorSpan : Syntax.SourceSpan) (left right : Syntax.Expr) :
    evaluateClosedSourceExpression? (budget + 1) owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ =
    (do
      let (.bool choice, middleStore) ←
        evaluateClosedSourceExpression? budget owner names captured initialStore left | none
      if choice then return (.bool true, middleStore)
      else evaluateClosedSourceExpression? budget owner names captured middleStore right) := by
  rw [evaluateClosedSourceExpression?]
  rfl

end Solcore.Frontend
