import Solcore.Frontend.ClosedSourceEvaluation
import Solcore.Frontend.ClosedSourceEvaluator

/- Ordered strict binary decomposition keeps actual Words and full stores.
Operator exclusions separate this family from the two short-circuit rules. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem closedSourceExpressionEvaluates_strictWordBinary_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore finalStore : List RuntimeValue}
    {span operatorSpan : Syntax.SourceSpan} {operator : Syntax.BinaryOp}
    (notAnd : operator ≠ .logicalAnd) (notOr : operator ≠ .logicalOr)
    {left right : Syntax.Expr} {value : RuntimeValue} :
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, operator⟩ right⟩ value finalStore ↔
    ∃ leftWord rightWord result middleStore,
      value = RuntimeValue.ofCore result ∧
      ClosedSourceExpressionEvaluates owner names captured initialStore
        left (.word leftWord) middleStore ∧
      ClosedSourceExpressionEvaluates owner names captured middleStore
        right (.word rightWord) finalStore ∧
      StrictWordBinaryDenotes operator leftWord rightWord result := by
  constructor
  · intro evaluated
    cases evaluated with
    | creation shape => cases shape
    | andTrue _ _ => exact False.elim (notAnd rfl)
    | andFalse _ => exact False.elim (notAnd rfl)
    | orTrue _ => exact False.elim (notOr rfl)
    | orFalse _ _ => exact False.elim (notOr rfl)
    | strictWordBinary leftEvaluation rightEvaluation meaning =>
        exact ⟨_, _, _, _, rfl, leftEvaluation, rightEvaluation, meaning⟩
  · rintro ⟨leftWord, rightWord, result, middleStore, rfl, leftEvaluation,
      rightEvaluation, meaning⟩
    exact .strictWordBinary leftEvaluation rightEvaluation meaning

theorem evaluateClosedSourceExpression?_strictWordBinary
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue)
    (span operatorSpan : Syntax.SourceSpan) (operator : Syntax.BinaryOp)
    (notAnd : operator ≠ .logicalAnd) (notOr : operator ≠ .logicalOr)
    (left right : Syntax.Expr) :
    evaluateClosedSourceExpression? (budget + 1) owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, operator⟩ right⟩ =
    (do
      let (.word leftWord, middleStore) ←
        evaluateClosedSourceExpression? budget owner names captured initialStore left | none
      let (.word rightWord, finalStore) ←
        evaluateClosedSourceExpression? budget owner names captured middleStore right | none
      let result ← evaluateStrictWordBinary? operator leftWord rightWord
      return (RuntimeValue.ofCore result, finalStore)) := by
  rw [evaluateClosedSourceExpression?] <;> first | rfl | assumption

end Solcore.Frontend
