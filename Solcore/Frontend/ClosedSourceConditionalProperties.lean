import Solcore.Frontend.ClosedSourceEvaluation
import Solcore.Frontend.ClosedSourceEvaluator

/- Exact original conditional decomposition and successor-depth computation.
Only the selected original branch is evaluated, under the unchanged lexical rows. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- An original conditional evaluates exactly its actual Bool-selected branch. -/
theorem closedSourceExpressionEvaluates_conditional_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore finalStore : List RuntimeValue}
    {span question colon : Syntax.SourceSpan}
    {condition thenBranch elseBranch : Syntax.Expr} {value : RuntimeValue} :
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .conditional condition question thenBranch colon elseBranch⟩ value finalStore ↔
    ∃ (choice : Bool) (middleStore : List RuntimeValue),
      ClosedSourceExpressionEvaluates owner names captured initialStore
        condition (.bool choice) middleStore ∧
      ClosedSourceExpressionEvaluates owner names captured middleStore
        (if choice then thenBranch else elseBranch) value finalStore := by
  constructor
  · intro evaluated
    cases evaluated with
    | creation shape => cases shape
    | conditionalTrue condition branch => exact ⟨true, _, condition, branch⟩
    | conditionalFalse condition branch => exact ⟨false, _, condition, branch⟩
  · rintro ⟨choice, middleStore, condition, branch⟩
    cases choice
    · exact .conditionalFalse condition branch
    · exact .conditionalTrue condition branch

/-- The guard and selected original branch share the same predecessor depth. -/
theorem evaluateClosedSourceExpression?_conditional
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue)
    (span question colon : Syntax.SourceSpan)
    (condition thenBranch elseBranch : Syntax.Expr) :
    evaluateClosedSourceExpression? (budget + 1) owner names captured initialStore
      ⟨span, .conditional condition question thenBranch colon elseBranch⟩ =
    (do
      let (.bool choice, middleStore) ←
        evaluateClosedSourceExpression? budget owner names captured initialStore condition | none
      evaluateClosedSourceExpression? budget owner names captured middleStore
        (if choice then thenBranch else elseBranch)) := by
  rw [evaluateClosedSourceExpression?]
  rfl

end Solcore.Frontend
