import Solcore.SourceSemantics.SourceInferenceActualExpressionCallOrder
import Solcore.SourceSemantics.SourceInferenceActualNonExpressionCallOrder

/-! Sibling calls in every actual inference family share a call or occupy
ordered allocator intervals. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution

theorem ChildStep.ordered {parent left right : CallIndex}
    (inputs : parent.Inputs) (first : ChildStep parent left) (second : ChildStep parent right) :
    left.Ordered right := by
  cases parent <;> first
    | exact ChildStep.expression_ordered inputs first second
    | exact ChildStep.expressions_ordered inputs first second
    | exact ChildStep.constructorApplication_ordered inputs first second
    | exact ChildStep.constructorArguments_ordered inputs first second
    | exact ChildStep.statements_ordered inputs first second
    | exact ChildStep.statement_ordered inputs first second
    | exact ChildStep.forItems_ordered inputs first second
    | exact ChildStep.forItem_ordered inputs first second
    | exact ChildStep.place_ordered inputs first second
    | exact ChildStep.assignedValue_ordered inputs first second
    | exact ChildStep.matchCases_ordered inputs first second

end Solcore.SourceSemantics.SourceInferenceExecution
