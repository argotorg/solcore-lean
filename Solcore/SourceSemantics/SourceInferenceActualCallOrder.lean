import Solcore.SourceSemantics.SourceInferenceActualCallInputTraversal

/-! Immediate actual children are identical or ordered by the real allocator. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables

def CallIndex.Ordered (left right : CallIndex) : Prop :=
  left = right ∨ left.final.inference.next ≤ right.initial.inference.next ∨
    right.final.inference.next ≤ left.initial.inference.next

theorem ChildStep.expressions_ordered
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Expr}
    {initial final : State} {values : List InferredExpression} {left right : CallIndex}
    (inputs : (CallIndex.expressions fuel context sources initial values final).Inputs)
    (leftStep : ChildStep (.expressions fuel context sources initial values final) left)
    (rightStep : ChildStep (.expressions fuel context sources initial values final) right) :
    left.Ordered right := by
  cases leftStep <;> cases rightStep <;> simp_all [CallIndex.Ordered, CallIndex.Accepted, CallIndex.initial, CallIndex.final]

end Solcore.SourceSemantics.SourceInferenceExecution
