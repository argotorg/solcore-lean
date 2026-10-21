import Solcore.SourceSemantics.SourceInferenceActualCallOrder
import Solcore.SourceSemantics.SourceInferenceActualExpressionEntryInputs

/-! Expression siblings follow the allocator order of their actual prefix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2500000
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables

private theorem fresh_order {before after : State} {type : Ty}
    (accepted : before.fresh = (type, after)) :
    before.inference.next ≤ after.inference.next := by
  have same := congrArg (fun result : Ty × State => result.2.inference.next) accepted
  simp only [State.fresh, InferState.fresh] at same
  omega

private theorem fresh_pair_order {baseState keyState valueState fitted : State}
    {keyType valueType baseType : Ty}
    (fitting : unify valueState baseType (.mapping keyType valueType) = .ok fitted)
    (valueFresh : keyState.fresh = (valueType, valueState))
    (keyFresh : baseState.fresh = (keyType, keyState)) :
    baseState.inference.next ≤ fitted.inference.next := by
  have a := fresh_order keyFresh
  have b := fresh_order valueFresh
  have c := unify_next fitting
  omega

private theorem lambdaPrefix_unique
    {context : SourceInference.Context} {expected : Option Ty}
    {annotation : Option Syntax.TypeExpr} {types : List Ty} {initial : State}
    {leftType rightType : Ty} {leftState rightState : State}
    (left : LambdaPrefixFacts context expected annotation types initial leftType leftState)
    (right : LambdaPrefixFacts context expected annotation types initial rightType rightState) :
    leftType = rightType ∧ leftState = rightState := by
  cases left <;> cases right <;> simp_all

private theorem conditional_then_next
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
    {value : InferredExpression}
    {condition thenBranch elseBranch : Syntax.Expr} {question colon : Syntax.SourceSpan}
    {conditionValue thenValue : InferredExpression} {conditionState thenState : State}
    (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
    (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
    (form : source.value = .conditional condition question thenBranch colon elseBranch)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok (conditionValue, conditionState))
    (thenAccepted : inferExprFuel fuel context thenBranch expected conditionState = .ok (thenValue, thenState)) :
    conditionState.inference.next ≤ thenState.inference.next := by
  have childInputs := ActualExpressionInputs.expression_conditional_then
    accepted form allocation conditionAccepted thenAccepted inputs
  exact (childInputs.progress thenAccepted).1.next_le

theorem ChildStep.expression_ordered
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {expected : Option Ty} {initial final : State} {value : InferredExpression}
    {left right : CallIndex}
    (inputs : (CallIndex.expression fuel context source expected initial value final).Inputs)
    (leftStep : ChildStep (.expression fuel context source expected initial value final) left)
    (rightStep : ChildStep (.expression fuel context source expected initial value final) right) :
    left.Ordered right := by
  cases leftStep
  all_goals try
    have thenNext := conditional_then_next inputs (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption)
  all_goals cases rightStep
  case expression_conditional_condition.expression_conditional_else =>
    rename_i accepted form allocation conditionAccepted thenAccepted child
    have thenNext := conditional_then_next inputs child form thenAccepted accepted allocation
    simp_all [CallIndex.Ordered, CallIndex.Accepted, CallIndex.initial, CallIndex.final]
  all_goals simp_all [CallIndex.Ordered, CallIndex.Accepted, CallIndex.initial, CallIndex.final]
  all_goals first
    | solve | grind only [lambdaPrefix_unique]
    | (have fittedNext := fresh_pair_order (by assumption) (by assumption) (by assumption)
       omega)

end Solcore.SourceSemantics.SourceInferenceExecution
