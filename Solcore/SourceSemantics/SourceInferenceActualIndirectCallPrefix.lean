import Solcore.SourceSemantics.SourceInferenceActualCallGraph

/-! An accepted indirect dispatch identifies its actual application suffix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail

theorem indirectCall_actual_suffix
    {fuel : Nat} {context : SourceInference.Context} {source callee : Syntax.Expr}
    {arguments : Syntax.DelimitedList Syntax.Expr} {id : ExpressionId} {expected : Option Ty}
    {initial allocated argumentState calleeState : State}
    {inferredArguments : List InferredExpression} {inferredCallee : InferredExpression}
    {result : InferredExpression × State}
    (form : source.value = .call callee arguments)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (nonconstructor : constructorCalleeCandidates context allocated callee = .ok [])
    (argumentsAccepted : inferExprsFuel fuel context arguments.elements allocated = .ok (inferredArguments, argumentState))
    (indirect : IndirectCalleeAt context callee argumentState)
    (calleeAccepted : inferExprFuel fuel context callee none argumentState = .ok (inferredCallee, calleeState))
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok result) :
    ∃ application,
      applyFunctionType context id inferredCallee.type inferredArguments expected calleeState = .ok application ∧
      recordIndirectCall source inferredCallee inferredArguments application = result := by
  unfold inferExprFuel at accepted
  simp only [allocation, form, nonconstructor, argumentsAccepted, calleeAccepted,
    bind, Except.bind] at accepted
  repeat' first | split at accepted
  all_goals try simp_all [IndirectCalleeAt, pure, Pure.pure, Except.pure]
  all_goals exact ⟨_, by assumption, by assumption⟩

end Solcore.SourceSemantics.SourceInferenceExecution
