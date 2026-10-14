import Solcore.SourceSemantics.SourceInferenceExpressionCallDispatchSoundness

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem inferExprFuel_call_constructorDiscovery
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {expression callee : Syntax.Expr} {arguments : Syntax.DelimitedList Syntax.Expr}
    {expected : Option Ty} {initial : State}
    {result : InferredExpression × State}
    (expressionEq : expression.value = .call callee arguments)
    (success : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result) :
    Detail.constructorCalleeCandidates context initial.allocateExpressionId.2 callee = .ok [] ∨
      ∃ dataType constructor,
        Detail.constructorCalleeCandidates context initial.allocateExpressionId.2 callee =
          .ok [(dataType, constructor)] := by
  generalize allocationEq : initial.allocateExpressionId = allocatedPair at *
  rcases allocatedPair with ⟨id, allocated⟩
  unfold Detail.inferExprFuel at success
  simp only [allocationEq, expressionEq, bind, Except.bind] at success
  cases discovery : Detail.constructorCalleeCandidates context allocated callee with
  | error error => simp [discovery] at success
  | ok candidates =>
      cases candidates with
      | nil => exact .inl rfl
      | cons first rest =>
          rcases first with ⟨dataType, constructor⟩
          cases rest with
          | nil => exact .inr ⟨dataType, constructor, rfl⟩
          | cons second tail => simp [discovery] at success

end Solcore.SourceSemantics.SourceInferenceSoundness
