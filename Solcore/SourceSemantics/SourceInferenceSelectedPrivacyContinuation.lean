import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyLookup

/-! Privacy for the actual expected-type continuation. Coercion commitment
allocates obligations but does not change type substitution or lexical binders. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem commit_binders (state : State) (plan : List Detail.PlannedCoercionStep) :
    (Detail.commitCoercionPlan state plan).2.localBinders = state.localBinders := by
  induction plan generalizing state with
  | nil => rfl
  | cons step rest ih =>
    simp only [Detail.commitCoercionPlan]
    rw [ih, requirementBatch_binders]
    rfl

/-- This is derived from the successful fit, including the real unifier or
coercion-plan branch. It places no restriction on dead substitution entries. -/
theorem withExpected_private
    {protectedVars : List TypeVarId} {context : SourceInference.Context}
    {state : State} {actual : InferredExpression} {expected : Option Ty}
    {result : Detail.ExpectationResult}
    (ready : state.InferenceReady)
    (actualBelow : actual.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (actualSafe : Safe protectedVars state actual.type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.withExpected context state actual expected = .ok result) :
    SafeTransport protectedVars state result.state ∧
    Safe protectedVars result.state result.expression.type ∧
    LiveBindersSafe protectedVars result.state := by
  have resultReady := (Detail.withExpected_inferenceProperties ready actualBelow expectedBelow accepted).2.1
  cases expected with
  | none =>
    simp only [Detail.withExpected, Except.ok.injEq] at accepted
    cases accepted
    exact ⟨.refl _ _, safe_resolved ready actualSafe, live⟩
  | some expected =>
    have expectedSafe := expectedSafe expected (by simp)
    cases unified : state.inference.unify actual.type expected with
    | ok inference =>
      simp only [Detail.withExpected, unified, Except.ok.injEq] at accepted
      cases accepted
      have actualUnify : Detail.unify state actual.type expected =
          .ok {state with inference} := by
        simp [Detail.unify, unified, Detail.liftUnification, bind, Except.bind]
      have transport := ProtectedVariables.unify actualSafe expectedSafe actualUnify
      exact ⟨transport, safe_resolved resultReady (transport _ expectedSafe),
        live.transport rfl transport⟩
    | error error =>
      cases error with
      | occursCheck _ _ => simp [Detail.withExpected, unified] at accepted
      | exhausted => simp [Detail.withExpected, unified] at accepted
      | mismatch left right =>
        simp only [Detail.withExpected, unified] at accepted
        cases planned : Detail.coercionPlan? context state
            (state.resolve actual.type) (state.resolve expected) with
        | error error => simp [planned, bind, Except.bind] at accepted
        | ok option =>
          cases option with
          | none => simp [planned, bind, Except.bind] at accepted
          | some plan =>
            simp only [planned, bind, Except.bind] at accepted
            change Except.ok _ = Except.ok result at accepted
            cases Except.ok.inj accepted
            have transport : SafeTransport protectedVars state
                (Detail.commitCoercionPlan state plan).2 := by
              intro type safe
              simpa only [Safe, Detail.commitCoercionPlan_resolve] using safe
            refine ⟨transport, ?_, live.transport (commit_binders _ _) transport⟩
            simpa only [Safe, Detail.commitCoercionPlan_resolve] using
              safe_resolved ready expectedSafe

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
