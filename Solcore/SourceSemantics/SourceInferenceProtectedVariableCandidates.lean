import Solcore.SourceSemantics.SourceInferenceProtectedVariableArguments

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem formed_below {context : SourceSemantics.Context} {type : Ty}
    (formed : TypeWellFormed context type) (next : Nat) : type.VariablesBelow next := by
  intro metavariable occurs
  have closed := StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil formed
  simp [closed] at occurs

private theorem candidate_fit {context : SourceInference.Context} {state : State}
    {actual : InferredExpression} {expected : Option Ty} {result : Detail.ExpectationResult}
    (accepted : Detail.candidateWithExpected context state actual expected = .ok (some result)) :
    Detail.withExpected context state actual expected = .ok result := by
  unfold Detail.candidateWithExpected at accepted
  cases fitted : Detail.withExpected context state actual expected with
  | ok value =>
    simp only [fitted, Except.ok.injEq, Option.some.injEq] at accepted
    cases accepted
    rfl
  | error error =>
    cases error <;> simp [fitted] at accepted
    all_goals cases ‹Unification.Error› <;> simp_all

/-- Actual candidate instantiation, argument fitting and result fitting preserve
initially fixed variables excluded by the real operand types. -/
theorem tryFunctionCandidate_fixes_protected {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {state : State} {arguments : List InferredExpression}
    {integerOrigins : List IntegerLiteralOrigin} {call : ExpressionId} {expected : Option Ty}
    {signature : ProgramFunctionSignature} {result : Detail.CandidateAttemptResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (member : signature ∈ context.signatures.functions)
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument.type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (fixed : FixesProtected protectedVars state)
    (accepted : Detail.tryFunctionCandidate context arguments integerOrigins call expected state signature = .ok (some result)) :
    FixesProtected protectedVars result.state := by
  let instantiated := signature.scheme.instantiate state.inference.next
  let advanced : State := {state with inference := {state.inference with next := instantiated.next}}
  have signatureFormed := catalog.functions_semantic signature member
  have nextLe := ConstrainedDeclarationScheme.instantiate_next_le signature.scheme state.inference.next
  have advanceProgress : state.InferenceProgress advanced :=
    State.InferenceProgress.of_substitution_eq ready.solved nextLe rfl
  have advancedReady := State.InferenceReady.of_progress_of_binderEnvironment_eq ready advanceProgress rfl
  have advancePrivacy : SafeTransport protectedVars state advanced := .of_substitution_eq rfl
  have rangeSafe := declaration_instantiation_private signature.scheme ready bound
  have rangeBelow : ∀ {parameter replacement}, (parameter, replacement) ∈ instantiated.parameterSubstitution →
      replacement.VariablesBelow advanced.inference.next :=
    ConstrainedDeclarationScheme.instantiate_parameterSubstitution_range_variablesBelow
      signature.scheme state.inference.next
  have parametersSafe : ∀ type ∈ signature.parameterTypes.map instantiated.parameterSubstitution.apply,
      Safe protectedVars advanced type := by
    intro type typeMember
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp typeMember
    exact safe_parameterApply rangeSafe
      (safe_closed _ _ (formed_below (signatureFormed.parameter_types _ originalMember) 0))
  have parametersBelow : ∀ type ∈ signature.parameterTypes.map instantiated.parameterSubstitution.apply,
      type.VariablesBelow advanced.inference.next := by
    intro type typeMember
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp typeMember
    exact ParameterSubstitution.apply_variables_below rangeBelow
      (formed_below (signatureFormed.parameter_types _ originalMember) _)
  have returnsClosed : (Ty.productMany signature.returnTypes).VariablesBelow 0 :=
    Ty.variablesBelow_productMany (fun type member => formed_below (signatureFormed.return_types type member) 0)
  have resultSafe : Safe protectedVars advanced
      (instantiated.parameterSubstitution.apply (Ty.productMany signature.returnTypes)) :=
    safe_parameterApply rangeSafe (safe_closed _ _ returnsClosed)
  obtain ⟨fittedArguments, fittedResult, trace, fitResult, _, _, _, _, _, stateEq⟩ :=
    Detail.tryFunctionCandidate_some_resultFitAllocationWitness signatureFormed.scheme_body accepted
  have argumentAccepted := trace.fitArguments_eq
  have argumentPrivacy := fitArguments_private catalog advancedReady
    (fun arg member => (argumentsBelow arg member).weaken advanceProgress.next_le) parametersBelow
    (fun arg member => advancePrivacy _ (argumentsSafe arg member)) parametersSafe
    (live.transport rfl advancePrivacy) argumentAccepted
  have argumentFixed := fitArguments_fixes_protected advancedReady
    (fun arg member => (argumentsBelow arg member).weaken advanceProgress.next_le) parametersBelow
    (fun arg member => advancePrivacy _ (argumentsSafe arg member)) parametersSafe
    (live.transport rfl advancePrivacy) (fixed.of_substitution_eq rfl) argumentAccepted
  have fittedFixed := withExpected_fixes_protected argumentFixed
    (argumentPrivacy.1 _ resultSafe)
    (fun type member => argumentPrivacy.1 _ (advancePrivacy _ (expectedSafe type member)))
    (candidate_fit fitResult)
  have sameInference : result.state.inference = fittedResult.state.inference := by
    rw [stateEq]
    exact requirementBatch_inference _ _
  exact fittedFixed.of_substitution_eq (congrArg InferState.substitution sameInference)

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
