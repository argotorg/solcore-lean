import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyApplications

/-! Named declaration parameters and predicates are instantiated from the
actual allocator and the checked signature catalog. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem formed_below {context : SourceSemantics.Context} {type : Ty}
    (formed : TypeWellFormed context type) (next : Nat) : type.VariablesBelow next := by
  intro metavariable occurs
  have closed := StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil formed
  simp [closed] at occurs

/-- The real rigid-parameter allocator cannot expose any older protected
metavariable. No privacy of an arbitrary substitution range is assumed. -/
theorem declaration_instantiation_private {protectedVars : List TypeVarId} {state : State}
    (scheme : ConstrainedDeclarationScheme)
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) :
    let instantiated := scheme.instantiate state.inference.next
    let advanced : State := {state with inference := {state.inference with next := instantiated.next}}
    ∀ parameter replacement, (parameter,replacement) ∈ instantiated.parameterSubstitution →
      Safe protectedVars advanced replacement := by
  dsimp only
  intro parameter replacement member
  obtain ⟨metavariable, rfl, lower, _⟩ :=
    ConstrainedDeclarationScheme.instantiate_parameterSubstitution_range_fresh scheme state.inference.next member
  change Avoids protectedVars (state.resolve (.variable metavariable))
  rw [resolve_fresh_variable ready metavariable lower]
  intro candidate occurs protectedMember
  have same : candidate = metavariable := by simpa [Ty.freeVariables] using occurs
  subst candidate
  exact (Nat.not_lt.mpr lower) (bound metavariable protectedMember)

private theorem predicate_parameters_private {protectedVars : List TypeVarId} {state : State}
    {context : SourceSemantics.Context} {predicate : ProgramPredicate}
    (formed : PredicateWellFormed context predicate) (substitution : ParameterSubstitution)
    (range : ∀ parameter replacement, (parameter,replacement) ∈ substitution →
      Safe protectedVars state replacement) :
    PredicateSafe protectedVars state (predicate.applyParameters substitution) := by
  intro type member
  rcases List.mem_cons.mp member with rfl | member
  · exact safe_parameterApply range (safe_closed _ _ (formed_below formed.subject 0))
  · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact safe_parameterApply range
      (safe_closed _ _ (formed_below (formed.arguments _ originalMember) 0))

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

/-- Actual signature selection, argument fitting, result fitting and the
final declaration batch jointly establish privacy for a retained candidate. -/
theorem tryFunctionCandidate_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {state : State} {arguments : List InferredExpression}
    {integerOrigins : List IntegerLiteralOrigin} {call : ExpressionId} {expected : Option Ty}
    {signature : ProgramFunctionSignature} {result : Detail.CandidateAttemptResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (member : signature ∈ context.signatures.functions)
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument.type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.tryFunctionCandidate context arguments integerOrigins call expected state signature =
      .ok (some result)) :
    SafeTransport protectedVars state result.state ∧
    Safe protectedVars result.state result.result.type ∧
    LiveBindersSafe protectedVars result.state ∧
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateSafe protectedVars result.state row.predicate := by
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
  have resultBelow : (instantiated.parameterSubstitution.apply (Ty.productMany signature.returnTypes)).VariablesBelow
      advanced.inference.next :=
    ParameterSubstitution.apply_variables_below rangeBelow (returnsClosed.weaken (Nat.zero_le _))
  have predicatesSafe : ∀ predicate ∈ instantiated.predicates, PredicateSafe protectedVars advanced predicate := by
    intro predicate predicateMember
    rw [ConstrainedDeclarationScheme.instantiate_predicates] at predicateMember
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp predicateMember
    exact predicate_parameters_private (signatureFormed.predicates _ originalMember) _ rangeSafe
  obtain ⟨fittedArguments, fittedResult, trace, fitResult, _, resultEq, _, _, _, stateEq⟩ :=
    Detail.tryFunctionCandidate_some_resultFitAllocationWitness signatureFormed.scheme_body accepted
  have argumentAccepted := trace.fitArguments_eq
  have argumentProgress := Detail.fitArguments_some_inferenceProperties advancedReady
    (fun arg member => (argumentsBelow arg member).weaken advanceProgress.next_le)
    parametersBelow argumentAccepted
  have argumentPrivacy := fitArguments_private catalog advancedReady
    (fun arg member => (argumentsBelow arg member).weaken advanceProgress.next_le) parametersBelow
    (fun arg member => advancePrivacy _ (argumentsSafe arg member)) parametersSafe
    (live.transport rfl advancePrivacy) argumentAccepted
  have fitAccepted := candidate_fit fitResult
  have beforeFit := advancePrivacy.trans argumentPrivacy.1
  have totalNext := (advanceProgress.trans argumentProgress.1).next_le
  have fittedPrivacy := withExpected_private argumentProgress.2
    (resultBelow.weaken argumentProgress.1.next_le)
    (fun type member => (expectedBelow type member).weaken totalNext)
    (argumentPrivacy.1 _ resultSafe)
    (fun type member => beforeFit _ (expectedSafe type member)) argumentPrivacy.2.1 fitAccepted
  have fittedRows := withExpected_new_requirements_private catalog argumentProgress.2
    (argumentPrivacy.1 _ resultSafe)
    (fun type member => beforeFit _ (expectedSafe type member)) fitAccepted
  have fittedReady := (Detail.withExpected_inferenceProperties argumentProgress.2
    (resultBelow.weaken argumentProgress.1.next_le)
    (fun type member => (expectedBelow type member).weaken totalNext) fitAccepted).2.1
  have sameInference : result.state.inference = fittedResult.state.inference := by
    rw [stateEq]
    exact requirementBatch_inference _ _
  have sameBinders : result.state.localBinders = fittedResult.state.localBinders := by
    rw [stateEq]
    exact requirementBatch_binders _ _
  have completion : SafeTransport protectedVars fittedResult.state result.state :=
    .of_substitution_eq (congrArg InferState.substitution sameInference)
  refine ⟨beforeFit.trans (fittedPrivacy.1.trans completion), ?_,
    fittedPrivacy.2.2.transport sameBinders completion, ?_⟩
  · rw [resultEq]
    have safe := safe_resolved fittedReady fittedPrivacy.2.1
    have batchInference := requirementBatch_inference fittedResult.state (signature.scheme.instantiate state.inference.next).predicates
    simpa only [Safe, State.resolve, InferState.resolve, sameInference, State.markDirectCallRequirements, batchInference] using safe
  · intro row rowMember fresh
    have batchMember : row ∈ (fittedResult.state.addRequirementsWithIds instantiated.predicates).2.requirements := by
      simpa only [stateEq, State.markDirectCallRequirements] using rowMember
    rcases requirementBatch_row_origin _ _ batchMember with old | issued
    · have beforeRows : ∀ row ∈ fittedResult.state.requirements, row ∉ state.requirements →
          PredicateSafe protectedVars fittedResult.state row.predicate := by
        have combined := new_requirements_trans argumentPrivacy.2.2 fittedRows fittedPrivacy.1
        exact combined
      intro type typeMember
      exact completion _ (beforeRows row old fresh type typeMember)
    · intro type typeMember
      exact completion _ (fittedPrivacy.1 _
        (argumentPrivacy.1 _ (predicatesSafe row.predicate issued type typeMember)))

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
