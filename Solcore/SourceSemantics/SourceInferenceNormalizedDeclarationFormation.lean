import Solcore.SourceSemantics.SourceInferenceNormalizedArgumentFormation

/-! The accepted declaration candidate supplies all argument, result and
signature batches used by normalized requirement formation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation SourceInferenceSoundness

private theorem formed_below {context : SourceSemantics.Context} {type : Ty}
    (formed : TypeWellFormed context type) (next : Nat) : type.VariablesBelow next := by
  intro metavariable occurs
  have closed := StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil formed
  simp [closed] at occurs

private theorem batch_inference (state : State) (predicates : List ProgramPredicate) :
    (state.addRequirementsWithIds predicates).2.inference = state.inference := by
  induction predicates generalizing state with
  | nil => rfl
  | cons predicate predicates ih => exact ih (state.addRequirementWithId predicate).2

private theorem batch_origin (state : State) (predicates : List ProgramPredicate)
    {row : Requirement} (member : row ∈ (state.addRequirementsWithIds predicates).2.requirements) :
    row ∈ state.requirements ∨ row.predicate ∈ predicates := by
  induction predicates generalizing state with
  | nil => exact Or.inl member
  | cons predicate predicates ih =>
    rcases ih (state.addRequirementWithId predicate).2 member with old | issued
    · rcases List.mem_append.mp old with old | new
      · exact .inl old
      · simp only [List.mem_singleton] at new
        subst row
        exact .inr (by simp)
    · exact .inr (by simp [issued])

/-- Actual declaration allocation gives an exact rigid substitution. The
selected finalizer's range forms its instantiated type after normalization. -/
theorem instantiated_declaration_type_normalized
    {semantic : SourceSemantics.Context} {context : SourceInference.Context} {outer : Substitution}
    (formation : FormationContext semantic context outer)
    (binders : TypeParameterBindersWellFormed semantic)
    {signature : ProgramFunctionSignature}
    (member : signature ∈ semantic.signatures.functions) (next : Nat) {type : Ty}
    (formed : TypeWellScoped (signatureContext semantic.signatures signature.id
      signature.scheme.parameters signature.scheme.predicates) [] type) :
    TypeAdmissible semantic (outer.apply
      ((signature.scheme.instantiate next).parameterSubstitution.apply type)) := by
  apply type_applySubstitution_residual formation.residual formation.range
  exact StructuralSubstitution.TypeWellScoped.applyParametersAdmissibleTo
    (source := signatureContext semantic.signatures signature.id
      signature.scheme.parameters signature.scheme.predicates)
    (signature.scheme.instantiate next).parameterSubstitution
    (DeclarationInstantiation.instantiate_parameterSubstitution_exact
      signature.scheme next (formation.catalog.function_parameters signature member).1)
    (DeclarationInstantiation.instantiate_parameterSubstitution_rangeAdmissible
      binders formation.residual signature.scheme next) rfl binders formed

/-- No candidate predicate-formation law is assumed: the real accepted
candidate reveals the ordered fits and final signature batch. -/
theorem tryFunctionCandidate_normalized_formation
    {semantic : SourceSemantics.Context} {context : SourceInference.Context} {outer : Substitution}
    {state : State} {arguments : List InferredExpression} {integerOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {signature : ProgramFunctionSignature}
    {result : Detail.CandidateAttemptResult}
    (formation : FormationContext semantic context outer)
    (binders : TypeParameterBindersWellFormed semantic)
    (member : signature ∈ semantic.signatures.functions)
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (argumentsFormed : ∀ argument ∈ arguments, TypeAdmissible semantic (outer.apply argument.type))
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (accepted : Detail.tryFunctionCandidate context arguments integerOrigins call expected state signature =
      .ok (some result)) :
    TypeAdmissible semantic (outer.apply result.result.type) ∧
      ∀ row ∈ result.state.requirements, row ∉ state.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  let instantiated := signature.scheme.instantiate state.inference.next
  let advanced : State := {state with inference := {state.inference with next := instantiated.next}}
  have signatureFormed := formation.catalog.functions_semantic signature member
  have nextLe := ConstrainedDeclarationScheme.instantiate_next_le signature.scheme state.inference.next
  have advanceProgress : state.InferenceProgress advanced :=
    State.InferenceProgress.of_substitution_eq ready.solved nextLe rfl
  have advancedReady := State.InferenceReady.of_progress_of_binderEnvironment_eq ready advanceProgress rfl
  have rangeBelow : ∀ {parameter replacement}, (parameter, replacement) ∈ instantiated.parameterSubstitution →
      replacement.VariablesBelow advanced.inference.next :=
    ConstrainedDeclarationScheme.instantiate_parameterSubstitution_range_variablesBelow
      signature.scheme state.inference.next
  have parametersBelow : ∀ type ∈ signature.parameterTypes.map instantiated.parameterSubstitution.apply,
      type.VariablesBelow advanced.inference.next := by
    intro type typeMember
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp typeMember
    exact ParameterSubstitution.apply_variables_below rangeBelow
      (formed_below (signatureFormed.parameter_types _ originalMember) _)
  have returnsClosed : (Ty.productMany signature.returnTypes).VariablesBelow 0 :=
    Ty.variablesBelow_productMany (fun type member => formed_below (signatureFormed.return_types type member) 0)
  have resultBelow : (instantiated.parameterSubstitution.apply (Ty.productMany signature.returnTypes)).VariablesBelow
      advanced.inference.next :=
    ParameterSubstitution.apply_variables_below rangeBelow (returnsClosed.weaken (Nat.zero_le _))
  have parametersFormed : ∀ type ∈ signature.parameterTypes.map instantiated.parameterSubstitution.apply,
      TypeAdmissible semantic (outer.apply type) := by
    intro type typeMember
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp typeMember
    exact instantiated_declaration_type_normalized formation binders member _
      (signatureFormed.parameter_types _ originalMember).typeWellScoped
  have resultFormed : TypeAdmissible semantic
      (outer.apply (instantiated.parameterSubstitution.apply (Ty.productMany signature.returnTypes))) :=
    instantiated_declaration_type_normalized formation binders member _
      (StructuralSubstitution.TypesWellScoped.productMany
        (StructuralSubstitution.TypesWellFormed.toTypesWellScoped signatureFormed.return_types))
  have predicatesFormed : ∀ predicate ∈ instantiated.predicates,
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer predicate) := by
    intro predicate predicateMember
    exact predicate_applySubstitution_residual formation.residual formation.range
      (instantiated_function_predicates formation.catalog binders formation.residual member _ predicate predicateMember)
  obtain ⟨fittedArguments, fittedResult, trace, fitResult, _, resultEq, _, _, _, stateEq⟩ :=
    Detail.tryFunctionCandidate_some_resultFitAllocationWitness signatureFormed.scheme_body accepted
  have sameInference : result.state.inference = fittedResult.state.inference := by
    rw [stateEq]
    exact batch_inference _ _
  have fittedContinuation : outer.SemanticallyExtends fittedResult.state.inference.substitution := by
    rw [sameInference] at continuation
    exact continuation
  have argumentProgress := trace.inferenceProperties advancedReady
    (fun arg member => (argumentsBelow arg member).weaken advanceProgress.next_le) parametersBelow
  have fittedProperties := Detail.candidateWithExpected_some_inferenceProperties argumentProgress.2
    (resultBelow.weaken argumentProgress.1.next_le)
    (fun type member => (expectedBelow type member).weaken (advanceProgress.trans argumentProgress.1).next_le)
    fitResult
  have argumentContinuation : outer.SemanticallyExtends fittedArguments.state.inference.substitution :=
    fittedContinuation.trans fittedProperties.1.substitution_extends
  have argumentFormation := argumentFitTrace_normalized_issuance formation trace advancedReady
    (fun arg member => (argumentsBelow arg member).weaken advanceProgress.next_le) parametersBelow
    argumentsFormed parametersFormed argumentContinuation
  have fittedFormation := candidateWithExpected_normalized_formation formation fittedContinuation
    resultFormed expectedFormed fitResult
  refine ⟨?_, ?_⟩
  · rw [resultEq]
    have resolved : TypeAdmissible semantic (outer.apply (result.state.resolve fittedResult.expression.type)) :=
      (continuation fittedResult.expression.type).symm ▸ fittedFormation.1
    simpa only [stateEq] using resolved
  · intro row rowMember fresh
    have batchMember : row ∈ (fittedResult.state.addRequirementsWithIds instantiated.predicates).2.requirements := by
      simpa only [stateEq, State.markDirectCallRequirements] using rowMember
    rcases batch_origin _ _ batchMember with old | issued
    · exact new_normalized_requirements_trans argumentFormation fittedFormation.2 row old fresh
    · exact predicatesFormed row.predicate issued

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
