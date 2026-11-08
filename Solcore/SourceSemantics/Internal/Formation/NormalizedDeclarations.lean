import Solcore.SourceSemantics.Internal.Formation.NormalizedCoercions
import Solcore.Frontend.SourceInference.Internal.LocalReadScopes
import Solcore.Frontend.SourceInference.Internal.OccurrenceProperties

/-!
# Normalized declarations

Producers, atoms, binders, captures and declarations under the final substitution, with the
contracts of the recursion.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedDeclarationFormation
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedAtomFormation
/-! Actual integer and nonlocal reference branches produce normalized result
types and every requirement issued before and during expected fitting. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation SourceInferenceSoundness

private theorem allocation_requirements {initial allocated : State} {id : ExpressionId}
    (allocation : initial.allocateExpressionId = (id, allocated)) :
    allocated.requirements = initial.requirements := by
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  rw [same]
  rfl

/-- The actual numeric branch allocates its variable and Int requirement;
final range validation forms that variable without assuming literal typing. -/
theorem inferExprFuel_numeric_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {literal : Syntax.CoreLiteral} {spelling : Syntax.CoreLiteralValue} {rawValue : Nat}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {result : InferredExpression × State}
    (formation : FormationContext semantic context outer)
    (binders : TypeParameterBindersWellFormed semantic)
    (form : expression.value = .literal literal) (literalForm : literal.value = spelling)
    (decoded : Frontend.numericLiteralValue? spelling = some rawValue)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (continuation : outer.SemanticallyExtends result.2.inference.substitution)
    (accepted : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result) :
    TypeAdmissible semantic (outer.apply result.1.type) ∧
      ∀ row ∈ result.2.requirements, row ∉ initial.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  let rawType := allocated.fresh.1
  let addition := allocated.fresh.2.addRequirementWithId (ProgramSignatures.builtinIntPredicate rawType)
  let origin : IntegerLiteralOrigin := {
    metavariable := ⟨allocated.inference.next⟩, expression := id, requirement := addition.1 }
  let literalState : State := {addition.2 with integerLiterals := addition.2.integerLiterals ++ [origin]}
  have rawFormed : TypeAdmissible semantic (outer.apply rawType) :=
    type_applySubstitution_residual formation.residual formation.range
      (.variableOfResidual binders formation.residual ⟨allocated.inference.next⟩)
  have recorded := (Detail.inferExprFuel_success_numericLiteral_record form literalForm decoded allocation accepted).1
  have fitted := recordExpressionWithExpected_normalized_formation formation continuation rawFormed expectedFormed recorded
  refine ⟨fitted.1, new_normalized_requirements_trans (middle := literalState) ?_ fitted.2⟩
  intro row member fresh
  change row ∈ allocated.requirements ++
    [{id := addition.1, predicate := ProgramSignatures.builtinIntPredicate rawType}] at member
  rw [allocation_requirements allocation] at member
  rcases List.mem_append.mp member with old | introduced
  · exact (fresh old).elim
  · cases List.mem_singleton.mp introduced
    exact builtin_integer_predicate rawFormed

/-- A real named-reference lookup fixes the catalog signature whose exact
fresh batch is recorded by this successful identifier inference. -/
theorem inferExprFuel_declaration_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {name : Syntax.Identifier} {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {signature : ProgramFunctionSignature} {result : InferredExpression × State}
    (formation : FormationContext semantic context outer)
    (binders : TypeParameterBindersWellFormed semantic)
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (notLocal : allocated.lookupBinder? name.value = none)
    (notBoolean : (name.value == "true" || name.value == "false") = false)
    (functions : Detail.functionsNamed context name.value = .ok [signature])
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (continuation : outer.SemanticallyExtends result.2.inference.substitution)
    (accepted : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result) :
    TypeAdmissible semantic (outer.apply result.1.type) ∧
      ∀ row ∈ result.2.requirements, row ∉ initial.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  have signatureMember : signature ∈ semantic.signatures.functions := by
    rw [formation.signatures]
    exact Detail.functionsNamed_success_subset_catalog functions (by simp)
  have signatureFormed := formation.catalog.functions_semantic signature signatureMember
  let instantiated := signature.scheme.instantiate allocated.inference.next
  let advanced : State := {allocated with inference := {allocated.inference with next := instantiated.next}}
  let batch := advanced.addRequirementsWithIds instantiated.predicates
  have rawFormed : TypeAdmissible semantic (outer.apply instantiated.body) := by
    rw [ConstrainedDeclarationScheme.instantiate_body]
    apply instantiated_declaration_type_normalized formation binders signatureMember
    rw [signatureFormed.scheme_body]
    exact .function
      (StructuralSubstitution.TypesWellScoped.productMany
        (StructuralSubstitution.TypesWellFormed.toTypesWellScoped signatureFormed.parameter_types))
      (StructuralSubstitution.TypesWellScoped.productMany
        (StructuralSubstitution.TypesWellFormed.toTypesWellScoped signatureFormed.return_types))
  have predicatesFormed : ∀ predicate ∈ instantiated.predicates,
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer predicate) := by
    intro predicate member
    exact predicate_applySubstitution_residual formation.residual formation.range
      (instantiated_function_predicates formation.catalog binders formation.residual signatureMember _ predicate member)
  have recorded := Detail.inferExprFuel_success_declarationIdentifier_record
    form allocation notLocal notBoolean functions accepted
  have fitted := recordExpressionWithExpected_normalized_formation formation continuation rawFormed expectedFormed recorded
  refine ⟨fitted.1, new_normalized_requirements_trans (middle := batch.2) ?_ fitted.2⟩
  intro row member fresh
  rcases batch_origin advanced instantiated.predicates member with old | introduced
  · have present : row ∈ allocated.requirements := old
    rw [allocation_requirements allocation] at present
    exact (fresh present).elim
  · exact predicatesFormed row.predicate introduced

/-- Builtin Boolean references have no initial batch; only their actual
expected fitting can add requirements. -/
theorem inferExprFuel_boolean_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {name : Syntax.Identifier} {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {result : InferredExpression × State}
    (formation : FormationContext semantic context outer)
    (binders : TypeParameterBindersWellFormed semantic)
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (notLocal : allocated.lookupBinder? name.value = none)
    (isBoolean : (name.value == "true" || name.value == "false") = true)
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (continuation : outer.SemanticallyExtends result.2.inference.substitution)
    (accepted : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result) :
    TypeAdmissible semantic (outer.apply result.1.type) ∧
      ∀ row ∈ result.2.requirements, row ∉ initial.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  have recorded := Detail.inferExprFuel_success_builtinBooleanIdentifier_record
    form allocation notLocal isBoolean accepted
  have fitted := recordExpressionWithExpected_normalized_formation formation continuation
    (type_applySubstitution_residual formation.residual formation.range (.bool binders)) expectedFormed recorded
  simpa only [allocation_requirements allocation] using fitted

/-- The actual builtin identifier lookup records its fixed admissible type
before the same successful expected fitting. -/
theorem inferExprFuel_builtin_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {name : Syntax.Identifier} {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {function : BuiltinFunctionId} {result : InferredExpression × State}
    (formation : FormationContext semantic context outer)
    (binders : TypeParameterBindersWellFormed semantic)
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (notLocal : allocated.lookupBinder? name.value = none)
    (notBoolean : (name.value == "true" || name.value == "false") = false)
    (functions : Detail.functionsNamed context name.value = .ok [])
    (builtin : builtinFunctionNamed? name.value = some function)
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (continuation : outer.SemanticallyExtends result.2.inference.substitution)
    (accepted : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result) :
    TypeAdmissible semantic (outer.apply result.1.type) ∧
      ∀ row ∈ result.2.requirements, row ∉ initial.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  have recorded := Detail.inferExprFuel_success_builtinFunctionIdentifier_record
    form allocation notLocal notBoolean functions builtin accepted
  have fitted := recordExpressionWithExpected_normalized_formation formation continuation
    (type_applySubstitution_residual formation.residual formation.range (.builtinFunction binders function)) expectedFormed recorded
  simpa only [allocation_requirements allocation] using fitted

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedLocalFormation
/-! The real local lookup reuses the earlier binder's formation and exact
fresh instantiation, then includes its actual expected-fitting obligations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation SourceInferenceSoundness

/-- This is only scheme instantiation and structural type formation. It does
not require expression typing or evidence entailment for the current use. -/
theorem local_instantiated_type_normalized
    {semantic : SourceSemantics.Context} {outer : Substitution} {binder : TypedBinder}
    (binders : TypeParameterBindersWellFormed semantic)
    (residual : semantic.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible semantic outer)
    (scheme : SchemeWellFormed semantic (binder.applySubstitution outer).scheme)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer binder) (next : Nat) :
    TypeAdmissible semantic (outer.apply (binder.scheme.instantiateWithSubstitution next).body) := by
  let instantiated := binder.scheme.instantiateWithSubstitution next
  have unique : binder.scheme.quantified.Nodup := by simpa using scheme.quantified_nodup
  have exactInner : ExactSubstitution instantiated.substitution binder.scheme.quantified := {
    variables_nodup := unique
    domain_permutation := binder.scheme.instantiateWithSubstitution_substitution_domain_permutation next unique }
  have restricted : outer.without binder.scheme.quantified = outer :=
    FlexibleSubstitution.Substitution.without_eq_self_of_disjoint_domain outer binder.scheme.quantified
      noCapture.quantified_fresh
  have composedRange := FlexibleSubstitution.SubstitutionRangeAdmissible.mapRange_instantiateWithSubstitution
    binder.scheme next binders residual range
  have instantiatedValid : SchemeInstantiatesAt semantic (binder.applySubstitution outer).scheme
      (outer.apply instantiated.body) := by
    refine .intro scheme (FlexibleSubstitution.Substitution.mapRange outer instantiated.substitution)
      (FlexibleSubstitution.Substitution.ExactSubstitution.mapRange outer exactInner) composedRange ?_
    change (FlexibleSubstitution.Substitution.mapRange outer instantiated.substitution).apply
      (binder.applySubstitution outer).scheme.body = outer.apply instantiated.body
    rw [FlexibleSubstitution.applyTypedBinder_scheme]
    change (FlexibleSubstitution.Substitution.mapRange outer instantiated.substitution).apply
      ((outer.without binder.scheme.quantified).apply binder.scheme.body) = outer.apply instantiated.body
    rw [restricted]
    exact (FlexibleSubstitution.Ty.applyFlexible_compose_of_rangeAvoidsVariablesOn outer
      instantiated.substitution exactInner noCapture.quantified_fresh noCapture.body_range).symm
  exact instantiatedValid.type_admissible

/-- The accepted local-reference branch produces its exact predicate batch
and then performs ordinary expected fitting. Earlier binder formation is the
only local scheme input; current-expression typing is not assumed. -/
theorem inferExprFuel_local_normalized_formation
    (lookup : LocalReadEvents.Lookup) {semantic : SourceSemantics.Context} {outer : Substitution}
    (formation : FormationContext semantic lookup.context outer)
    (binders : TypeParameterBindersWellFormed semantic)
    (earlierRequirements : LocalSchemeRequirementsWellFormed semantic (lookup.binder.applySubstitution outer))
    (earlierScheme : SchemeWellFormed semantic (lookup.binder.applySubstitution outer).scheme)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer lookup.binder)
    (beforeContinuation : outer.SemanticallyExtends lookup.advanced.inference.substitution)
    (afterContinuation : outer.SemanticallyExtends lookup.result.2.inference.substitution)
    (expectedFormed : ∀ type ∈ lookup.expected, TypeAdmissible semantic (outer.apply type)) :
    TypeAdmissible semantic (outer.apply lookup.result.1.type) ∧
      ∀ row ∈ lookup.result.2.requirements, row ∉ lookup.initial.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  have bodyFormed := local_instantiated_type_normalized binders formation.residual formation.range
    earlierScheme noCapture lookup.allocated.inference.next
  have resolvedFormed : TypeAdmissible semantic
      (outer.apply (lookup.advanced.resolve
        (lookup.binder.scheme.instantiateWithSubstitution lookup.allocated.inference.next).body)) :=
    (beforeContinuation _).symm ▸ bodyFormed
  have predicatesFormed := local_read_normalized_predicates lookup binders formation.residual formation.range
    earlierRequirements earlierScheme noCapture beforeContinuation
  have recorded := recordExpressionWithExpected_normalized_formation formation afterContinuation
    resolvedFormed expectedFormed lookup.recorded
  refine ⟨recorded.1, new_normalized_requirements_trans (middle := lookup.batch.2) ?_ recorded.2⟩
  intro row member fresh
  rcases batch_origin lookup.advanced lookup.predicates member with old | issued
  · have present : row ∈ lookup.allocated.requirements := old
    have allocatedEq : lookup.allocated = lookup.initial.allocateExpressionId.2 :=
      (congrArg Prod.snd lookup.allocation).symm
    rw [allocatedEq] at present
    exact (fresh present).elim
  · exact predicatesFormed row.predicate issued

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedBinderFormation
/-! A producer invariant contains only structural normalized body/predicate
formation and actual allocator/no-capture facts. It does not contain evidence
entailment, template validity or typing for the current initializer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation SourceInferenceSoundness

structure NormalizedBinderFormation (semantic : SourceSemantics.Context)
    (outer : Substitution) (binder : TypedBinder) : Prop where
  unique : binder.scheme.quantified.Nodup
  body : TypeAdmissible semantic (outer.apply binder.scheme.body)
  predicates : ∀ requirement ∈ binder.schemeRequirements,
    PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer requirement.predicate)
  noCapture : Detail.LocalBinderInstantiationNoCapture outer binder

structure NormalizedStateFormation (semantic : SourceSemantics.Context)
    (outer : Substitution) (state : State) : Prop where
  requirements : ∀ row ∈ state.requirements,
    PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate)
  binders : ∀ binder ∈ state.localBinders, NormalizedBinderFormation semantic outer binder

namespace NormalizedBinderFormation

theorem mono {semantic : SourceSemantics.Context} {outer : Substitution}
    (state : State) (name : String) (type : Ty) (span : Option Syntax.SourceSpan)
    (comptime : Bool) (body : TypeAdmissible semantic (outer.apply type)) :
    NormalizedBinderFormation semantic outer
      (state.allocateBinder name (.mono type) span comptime).1 :=
  ⟨by simp [State.allocateBinder, Scheme.mono], body, by simp [State.allocateBinder],
    Detail.LocalBinderInstantiationNoCapture.of_quantified_eq_nil rfl⟩

theorem instantiate {semantic : SourceSemantics.Context} {context : SourceInference.Context}
    {outer : Substitution} {binder : TypedBinder}
    (binderFormed : NormalizedBinderFormation semantic outer binder)
    (formation : FormationContext semantic context outer)
    (binders : TypeParameterBindersWellFormed semantic) (next : Nat) :
    TypeAdmissible semantic (outer.apply (binder.scheme.instantiateWithSubstitution next).body) ∧
      ∀ requirement ∈ binder.schemeRequirements,
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer
          (TypedTraitResolution.applySubstitution
            (binder.scheme.instantiateWithSubstitution next).substitution requirement.predicate)) := by
  let inner := (binder.scheme.instantiateWithSubstitution next).substitution
  have exactInner : ExactSubstitution inner binder.scheme.quantified := {
    variables_nodup := binderFormed.unique
    domain_permutation := binder.scheme.instantiateWithSubstitution_substitution_domain_permutation next binderFormed.unique }
  have range := FlexibleSubstitution.SubstitutionRangeAdmissible.mapRange_instantiateWithSubstitution
    binder.scheme next binders formation.residual formation.range
  constructor
  · change TypeAdmissible semantic (outer.apply (inner.apply binder.scheme.body))
    rw [FlexibleSubstitution.Ty.applyFlexible_compose_of_rangeAvoidsVariablesOn outer inner exactInner
      binderFormed.noCapture.quantified_fresh binderFormed.noCapture.body_range]
    exact type_applySubstitution_residual formation.residual range binderFormed.body
  · intro requirement member
    rw [FlexibleSubstitution.TypedTraitResolution.applySubstitution_compose_of_rangeAvoidsVariablesOn
      outer inner exactInner binderFormed.noCapture.quantified_fresh
      (localBinderInstantiationNoCapture_predicateRangeAvoids binderFormed.noCapture requirement member)]
    exact predicate_applySubstitution_residual formation.residual range (binderFormed.predicates requirement member)

/-- Generalization copies its actual input type and selects predicates from
its actual ready ledger. One final continuation normalizes both fields. -/
theorem generalized
    {semantic : SourceSemantics.Context} {outer : Substitution} {state : State} {type : Ty}
    (locals : Environment) (cutoff : Nat) (name : String)
    (span : Option Syntax.SourceSpan) (comptime : Bool)
    (continuation : outer.SemanticallyExtends state.inference.substitution)
    (body : TypeAdmissible semantic (outer.apply type))
    (requirements : ∀ row ∈ state.requirements,
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate))
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer
      (state.allocateBinder name (Detail.generalizeValue state locals cutoff type).scheme span comptime
        (Detail.generalizeValue state locals cutoff type).requirements).1) :
    NormalizedBinderFormation semantic outer
      (state.allocateBinder name (Detail.generalizeValue state locals cutoff type).scheme span comptime
        (Detail.generalizeValue state locals cutoff type).requirements).1 := by
  refine ⟨Detail.generalizeValue_scheme_quantified_nodup state locals cutoff type, body, ?_, noCapture⟩
  intro requirement member
  obtain ⟨raw, rawMember, _, predicateEq⟩ :=
    Detail.generalizeValue_requirement_source state locals cutoff type requirement member
  rw [predicateEq]
  have normalized : TypedTraitResolution.applySubstitution outer (Detail.applyPredicate state raw.predicate) =
      TypedTraitResolution.applySubstitution outer raw.predicate := by
    cases raw.predicate with
    | mk trait subject arguments =>
      simp only [Detail.applyPredicate, TypedTraitResolution.applySubstitution]
      congr 1
      · exact continuation subject
      · simp only [List.map_map]
        exact List.map_congr_left (fun type _ => continuation type)
  rw [normalized]
  exact requirements raw rawMember

end NormalizedBinderFormation

namespace NormalizedStateFormation

theorem of_new_rows {semantic : SourceSemantics.Context} {outer : Substitution}
    {before after : State} (formed : NormalizedStateFormation semantic outer before)
    (binders : after.localBinders = before.localBinders)
    (issued : ∀ row ∈ after.requirements, row ∉ before.requirements →
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate)) :
    NormalizedStateFormation semantic outer after := by
  refine ⟨?_, ?_⟩
  · intro row member
    by_cases old : row ∈ before.requirements
    · exact formed.requirements row old
    · exact issued row member old
  · intro binder member
    exact formed.binders binder (binders ▸ member)

theorem congr {semantic : SourceSemantics.Context} {outer : Substitution}
    {before after : State} (formed : NormalizedStateFormation semantic outer before)
    (binders : after.localBinders = before.localBinders)
    (rows : after.requirements = before.requirements) :
    NormalizedStateFormation semantic outer after :=
  formed.of_new_rows binders (fun _ member fresh => (fresh (rows ▸ member)).elim)

/-- Scope restoration uses a real saved scope whose binders had formation at
entry. The later ledger keeps the facts accumulated inside the scope. -/
theorem restore {semantic : SourceSemantics.Context} {outer : Substitution}
    {before after : State} (entry : NormalizedStateFormation semantic outer before)
    (later : NormalizedStateFormation semantic outer after)
    (scope : LexicalScope) (saved : scope.binders ⊆ before.localBinders) :
    NormalizedStateFormation semantic outer (after.restoreLexicalScope scope) :=
  ⟨later.requirements, fun binder member => entry.binders binder (saved member)⟩

theorem allocate {semantic : SourceSemantics.Context} {outer : Substitution}
    {state : State} (formed : NormalizedStateFormation semantic outer state)
    (name : String) (scheme : Scheme) (span : Option Syntax.SourceSpan) (comptime : Bool)
    (requirements : List LocalSchemeRequirement)
    (newBinder : NormalizedBinderFormation semantic outer
      (state.allocateBinder name scheme span comptime requirements).1) :
    NormalizedStateFormation semantic outer
      (state.allocateBinder name scheme span comptime requirements).2 := by
  refine ⟨formed.requirements, ?_⟩
  intro binder member
  rcases List.mem_cons.mp member with rfl | old
  · exact newBinder
  · exact formed.binders binder old

end NormalizedStateFormation

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedCaptureFormation
/-! Finalizer capture checks travel backwards along the actual node table.
Header items carry their binders explicitly until the enclosing for node is
recorded. Expression coercion attachment preserves this binder inventory. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceSoundness

def NoCaptureBinders (outer : Substitution) (binders : List TypedBinder) : Prop :=
  ∀ binder ∈ binders, Detail.LocalBinderInstantiationNoCapture outer binder

def NoCaptureNodes (outer : Substitution) (nodes : List Node) : Prop :=
  NoCaptureBinders outer (nodes.flatMap Node.initializedLetBinders)

def NoCaptureItems (outer : Substitution) (items : List ForItemForm) : Prop :=
  NoCaptureBinders outer (items.flatMap ForItemForm.initializedLetBinders)

namespace NoCaptureNodes

theorem mono {outer : Substitution} {before after : List Node}
    (formed : NoCaptureNodes outer after) (subset : before ⊆ after) :
    NoCaptureNodes outer before := by
  intro binder member
  obtain ⟨node, present, selected⟩ := List.mem_flatMap.mp member
  exact formed binder (List.mem_flatMap.mpr ⟨node, subset present, selected⟩)

theorem of_prefix {outer : Substitution} {before after : List Node}
    (formed : NoCaptureNodes outer after) (retained : before <+: after) :
    NoCaptureNodes outer before := formed.mono retained.subset

theorem at_statement {outer : Substitution} {nodes : List Node}
    (formed : NoCaptureNodes outer nodes) {node : StatementNode}
    (member : .statement node ∈ nodes) :
    NoCaptureBinders outer node.form.initializedLetBinders :=
  fun binder selected => formed binder (List.mem_flatMap.mpr ⟨_, member, selected⟩)

theorem of_finalizer
    {context : SourceInference.Context} {expectedReturn : Ty} {state : State}
    {roots : List NodeId} {result : SourceInference.Result}
    (resources : FinalInferenceResources context expectedReturn state roots result) :
    NoCaptureNodes result.substitution state.nodes :=
  resources.local_no_capture

theorem modifyExpressionNode_inventory (state : State) (id : ExpressionId)
    (modify : ExpressionNode → ExpressionNode) :
    (state.modifyExpressionNode id modify).nodes.flatMap Node.initializedLetBinders =
      state.nodes.flatMap Node.initializedLetBinders := by
  change (state.nodes.map _).flatMap _ = _
  rw [List.flatMap_map]
  apply congrArg (fun operation : Node → List TypedBinder => state.nodes.flatMap operation)
  funext node
  cases node with
  | expression node => simp only; split <;> rfl
  | statement node => rfl

theorem attachExpressionCoercions_inventory (state : State)
    (entries : List Detail.ExpressionCoercions) :
    (Detail.attachExpressionCoercions state entries).nodes.flatMap Node.initializedLetBinders =
      state.nodes.flatMap Node.initializedLetBinders := by
  unfold Detail.attachExpressionCoercions
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih =>
      exact (ih _).trans (modifyExpressionNode_inventory _ _ _)

theorem before_attachExpressionCoercions {outer : Substitution} {state : State}
    {entries : List Detail.ExpressionCoercions}
    (formed : NoCaptureNodes outer (Detail.attachExpressionCoercions state entries).nodes) :
    NoCaptureNodes outer state.nodes := by
  unfold NoCaptureNodes at formed ⊢
  rwa [attachExpressionCoercions_inventory] at formed

theorem for_items {outer : Substitution} {nodes : List Node}
    {id : StatementId} {span : Syntax.SourceSpan} {type : Ty}
    {initializer post : List ForItemForm} {condition : ExpressionId}
    {body : List StatementId}
    (formed : NoCaptureNodes outer nodes)
    (recorded : .statement {
      id := id
      span := span
      type := type
      form := .forLoop initializer condition post body } ∈ nodes) :
    NoCaptureItems outer initializer ∧ NoCaptureItems outer post := by
  have binders := formed.at_statement recorded
  exact ⟨fun binder member => binders binder (List.mem_append_left _ member),
    fun binder member => binders binder (List.mem_append_right _ member)⟩

end NoCaptureNodes

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedEntryFormation
/-! The real declaration entry has an empty requirement ledger and only
monomorphic parameter binders. Its normalized formation comes from the
accepted signature catalog and the same final substitution range. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation SourceInferenceSoundness

namespace NormalizedStateFormation

theorem initial
    {semantic : SourceSemantics.Context} {outer : Substitution}
    (owner : Resolved.DeclarationId) (locals : Environment) (comptime : List Bool)
    (monomorphic : ∀ entry ∈ locals, entry.2.quantified = [])
    (formed : ∀ entry ∈ locals, TypeAdmissible semantic (outer.apply entry.2.body)) :
    NormalizedStateFormation semantic outer (State.initial owner locals comptime) := by
  refine ⟨by simp [State.initial], ?_⟩
  intro binder member
  rw [← State.initial_inputs_eq_localBinders, State.initial_inputs_definition] at member
  obtain ⟨index, below, binderEq⟩ := List.exists_of_mem_mapIdx member
  subst binder
  have entryMember := List.getElem_mem below
  have quantified := monomorphic locals[index] entryMember
  refine ⟨?_, formed _ entryMember, by simp, ?_⟩
  · simpa only [quantified] using (List.nodup_nil : ([] : List TypeVarId).Nodup)
  · exact Detail.LocalBinderInstantiationNoCapture.of_quantified_eq_nil quantified

end NormalizedStateFormation

/-- All input formation hypotheses are discharged by the actual signature
and final range; no body typing or generalized-initializer law is used. -/
theorem function_entry_normalized_formation
    {semantic : SourceSemantics.Context} {context : SourceInference.Context}
    {outer : Substitution} {signature : ProgramFunctionSignature}
    (formation : FormationContext semantic context outer)
    (member : signature ∈ semantic.signatures.functions)
    (parameters : semantic.typeParameters = signature.scheme.parameters)
    (owner : semantic.currentDeclaration = some signature.id)
    (declaration : Resolved.DeclarationId) :
    NormalizedStateFormation semantic outer
      (State.initial declaration
        ((signature.parameterNames.zip signature.parameterTypes).map
          fun parameter => (parameter.1, Scheme.mono parameter.2))
        signature.parameterComptime) := by
  apply NormalizedStateFormation.initial
  · intro entry entryMember
    obtain ⟨parameter, _, rfl⟩ := List.mem_map.mp entryMember
    rfl
  · intro entry entryMember
    obtain ⟨parameter, parameterMember, rfl⟩ := List.mem_map.mp entryMember
    have formed := (formation.catalog.functions_semantic signature member).parameter_types
      parameter.2 (List.of_mem_zip parameterMember).2
    apply type_applySubstitution_residual formation.residual formation.range
    exact TypeAdmissible.ofWellFormed (StructuralSubstitution.TypeWellFormed.transportContext
      (source := signatureContext semantic.signatures signature.id
        signature.scheme.parameters signature.scheme.predicates)
      (target := semantic)
      rfl parameters owner formed)

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedLocalIssuance
/-! A local-reference producer needs structural facts about the earlier
binder; template evidence and current-expression typing are not inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation SourceInferenceSoundness

private theorem normalize_predicate {outer : Substitution} {state : State}
    (continuation : outer.SemanticallyExtends state.inference.substitution) (predicate : ProgramPredicate) :
    TypedTraitResolution.applySubstitution outer (Detail.applyPredicate state predicate) =
      TypedTraitResolution.applySubstitution outer predicate := by
  cases predicate with
  | mk trait subject arguments =>
    simp only [Detail.applyPredicate, TypedTraitResolution.applySubstitution]
    congr 1
    · exact continuation subject
    · simp only [List.map_map]
      exact List.map_congr_left (fun type _ => continuation type)

theorem lookup_normalized_formation
    (lookup : LocalReadEvents.Lookup) {semantic : SourceSemantics.Context} {outer : Substitution}
    (formation : FormationContext semantic lookup.context outer)
    (binders : TypeParameterBindersWellFormed semantic)
    (earlier : NormalizedBinderFormation semantic outer lookup.binder)
    (beforeContinuation : outer.SemanticallyExtends lookup.advanced.inference.substitution)
    (afterContinuation : outer.SemanticallyExtends lookup.result.2.inference.substitution)
    (expectedFormed : ∀ type ∈ lookup.expected, TypeAdmissible semantic (outer.apply type)) :
    TypeAdmissible semantic (outer.apply lookup.result.1.type) ∧
      ∀ row ∈ lookup.result.2.requirements, row ∉ lookup.initial.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  have instantiated := earlier.instantiate formation binders lookup.allocated.inference.next
  have resolvedFormed : TypeAdmissible semantic
      (outer.apply (lookup.advanced.resolve
        (lookup.binder.scheme.instantiateWithSubstitution lookup.allocated.inference.next).body)) :=
    (beforeContinuation _).symm ▸ instantiated.1
  have predicatesFormed : ∀ predicate ∈ lookup.predicates,
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer predicate) := by
    intro predicate member
    obtain ⟨requirement, requirementMember, rfl⟩ := List.mem_map.mp member
    rw [normalize_predicate beforeContinuation]
    exact instantiated.2 requirement requirementMember
  have recorded := recordExpressionWithExpected_normalized_formation formation afterContinuation
    resolvedFormed expectedFormed lookup.recorded
  refine ⟨recorded.1, new_normalized_requirements_trans (middle := lookup.batch.2) ?_ recorded.2⟩
  intro row member fresh
  rcases batch_origin lookup.advanced lookup.predicates member with old | issued
  · have present : row ∈ lookup.allocated.requirements := old
    have allocatedEq : lookup.allocated = lookup.initial.allocateExpressionId.2 :=
      (congrArg Prod.snd lookup.allocation).symm
    rw [allocatedEq] at present
    exact (fresh present).elim
  · exact predicatesFormed row.predicate issued

/-- Actual lookup membership selects the earlier binder from the input
invariant. The complete accepted branch updates the real ledger and returns
the same executable lexical scope. -/
theorem lookup_normalized_state
    (lookup : LocalReadEvents.Lookup) {semantic : SourceSemantics.Context} {outer : Substitution}
    (formation : FormationContext semantic lookup.context outer)
    (binders : TypeParameterBindersWellFormed semantic)
    (initial : NormalizedStateFormation semantic outer lookup.initial)
    (beforeContinuation : outer.SemanticallyExtends lookup.advanced.inference.substitution)
    (afterContinuation : outer.SemanticallyExtends lookup.result.2.inference.substitution)
    (expectedFormed : ∀ type ∈ lookup.expected, TypeAdmissible semantic (outer.apply type)) :
    TypeAdmissible semantic (outer.apply lookup.result.1.type) ∧
      NormalizedStateFormation semantic outer lookup.result.2 := by
  have member := (State.lookupBinder?_eq_some_facts lookup.found).1
  have allocatedEq : lookup.allocated = lookup.initial.allocateExpressionId.2 :=
    (congrArg Prod.snd lookup.allocation).symm
  rw [allocatedEq] at member
  have produced := lookup_normalized_formation lookup formation binders
    (initial.binders lookup.binder member) beforeContinuation afterContinuation expectedFormed
  exact ⟨produced.1, initial.of_new_rows
    (congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq lookup.accepted)) produced.2⟩

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedGeneralizationFormation
/-! Actual initialized let and header receipts install their generalized
binder using normalized initializer/ledger formation. No current initializer
typing or retained-template evidence is required for this producer step. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation SourceInferenceSoundness

/-- Both optional annotation paths use the same real initializer return and
allocation. The no-capture certificate belongs to that exact emitted binder. -/
theorem initialized_statement_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : Detail.StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    (ready : NormalizedStateFormation semantic outer receipt.ready)
    (value : TypeAdmissible semantic (outer.apply receipt.value.type))
    (continuation : outer.SemanticallyExtends receipt.ready.inference.substitution)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer receipt.binding.1) :
    NormalizedBinderFormation semantic outer receipt.binding.1 ∧
      NormalizedStateFormation semantic outer result.state := by
  have localsFormed : NormalizedStateFormation semantic outer (receipt.ready.withLocals receipt.locals) :=
    ready.congr rfl rfl
  have valueFormed : TypeAdmissible semantic (outer.apply (receipt.ready.resolve receipt.value.type)) :=
    (continuation _).symm ▸ value
  have binderFormed : NormalizedBinderFormation semantic outer receipt.binding.1 :=
    NormalizedBinderFormation.generalized receipt.locals initial.nextRequirement receipt.name.value
      (some receipt.name.span) false continuation valueFormed ready.requirements noCapture
  have allocated := localsFormed.allocate receipt.name.value receipt.generalized.scheme
    (some receipt.name.span) false receipt.generalized.requirements binderFormed
  refine ⟨binderFormed, ?_⟩
  rw [receipt.completed]
  exact allocated.congr rfl rfl

/-- Header receipts return the actual binder as metadata before the enclosing
for statement records it. The same formation result enters the next item. -/
theorem initialized_header_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    (ready : NormalizedStateFormation semantic outer receipt.ready)
    (value : TypeAdmissible semantic (outer.apply receipt.value.type))
    (continuation : outer.SemanticallyExtends receipt.ready.inference.substitution)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer receipt.binding.1) :
    NormalizedBinderFormation semantic outer receipt.binding.1 ∧
      NormalizedStateFormation semantic outer result.2 := by
  have localsFormed : NormalizedStateFormation semantic outer (receipt.ready.withLocals receipt.locals) :=
    ready.congr rfl rfl
  have valueFormed : TypeAdmissible semantic (outer.apply (receipt.ready.resolve receipt.value.type)) :=
    (continuation _).symm ▸ value
  have binderFormed : NormalizedBinderFormation semantic outer receipt.binding.1 :=
    NormalizedBinderFormation.generalized receipt.locals initial.nextRequirement receipt.name.value
      (some receipt.name.span) false continuation valueFormed ready.requirements noCapture
  have allocated := localsFormed.allocate receipt.name.value receipt.generalized.scheme
    (some receipt.name.span) false receipt.generalized.requirements binderFormed
  refine ⟨binderFormed, ?_⟩
  rw [receipt.completed]
  exact allocated

/-- The real finalizer supplies no-capture for the receipt's actual recorded
statement binder. Node retention is the executable continuation's input. -/
theorem initialized_statement_normalized_from_finalizer
    {whole : SourceInference.Context} {wholeReturn : Ty} {evidence : State}
    {roots : List NodeId} {finalized : SourceInference.Result}
    (resources : FinalInferenceResources whole wholeReturn evidence roots finalized)
    {semantic : SourceSemantics.Context} {fuel : Nat} {context : SourceInference.Context}
    {source : Syntax.Statement} {initial : State} {result : Detail.StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    (ready : NormalizedStateFormation semantic finalized.substitution receipt.ready)
    (value : TypeAdmissible semantic (finalized.substitution.apply receipt.value.type))
    (continuation : finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution)
    (retained : result.state.nodes ⊆ evidence.nodes) :
    NormalizedBinderFormation semantic finalized.substitution receipt.binding.1 ∧
      NormalizedStateFormation semantic finalized.substitution result.state := by
  apply initialized_statement_normalized_formation receipt ready value continuation
  apply resources.local_no_capture
  apply List.mem_flatMap.mpr
  refine ⟨.statement {
    id := initial.allocateStatementId.1, span := source.span, type := .unit,
    form := .letDecl receipt.binding.1 (some receipt.value.id) }, retained receipt.recorded, ?_⟩
  exact List.mem_singleton_self _

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedContracts
/-! Contracts for normalized formation along the actual mutually recursive
inference calls. The outer substitution is the eventual real finalizer's
substitution. Capture checks refer only to actual returned node/header
inventories; the whole-body finalizer discharges these terminal conditions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness

structure InferenceFormationContext (semantic : SourceSemantics.Context)
    (context : SourceInference.Context) (outer : Substitution) : Prop
    extends FormationContext semantic context outer where
  scope : ProducerScope context semantic
  canonical : SignatureParametersWellFormed context.scope.genericOwner context.typeParameters
  validated : ProgramSignatureFormationValidated context.signatures
  functionShapes : ∀ signature ∈ context.signatures.functions,
    signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
      (Ty.productMany signature.returnTypes)

def InferExprFuelFormation
    (semantic : SourceSemantics.Context) (outer : Substitution) (fuel : Nat) (context : SourceInference.Context) (expression : Syntax.Expr)
    (expected : Option Ty) (state : State) : Prop :=
  state.InferenceReady →
    state.NodesBelowNextOccurrence →
    NormalizedStateFormation semantic outer state →
    InferenceFormationContext semantic context outer →
    (∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next) →
    (∀ expectedType ∈ expected, TypeAdmissible semantic (outer.apply expectedType)) →
    ∀ result,
      inferExprFuel fuel context expression expected state = .ok result →
      outer.SemanticallyExtends result.2.inference.substitution →
      NoCaptureNodes outer result.2.nodes →
      TypeAdmissible semantic (outer.apply result.1.type) ∧
        NormalizedStateFormation semantic outer result.2

def InferConstructorApplicationFuelFormation
    (semantic : SourceSemantics.Context) (outer : Substitution) (fuel : Nat) (context : SourceInference.Context) (source : Syntax.Expr)
    (id : ExpressionId) (instantiation : DataConstructorInstantiation)
    (arguments : List Syntax.Expr) (expected : Option Ty)
    (state : State) : Prop :=
  state.InferenceReady →
    state.NodesBelowNextOccurrence →
    NormalizedStateFormation semantic outer state →
    InferenceFormationContext semantic context outer →
    (∀ payload ∈ instantiation.payloadTypes,
      payload.VariablesBelow state.inference.next) →
    (∀ payload ∈ instantiation.payloadTypes, TypeAdmissible semantic (outer.apply payload)) →
    instantiation.resultType.VariablesBelow state.inference.next →
    TypeAdmissible semantic (outer.apply instantiation.resultType) →
    (∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next) →
    (∀ expectedType ∈ expected, TypeAdmissible semantic (outer.apply expectedType)) →
    ∀ result,
      inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state = .ok result →
      outer.SemanticallyExtends result.2.inference.substitution →
      NoCaptureNodes outer result.2.nodes →
      TypeAdmissible semantic (outer.apply result.1.type) ∧
        NormalizedStateFormation semantic outer result.2

def InferConstructorArgumentsFuelFormation
    (semantic : SourceSemantics.Context) (outer : Substitution) (fuel : Nat) (context : SourceInference.Context) (sources : List Syntax.Expr)
    (expectedTypes : List Ty) (state : State) : Prop :=
  state.InferenceReady →
    state.NodesBelowNextOccurrence →
    NormalizedStateFormation semantic outer state →
    InferenceFormationContext semantic context outer →
    (∀ expectedType ∈ expectedTypes,
      expectedType.VariablesBelow state.inference.next) →
    (∀ expectedType ∈ expectedTypes, TypeAdmissible semantic (outer.apply expectedType)) →
    ∀ result,
      inferConstructorArgumentsFuel fuel context sources expectedTypes state =
          .ok result →
      outer.SemanticallyExtends result.2.inference.substitution →
      NoCaptureNodes outer result.2.nodes →
      (∀ expression ∈ result.1, TypeAdmissible semantic (outer.apply expression.type)) ∧
        NormalizedStateFormation semantic outer result.2

def InferStatementsFuelFormation
    (semantic : SourceSemantics.Context) (outer : Substitution) (fuel : Nat) (context : SourceInference.Context) (statements : List Syntax.Statement)
    (expectedReturn : Ty) (state : State) : Prop :=
  state.InferenceReady →
    state.NodesBelowNextOccurrence →
    NormalizedStateFormation semantic outer state →
    InferenceFormationContext semantic context outer →
    expectedReturn.VariablesBelow state.inference.next →
    TypeAdmissible semantic (outer.apply expectedReturn) →
    ∀ result,
      inferStatementsFuel fuel context statements expectedReturn state =
          .ok result →
      outer.SemanticallyExtends result.state.inference.substitution →
      NoCaptureNodes outer result.state.nodes →
      TypeAdmissible semantic (outer.apply result.type) ∧
        NormalizedStateFormation semantic outer result.state

def InferStatementFuelFormation
    (semantic : SourceSemantics.Context) (outer : Substitution) (fuel : Nat) (context : SourceInference.Context) (statement : Syntax.Statement)
    (expectedReturn : Ty) (state : State) : Prop :=
  state.InferenceReady →
    state.NodesBelowNextOccurrence →
    NormalizedStateFormation semantic outer state →
    InferenceFormationContext semantic context outer →
    expectedReturn.VariablesBelow state.inference.next →
    TypeAdmissible semantic (outer.apply expectedReturn) →
    ∀ result,
      inferStatementFuel fuel context statement expectedReturn state =
          .ok result →
      outer.SemanticallyExtends result.state.inference.substitution →
      NoCaptureNodes outer result.state.nodes →
      TypeAdmissible semantic (outer.apply result.type) ∧
        NormalizedStateFormation semantic outer result.state

def InferForItemsFuelFormation
    (semantic : SourceSemantics.Context) (outer : Substitution) (fuel : Nat) (context : SourceInference.Context) (items : List Syntax.ForItem)
    (state : State) : Prop :=
  state.InferenceReady →
    state.NodesBelowNextOccurrence →
    NormalizedStateFormation semantic outer state →
    InferenceFormationContext semantic context outer →
    ∀ result,
      inferForItemsFuel fuel context items state = .ok result →
      outer.SemanticallyExtends result.state.inference.substitution →
      NoCaptureNodes outer result.state.nodes →
      NoCaptureItems outer result.items →
      NormalizedStateFormation semantic outer result.state

def InferForItemFuelFormation
    (semantic : SourceSemantics.Context) (outer : Substitution) (fuel : Nat) (context : SourceInference.Context) (item : Syntax.ForItem)
    (state : State) : Prop :=
  state.InferenceReady →
    state.NodesBelowNextOccurrence →
    NormalizedStateFormation semantic outer state →
    InferenceFormationContext semantic context outer →
    ∀ result,
      inferForItemFuel fuel context item state = .ok result →
      outer.SemanticallyExtends result.2.inference.substitution →
      NoCaptureNodes outer result.2.nodes →
      NoCaptureItems outer [result.1] →
      NormalizedStateFormation semantic outer result.2

def InferPlaceFuelFormation
    (semantic : SourceSemantics.Context) (outer : Substitution) (fuel : Nat) (context : SourceInference.Context) (target : Syntax.Expr)
    (state : State) : Prop :=
  state.InferenceReady →
    state.NodesBelowNextOccurrence →
    NormalizedStateFormation semantic outer state →
    InferenceFormationContext semantic context outer →
    ∀ result,
      inferPlaceFuel fuel context target state = .ok result →
      outer.SemanticallyExtends result.2.inference.substitution →
      NoCaptureNodes outer result.2.nodes →
      TypeAdmissible semantic (outer.apply result.1.type) ∧
        NormalizedStateFormation semantic outer result.2

def InferAssignedValueFuelFormation
    (semantic : SourceSemantics.Context) (outer : Substitution) (fuel : Nat) (context : SourceInference.Context) (target : Syntax.Expr)
    (operator : Syntax.ValueAssignOp) (value : Syntax.Expr)
    (state : State) : Prop :=
  state.InferenceReady →
    state.NodesBelowNextOccurrence →
    NormalizedStateFormation semantic outer state →
    InferenceFormationContext semantic context outer →
    ∀ result,
      inferAssignedValueFuel fuel context target operator value state =
          .ok result →
      outer.SemanticallyExtends result.2.2.inference.substitution →
      NoCaptureNodes outer result.2.2.nodes →
      TypeAdmissible semantic (outer.apply result.1.target.type) ∧
        TypeAdmissible semantic (outer.apply result.2.1.type) ∧
        NormalizedStateFormation semantic outer result.2.2

def InferExprsFuelFormation
    (semantic : SourceSemantics.Context) (outer : Substitution) (fuel : Nat) (context : SourceInference.Context) (expressions : List Syntax.Expr)
    (state : State) : Prop :=
  state.InferenceReady →
    state.NodesBelowNextOccurrence →
    NormalizedStateFormation semantic outer state →
    InferenceFormationContext semantic context outer →
    ∀ result,
      inferExprsFuel fuel context expressions state = .ok result →
      outer.SemanticallyExtends result.2.inference.substitution →
      NoCaptureNodes outer result.2.nodes →
      (∀ expression ∈ result.1, TypeAdmissible semantic (outer.apply expression.type)) ∧
        NormalizedStateFormation semantic outer result.2

def InferMatchCasesFuelFormation
    (semantic : SourceSemantics.Context) (outer : Substitution) (fuel : Nat) (context : SourceInference.Context) (scrutineeType expectedReturn : Ty)
    (outerScope : LexicalScope) (cases : List Syntax.MatchCase)
    (state : State) : Prop :=
  state.InferenceReady →
    state.NodesBelowNextOccurrence →
    NormalizedStateFormation semantic outer state →
    InferenceFormationContext semantic context outer →
    scrutineeType.VariablesBelow state.inference.next →
    TypeAdmissible semantic (outer.apply scrutineeType) →
    expectedReturn.VariablesBelow state.inference.next →
    TypeAdmissible semantic (outer.apply expectedReturn) →
    state.lexicalScope = outerScope →
    ∀ result,
      inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state = .ok result →
      outer.SemanticallyExtends result.state.inference.substitution →
      NoCaptureNodes outer result.state.nodes →
      NormalizedStateFormation semantic outer result.state

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedCallFormation
/-! Actual overload and call recording preserve normalized formation. The
recorded nodes retain the exact initialized-binder inventory. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness SourceInferenceRequirementFormation

private theorem attach_fields (state : State) (entries : List ExpressionCoercions) :
    (attachExpressionCoercions state entries).inference = state.inference ∧
      (attachExpressionCoercions state entries).localBinders = state.localBinders ∧
      (attachExpressionCoercions state entries).requirements = state.requirements := by
  induction entries generalizing state with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons entry rest ih => exact ih (state.modifyExpressionNode entry.expression
      (fun node => appendExpressionCoercions node entry.coercions))

theorem recordSelectedCallResult_normalized_fields
    (source callee : Syntax.Expr) (name : String) (arguments : List InferredExpression)
    (attempt : CandidateAttemptResult) (result : InferredExpression)
    (coercions : List CoercionStep) (state : State) :
    let recorded := recordSelectedCallResult source callee name arguments attempt result coercions state
    recorded.2.inference = state.inference ∧ recorded.2.localBinders = state.localBinders ∧
      recorded.2.requirements = state.requirements ∧ recorded.1.type = result.type ∧
      recorded.2.nodes.flatMap Node.initializedLetBinders = state.nodes.flatMap Node.initializedLetBinders := by
  dsimp only
  have fields := attach_fields state attempt.argumentCoercions
  refine ⟨fields.1,fields.2.1,fields.2.2,rfl,?_⟩
  simp only [recordSelectedCallResult, recordExpression, State.recordNode, State.allocateExpressionId,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, Node.initializedLetBinders,
    List.append_nil]
  exact NoCaptureNodes.attachExpressionCoercions_inventory state attempt.argumentCoercions

theorem recordIndirectCall_normalized_fields
    (source : Syntax.Expr) (callee : InferredExpression) (arguments : List InferredExpression)
    (application : IndirectApplicationResult) :
    let recorded := recordIndirectCall source callee arguments application
    recorded.2.inference = application.state.inference ∧
      recorded.2.localBinders = application.state.localBinders ∧
      recorded.2.requirements = application.state.requirements ∧
      recorded.1.type = application.result.type ∧
      recorded.2.nodes.flatMap Node.initializedLetBinders = application.state.nodes.flatMap Node.initializedLetBinders := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  simp only [recordIndirectCall, recordExpression, State.recordNode, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, Node.initializedLetBinders, List.append_nil]

theorem selectFunctionCandidateFrom_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution} {context : SourceInference.Context}
    {state : State} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {result : CandidateAttemptResult}
    (formation : InferenceFormationContext semantic context outer)
    (formed : NormalizedStateFormation semantic outer state)
    (cataloged : candidates ⊆ context.signatures.functions)
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (argumentsFormed : ∀ argument ∈ arguments, TypeAdmissible semantic (outer.apply argument.type))
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (accepted : selectFunctionCandidateFrom context name candidates arguments integerOrigins call expected state = .ok result) :
    TypeAdmissible semantic (outer.apply result.result.type) ∧
      NormalizedStateFormation semantic outer result.state := by
  obtain ⟨signature,member,tried⟩ := selectFunctionCandidateFrom_success_candidate accepted
  have produced := tryFunctionCandidate_normalized_formation formation.toFormationContext formation.scope.binders
    (formation.signatures.symm ▸ cataloged member) ready argumentsBelow expectedBelow argumentsFormed expectedFormed continuation tried
  exact ⟨produced.1,formed.of_new_rows
    (congrArg LexicalScope.binders (localReadScope_selectFunctionCandidateFrom_lexicalScope accepted)) produced.2⟩

private theorem unify_fields {state result : State} {left right : Ty}
    (accepted : Detail.unify state left right = .ok result) :
    result.localBinders = state.localBinders ∧ result.requirements = state.requirements ∧ result.nodes = state.nodes := by
  unfold Detail.unify at accepted
  cases unified : state.inference.unify left right with
  | error error => simp [unified, liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    cases accepted
    exact ⟨rfl,rfl,rfl⟩

private theorem builtin_arguments_fields {arguments : List InferredExpression} {parameters : List Ty}
    {state result : State}
    (accepted : unifyBuiltinFunctionArgumentsEqual arguments parameters state = .ok result) :
    result.localBinders = state.localBinders ∧ result.requirements = state.requirements ∧ result.nodes = state.nodes := by
  induction arguments generalizing parameters state result with
  | nil => cases accepted; exact ⟨rfl,rfl,rfl⟩
  | cons argument arguments ih =>
    cases parameters with
    | nil => cases accepted; exact ⟨rfl,rfl,rfl⟩
    | cons parameter parameters =>
      cases unified : Detail.unify state argument.type parameter with
      | error error => simp [unifyBuiltinFunctionArgumentsEqual,unified,bind,Except.bind] at accepted
      | ok middle =>
        simp only [unifyBuiltinFunctionArgumentsEqual,unified,bind,Except.bind] at accepted
        have child := ih accepted
        have fields := unify_fields unified
        exact ⟨child.1.trans fields.1,child.2.1.trans fields.2.1,child.2.2.trans fields.2.2⟩

theorem recordBuiltinFunctionCall_normalized_fields
    {source callee : Syntax.Expr} {name : String} {function : BuiltinFunctionId}
    {arguments : List InferredExpression} {call : ExpressionId} {expected : Option Ty}
    {state : State} {result : InferredExpression × State}
    (accepted : recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    result.2.localBinders = state.localBinders ∧ result.2.requirements = state.requirements ∧
      result.2.nodes.flatMap Node.initializedLetBinders = state.nodes.flatMap Node.initializedLetBinders := by
  unfold recordBuiltinFunctionCall at accepted
  by_cases arity : arguments.length = function.parameterTypes.length
  · simp only [if_pos arity,bind,Except.bind,pure,Pure.pure,Except.pure] at accepted
    cases argumentRun : unifyBuiltinFunctionArgumentsEqual arguments function.parameterTypes state with
    | error error => simp [argumentRun] at accepted
    | ok middle =>
      simp only [argumentRun] at accepted
      have fields := builtin_arguments_fields argumentRun
      cases expected with
      | none =>
        cases accepted
        refine ⟨fields.1,fields.2.1,?_⟩
        simp only [recordExpression,State.recordNode,State.allocateExpressionId,List.flatMap_append,
          List.flatMap_cons,List.flatMap_nil,Node.initializedLetBinders,List.append_nil]
        exact congrArg (List.flatMap Node.initializedLetBinders) fields.2.2
      | some expected =>
        cases resultRun : Detail.unify middle function.returnType expected with
        | error error => simp [resultRun] at accepted
        | ok final =>
          simp only [resultRun] at accepted
          cases accepted
          have finalFields := unify_fields resultRun
          refine ⟨finalFields.1.trans fields.1,finalFields.2.1.trans fields.2.1,?_⟩
          simp only [recordExpression,State.recordNode,State.allocateExpressionId,List.flatMap_append,
            List.flatMap_cons,List.flatMap_nil,Node.initializedLetBinders,List.append_nil]
          exact congrArg (List.flatMap Node.initializedLetBinders) (finalFields.2.2.trans fields.2.2)
  · simp [arity,bind,Except.bind] at accepted

theorem recordBuiltinFunctionCall_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution} {context : SourceInference.Context}
    {source callee : Syntax.Expr} {name : String} {function : BuiltinFunctionId}
    {arguments : List InferredExpression} {call : ExpressionId} {expected : Option Ty}
    {state : State} {result : InferredExpression × State}
    (formation : InferenceFormationContext semantic context outer)
    (formed : NormalizedStateFormation semantic outer state)
    (accepted : recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    TypeAdmissible semantic (outer.apply result.1.type) ∧ NormalizedStateFormation semantic outer result.2 := by
  have fields := recordBuiltinFunctionCall_normalized_fields accepted
  refine ⟨?_,formed.congr fields.1 fields.2.1⟩
  rw [recordBuiltinFunctionCall_success_returnType_eq accepted]
  apply type_applySubstitution_residual formation.residual formation.range
  cases function <;> first | exact .integer formation.scope.binders | exact .word formation.scope.binders | exact .bool formation.scope.binders

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedConstructorDispatch
/-! Source constructor dispatch uses the actual catalog member and freshening
operation before the smaller constructor-application inference call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness SourceInferenceRequirementFormation

private theorem freshConstructor_requirements (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    (freshDataConstructorInstantiation dataType constructor state).2.requirements = state.requirements := by
  have fold (parameters : List TypeParameterId) (accumulator : List Ty × State) :
      (parameters.foldl (fun result _ =>
        (result.1 ++ [result.2.fresh.1],result.2.fresh.2)) accumulator).2.requirements =
        accumulator.2.requirements := by
    induction parameters generalizing accumulator with
    | nil => rfl
    | cons parameter rest ih => exact ih (accumulator.1 ++ [accumulator.2.fresh.1],accumulator.2.fresh.2)
  exact fold dataType.parameters ([],state)

theorem fresh_constructor_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution} {context : SourceInference.Context}
    {state : State} {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
    (formation : InferenceFormationContext semantic context outer)
    (formed : NormalizedStateFormation semantic outer state)
    (dataMember : dataType ∈ context.signatures.dataTypes) (constructorMember : constructor ∈ dataType.constructors) :
    let fresh := freshDataConstructorInstantiation dataType constructor state
    NormalizedStateFormation semantic outer fresh.2 ∧
      (∀ type ∈ fresh.1.payloadTypes, TypeAdmissible semantic (outer.apply type)) ∧
      TypeAdmissible semantic (outer.apply fresh.1.resultType) := by
  dsimp only
  have valid := freshDataConstructorInstantiation_admissible (state := state) formation.catalog formation.scope.binders
    formation.residual (formation.signatures.symm ▸ dataMember) constructorMember rfl
  refine ⟨formed.congr
    (congrArg LexicalScope.binders (freshDataConstructorInstantiation_preserves_lexicalScope dataType constructor state))
    (freshConstructor_requirements dataType constructor state),?_,?_⟩
  · intro type member
    exact type_applySubstitution_residual formation.residual formation.range
      (SourceSemantics.DataConstructorInstantiation.Admissible.payload_type_admissible formation.catalog formation.scope.binders valid member)
  · exact type_applySubstitution_residual formation.residual formation.range
      (SourceSemantics.DataConstructorInstantiation.Admissible.result_type_admissible formation.scope.binders valid)

theorem inferExprFuel_dotConstructor_formation
    {semantic : SourceSemantics.Context} {outer : Substitution} {fuel : Nat} {context : SourceInference.Context}
    {expression : Syntax.Expr} {dot : Syntax.SourceSpan} {name : Syntax.Identifier}
    {arguments : Option (Syntax.DelimitedList Syntax.Expr)} {expected : Option Ty} {initial : State}
    (form : expression.value = .dotConstructor dot name arguments)
    (constructorIH : ∀ dataType constructor typeArguments,
      InferConstructorApplicationFuelFormation semantic outer fuel context expression initial.allocateExpressionId.1
        (instantiateDataConstructor dataType constructor typeArguments)
        (arguments.map (·.elements) |>.getD []) expected initial.allocateExpressionId.2) :
    InferExprFuelFormation semantic outer (fuel+1) context expression expected initial := by
  intro ready nodes formed formation expectedBelow expectedFormed result success continuation capture
  let id := initial.allocateExpressionId.1
  let allocated := initial.allocateExpressionId.2
  have allocationEq : initial.allocateExpressionId = (id,allocated) := rfl
  have allocatedReady : allocated.InferenceReady := State.InferenceReady.allocateExpressionId ready
  have allocatedNodes := State.allocateExpressionId_preserves_nodesBelowNextOccurrence initial nodes
  have allocatedFormed : NormalizedStateFormation semantic outer allocated := formed.congr rfl rfl
  unfold inferExprFuel at success
  simp only [allocationEq,form,bind,Except.bind] at success
  cases selected : contextualConstructorCandidate context allocated expected name.value with
  | error error => simp [selected] at success
  | ok candidate =>
    rcases candidate with ⟨dataType,constructor,typeArguments⟩
    simp only [selected] at success
    have below := contextualConstructorCandidate_success_instantiation_variablesBelow allocatedReady expectedBelow formation.validated selected
    have progress := inferConstructorApplicationFuel_inferenceProperties allocatedReady formation.validated
      formation.functionShapes below.1 below.2 expectedBelow success
    have entryContinuation := continuation.trans progress.1.substitution_extends
    obtain ⟨dataMember,constructorMember,actual,expectedEq,nominalEq⟩ := contextualConstructorCandidate_success_facts selected
    have actualFormed := expectedFormed actual (by rw [expectedEq]; simp)
    have resultFormed : TypeAdmissible semantic
        (outer.apply (instantiateDataConstructor dataType constructor typeArguments).resultType) := by
      have resolved : TypeAdmissible semantic (outer.apply (allocated.resolve actual)) :=
        (entryContinuation actual).symm ▸ actualFormed
      simpa only [nominalEq,instantiateDataConstructor] using resolved
    have valid := SourceSemantics.DataConstructorInstantiation.Admissible.instantiateDataConstructor_applySubstitution
      formation.catalog (formation.signatures.symm ▸ dataMember) constructorMember outer resultFormed
    have payloadFormed : ∀ type ∈ (instantiateDataConstructor dataType constructor typeArguments).payloadTypes,
        TypeAdmissible semantic (outer.apply type) := by
      intro type member
      exact SourceSemantics.DataConstructorInstantiation.Admissible.payload_type_admissible
        formation.catalog formation.scope.binders valid (List.mem_map.mpr ⟨type,member,rfl⟩)
    exact constructorIH dataType constructor typeArguments allocatedReady allocatedNodes allocatedFormed formation
      below.1 payloadFormed below.2 resultFormed expectedBelow expectedFormed result success continuation capture

theorem inferExprFuel_fieldConstructor_formation
    {semantic : SourceSemantics.Context} {outer : Substitution} {fuel : Nat} {context : SourceInference.Context}
    {expression base : Syntax.Expr} {dot : Syntax.SourceSpan} {name : Syntax.Identifier}
    {expected : Option Ty} {initial : State}
    (form : expression.value = .field base dot name)
    (constructorIH : ∀ instantiation state,
      InferConstructorApplicationFuelFormation semantic outer fuel context expression initial.allocateExpressionId.1
        instantiation [] expected state) :
    InferExprFuelFormation semantic outer (fuel+1) context expression expected initial := by
  intro ready nodes formed formation expectedBelow expectedFormed result success continuation capture
  let id := initial.allocateExpressionId.1
  let allocated := initial.allocateExpressionId.2
  have allocationEq : initial.allocateExpressionId = (id,allocated) := rfl
  have allocatedReady : allocated.InferenceReady := State.InferenceReady.allocateExpressionId ready
  have allocatedNodes := State.allocateExpressionId_preserves_nodesBelowNextOccurrence initial nodes
  have allocatedFormed : NormalizedStateFormation semantic outer allocated := formed.congr rfl rfl
  unfold inferExprFuel at success
  simp only [allocationEq,form,bind,Except.bind] at success
  cases candidatesResult : constructorCalleeCandidates context allocated expression with
  | error error => simp [candidatesResult] at success
  | ok candidates =>
    simp only [candidatesResult] at success
    cases candidates with
    | nil =>
      simp only at success
      repeat' first | split at success
      all_goals contradiction
    | cons candidate rest =>
      cases rest with
      | cons second tail => simp at success
      | nil =>
        rcases candidate with ⟨dataType,constructor⟩
        let fresh := freshDataConstructorInstantiation dataType constructor allocated
        have members := constructorCalleeCandidates_success_members candidatesResult dataType constructor (by simp)
        have freshProperties := freshDataConstructorInstantiation_inferenceProperties dataType constructor allocated allocatedReady
          (formation.validated.data_constructor_payloadTypes_variablesBelow members.1 members.2 _)
        have freshFormed := fresh_constructor_normalized_formation formation allocatedFormed members.1 members.2
        have freshNodes := (freshDataConstructorInstantiation_occurrenceBoundExtends dataType constructor allocated).nodesBelowNextOccurrence allocatedNodes
        exact constructorIH fresh.1 fresh.2 freshProperties.2.1 freshNodes freshFormed.1 formation
          freshProperties.2.2.2.1 freshFormed.2.1 freshProperties.2.2.2.2 freshFormed.2.2
          (fun type member => (expectedBelow type member).weaken freshProperties.1.next_le)
          expectedFormed result success continuation capture

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedLambdaParameters
/-! Actual lambda parameter allocation forms each fresh or annotated type
under the selected final substitution and enters its real monomorphic binder. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation SourceInferenceSoundness

theorem resolved_annotation_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution} {context : SourceInference.Context}
    {source : Syntax.TypeExpr} {type : Ty}
    (formation : InferenceFormationContext semantic context outer)
    (accepted : Detail.resolveSourceType context source = .ok type) :
    TypeAdmissible semantic (outer.apply type) :=
  type_applySubstitution_residual formation.residual formation.range
    (.ofWellFormed (resolveSourceType_success_typeWellFormed formation.canonical
      formation.scope.signatures formation.scope.parameters formation.scope.owner accepted))

/-- Inferred and annotated parameters follow the actual recursive allocator. -/
theorem bindLambdaParameters_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {context : SourceInference.Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (formation : InferenceFormationContext semantic context outer)
    (formed : NormalizedStateFormation semantic outer state)
    (accepted : Detail.bindLambdaParameters context parameters index seen state = .ok result) :
    (∀ type ∈ result.2.1, TypeAdmissible semantic (outer.apply type)) ∧
      NormalizedStateFormation semantic outer result.2.2 := by
  induction parameters generalizing index seen state result with
  | nil =>
    simp only [Detail.bindLambdaParameters, Except.ok.injEq] at accepted
    subst result
    exact ⟨by simp, formed⟩
  | cons parameter rest ih =>
    cases parameterValue : parameter.value with
    | error =>
      simp [Detail.bindLambdaParameters, parameterValue, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    | inferred name =>
      by_cases duplicate : name.value ∈ seen
      · simp [Detail.bindLambdaParameters, parameterValue, duplicate, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
      · let type := state.fresh.1
        let freshState := state.fresh.2
        let binderState := (freshState.allocateBinder name.value (.mono type) (some parameter.span) false []).2
        cases tailRun : Detail.bindLambdaParameters context rest (index + 1) (name.value :: seen) binderState with
        | error error =>
          simp [Detail.bindLambdaParameters, parameterValue, duplicate, type, freshState,
            binderState, tailRun, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
        | ok tail =>
          rcases tail with ⟨binders, types, finalState⟩
          have same : ((freshState.allocateBinder name.value (.mono type) (some parameter.span) false []).1 :: binders,
              type :: types, finalState) = result := by
            simpa [Detail.bindLambdaParameters, parameterValue, duplicate, type, freshState,
              binderState, tailRun, bind, Except.bind, pure, Pure.pure, Except.pure] using accepted
          subst result
          have typeFormed : TypeAdmissible semantic (outer.apply type) :=
            type_applySubstitution_residual formation.residual formation.range
              (.variableOfResidual formation.scope.binders formation.residual _)
          have freshFormed : NormalizedStateFormation semantic outer freshState := formed.congr rfl rfl
          have entered : NormalizedStateFormation semantic outer binderState :=
            freshFormed.allocate _ _ _ _ [] (NormalizedBinderFormation.mono _ _ _ _ _ typeFormed)
          have child := ih entered tailRun
          refine ⟨?_,child.2⟩
          intro actual member
          rcases List.mem_cons.mp member with rfl | member
          · exact typeFormed
          · exact child.1 actual member
    | typed marker name sourceType =>
      cases resolved : Detail.resolveSourceType context sourceType with
      | error error =>
        simp [Detail.bindLambdaParameters, parameterValue, resolved, bind, Except.bind] at accepted
      | ok type =>
        by_cases duplicate : name.value ∈ seen
        · simp [Detail.bindLambdaParameters, parameterValue, resolved, duplicate, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
        · let binderState := (state.allocateBinder name.value (.mono type) (some parameter.span) marker.isSome []).2
          cases tailRun : Detail.bindLambdaParameters context rest (index + 1) (name.value :: seen) binderState with
          | error error =>
            simp [Detail.bindLambdaParameters, parameterValue, resolved, duplicate,
              binderState, tailRun, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
          | ok tail =>
            rcases tail with ⟨binders, types, finalState⟩
            have same : ((state.allocateBinder name.value (.mono type) (some parameter.span) marker.isSome []).1 :: binders,
                type :: types, finalState) = result := by
              simpa [Detail.bindLambdaParameters, parameterValue, resolved, duplicate,
                binderState, tailRun, bind, Except.bind, pure, Pure.pure, Except.pure] using accepted
            subst result
            have typeFormed := resolved_annotation_normalized_formation formation resolved
            have entered : NormalizedStateFormation semantic outer binderState :=
              formed.allocate _ _ _ _ [] (NormalizedBinderFormation.mono _ _ _ _ _ typeFormed)
            have child := ih entered tailRun
            refine ⟨?_,child.2⟩
            intro actual member
            rcases List.mem_cons.mp member with rfl | member
            · exact typeFormed
            · exact child.1 actual member

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end
