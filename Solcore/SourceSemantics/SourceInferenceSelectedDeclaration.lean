import Solcore.SourceSemantics.SourceInferenceSelectedLeafSoundness

/-! Named references retain their complete canonical instantiation. Final
substitution range formation and the actual preparation interfaces supply
the remaining static obligations at the selected body boundary. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem declarationInstantiation_afterSubstitution
    {context : SourceSemantics.Context} {substitution : Substitution}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (binders : TypeParameterBindersWellFormed context)
    (residual : context.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible context substitution)
    {signature : ProgramFunctionSignature}
    (member : signature ∈ context.signatures.functions) (next : Nat) :
    SourceSemantics.DeclarationInstantiation.Admissible context
      ((Frontend.SourceInference.DeclarationInstantiation.ofInstantiated
        signature (signature.scheme.instantiate next)).applySubstitution substitution) := by
  let instantiated := signature.scheme.instantiate next
  have signatureWellFormed := catalog.functions_semantic signature member
  have innerExact := DeclarationInstantiation.instantiate_parameterSubstitution_exact
    signature.scheme next (catalog.function_parameters signature member).1
  let signatureTypingContext := signatureContext context.signatures
    signature.id signature.scheme.parameters signature.scheme.predicates
  have schemeScoped : TypeWellScoped signatureTypingContext [] signature.scheme.body := by
    rw [signatureWellFormed.scheme_body]
    exact .function
      (StructuralSubstitution.TypesWellScoped.productMany
        (StructuralSubstitution.TypesWellFormed.toTypesWellScoped signatureWellFormed.parameter_types))
      (StructuralSubstitution.TypesWellScoped.productMany
        (StructuralSubstitution.TypesWellFormed.toTypesWellScoped signatureWellFormed.return_types))
  refine .intro signature member rfl ?_ ?_ ?_ ?_ rfl rfl
  · exact FlexibleSubstitution.ParameterSubstitution.Exact.mapRange substitution innerExact
  · intro parameter replacement entry
    obtain ⟨⟨originalParameter, originalReplacement⟩, originalMember, same⟩ := List.mem_map.mp entry
    cases same
    obtain ⟨metavariable, rfl⟩ :=
      Frontend.ConstrainedDeclarationScheme.instantiate_parameterSubstitution_range_is_variable
        signature.scheme next originalParameter originalReplacement originalMember
    cases found : substitution.lookup? metavariable with
    | none =>
      simp only [Substitution.apply, found, Option.getD_none]
      exact TypeAdmissible.variableOfResidual binders residual metavariable
    | some type =>
      simp only [Substitution.apply, found, Option.getD_some]
      exact range metavariable type (Substitution.lookup?_eq_some_mem found)
  · change substitution.apply instantiated.body =
      (FlexibleSubstitution.ParameterSubstitution.mapRange substitution instantiated.parameterSubstitution).apply signature.scheme.body
    rw [ConstrainedDeclarationScheme.instantiate_body]
    exact FlexibleSubstitution.TypeWellScoped.applyFlexible_composeParameters
      substitution instantiated.parameterSubstitution innerExact schemeScoped
  · change instantiated.predicates.map (TypedTraitResolution.applySubstitution substitution) =
      signature.scheme.predicates.map (ProgramPredicate.applyParameters
        (FlexibleSubstitution.ParameterSubstitution.mapRange substitution instantiated.parameterSubstitution))
    rw [ConstrainedDeclarationScheme.instantiate_predicates]
    exact FlexibleSubstitution.PredicatesWellFormed.applyFlexible_composeParameters
      substitution instantiated.parameterSubstitution innerExact signatureWellFormed.predicates

theorem inferExprFuel_success_declarationIdentifier_expressionTypingBase_selected
    {fuel : Nat}
    {inferenceContext solverContext : Frontend.SourceInference.Context}
    {expression : Syntax.Expr} {expected : Option TypeSystem.Ty}
    {initial allocated later : Frontend.SourceInference.State}
    {id : ExpressionId} {name : Syntax.Identifier}
    {signature : ProgramFunctionSignature}
    {result : InferredExpression × Frontend.SourceInference.State}
    {roots : List NodeId}
    {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context}
    {semanticSource evidenceSource : TypedSource}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = none)
    (notBoolean :
      (name.value == "true" || name.value == "false") = false)
    (functionsEq : Detail.functionsNamed inferenceContext name.value =
      .ok [signature])
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok result)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        result.2.inference.substitution)
    (requirementsSubset : result.2.requirements ⊆ later.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (result.2.toTypedSource roots) evidenceSource result.1.id)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      inferenceContext.signatures solved evidenceSource)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt
      (result.2.toTypedSource roots) evidenceSource result.1.id)
    (catalog : SignatureCatalogWellFormed active.signatures)
    (binders : TypeParameterBindersWellFormed active)
    (residual : active.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible active later.inference.substitution)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (solveSuccess : Detail.solveRequirements solverContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base evidenceSource)
    (ownership : RequirementOwnership base evidenceSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (covered : TemplateScopeCovered evidenceSource active
      (.expression result.1.id)) :
    ExpressionTypingBase (result.2.toTypedSource roots) semanticSource active
      later.inference.substitution result.1 := by
  let instantiated :=
    signature.scheme.instantiate allocated.inference.next
  let inference := {
    allocated.inference with next := instantiated.next
  }
  let advanced : Frontend.SourceInference.State := {
    allocated with inference
  }
  let allocation :=
    advanced.addRequirementsWithIds instantiated.predicates
  have recorded : Detail.recordExpressionWithExpected inferenceContext
      expression id instantiated.body
      (.reference name.value (.declaration
        (Frontend.SourceInference.DeclarationInstantiation.ofInstantiated
          signature instantiated)))
      allocation.1 expected allocation.2 = .ok result := by
    simpa only [instantiated, inference, advanced, allocation] using
      (Detail.inferExprFuel_success_declarationIdentifier_record expressionEq
        allocationEq lookupEq notBoolean functionsEq success)
  have inferenceSignatureMember :
      signature ∈ inferenceContext.signatures.functions :=
    Detail.functionsNamed_success_subset_catalog functionsEq (by simp)
  have signatureMember : signature ∈ active.signatures.functions := by
    rw [signaturesEq]
    exact inferenceSignatureMember
  have mappedInstantiationValid := declarationInstantiation_afterSubstitution
    catalog binders residual range signatureMember allocated.inference.next
  have allocationAtLater : allocation.2.requirements ⊆ later.requirements :=
    List.Subset.trans
      (Detail.recordExpressionWithExpected_requirements_subset recorded)
      requirementsSubset
  have allocationCorresponds : RequirementPredicatesCorrespond
      allocation.2.requirements instantiated.predicates allocation.1 := by
    simpa only [allocation] using
      Frontend.SourceInference.State.addRequirementsWithIds_correspond
        advanced instantiated.predicates
  have laterCorresponds : RequirementPredicatesCorrespond later.requirements
      instantiated.predicates allocation.1 :=
    allocationCorresponds.mono allocationAtLater
  obtain ⟨coercions, recordedContains⟩ :=
    recordExpressionWithExpected_success_containsExpression recorded roots
  have occurs : ∀ requirement, requirement ∈ allocation.1 →
      PrimaryRequirementOccursAt evidenceSource (.expression result.1.id)
        requirement := by
    intro requirement member
    apply retained recordedContains
    change requirement ∈
      allocation.1 ++ Detail.coercionRequirements coercions
    exact List.mem_append_left _ member
  have sequence := solveRequirements_correspondingSequenceProvesAt
    laterCorresponds solveSuccess solvedEq ledger ownership
    activeSignaturesEq activeRequirementsEq assumptionsMono covered occurs
  have predicateMapEq :
      instantiated.predicates.map (Detail.applyPredicate later) =
        instantiated.predicates.map
          (TypedTraitResolution.applySubstitution
            later.inference.substitution) := by
    apply List.map_congr_left
    intro predicate _
    rfl
  have finalSequence : RequirementSequenceProves active allocation.1
      (instantiated.predicates.map
        (TypedTraitResolution.applySubstitution
          later.inference.substitution)) := by
    rw [predicateMapEq] at sequence
    exact sequence
  have referenceValid : ReferenceUseValid active
      ((ReferenceResolution.declaration
        (Frontend.SourceInference.DeclarationInstantiation.ofInstantiated
          signature instantiated)).applySubstitution
            later.inference.substitution)
      (later.inference.substitution.apply instantiated.body) allocation.1 :=
    .declaration mappedInstantiationValid finalSequence
  have formType : ExpressionFormHasRawType semanticSource active
      ((ExpressionForm.reference name.value (ReferenceResolution.declaration
        (Frontend.SourceInference.DeclarationInstantiation.ofInstantiated
          signature instantiated))).applySubstitution
            later.inference.substitution)
      (later.inference.substitution.apply instantiated.body)
      (.ordinary allocation.1) :=
    .reference referenceValid
  have rawAdmissible : TypeAdmissible active
      (later.inference.substitution.apply instantiated.body) :=
    mappedInstantiationValid.type_admissible catalog binders
  exact
    recordExpressionWithExpected_success_ordinaryExpressionTypingBase_from_interfaces
      recorded substitutionExtends requirementsSubset retained formType
      rawAdmissible interfaces coercionsRetained catalog
      signaturesEq solveSuccess solvedEq ledger ownership
      activeSignaturesEq activeRequirementsEq assumptionsMono covered



theorem inferExprFuel_success_declarationIdentifier_expressionTypingBase_actual
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      wholeContext.signatures finalized.solvedRequirements finalized.typedSource)
    {fuel : Nat} {expression : Syntax.Expr} {expected : Option Ty}
    {initial allocated resultState : State} {id : ExpressionId} {name : Syntax.Identifier}
    {signature : ProgramFunctionSignature} {inferred : InferredExpression}
    {semanticSource : TypedSource} {active : SourceSemantics.Context}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = none)
    (notBoolean : (name.value == "true" || name.value == "false") = false)
    (functionsEq : Detail.functionsNamed inferenceContext name.value = .ok [signature])
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression expected initial =
      .ok (inferred, resultState))
    (extension : finalized.substitution.SemanticallyExtends resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆ evidenceState.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (canonical : SignatureParametersWellFormed wholeContext.scope.genericOwner wholeContext.typeParameters)
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial active)
    (covered : TemplateScopeCovered finalized.typedSource active (.expression inferred.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource active
      finalized.substitution inferred := by
  have finalSubstitutionEq := resources.substitution_eq.symm
  have finalExtension : resources.finalState.inference.substitution.SemanticallyExtends
      resultState.inference.substitution := by simpa only [finalSubstitutionEq] using extension
  have finalRequirements : resultState.requirements ⊆ resources.finalState.requirements := by
    rw [resources.requirements_eq]
    exact requirementsSubset
  have activeSignaturesEq : active.signatures = inferenceContext.signatures :=
    invariant.signatures_eq_whole.trans signaturesEq.symm
  have activeCatalog : SignatureCatalogWellFormed active.signatures := by
    rw [activeSignaturesEq]
    exact catalog
  have binders := invariant.typeParameterBinders canonical
  have range := resources.substitutionRangeAdmissible binders
    invariant.signatures_eq_whole invariant.typeParametersEq invariant.declarationEq invariant.residual
  simpa only [finalSubstitutionEq] using
    (inferExprFuel_success_declarationIdentifier_expressionTypingBase_selected
      (base := finalizedRequirementContext wholeContext finalized)
      expressionEq allocationEq lookupEq notBoolean functionsEq success finalExtension
      finalRequirements retained (by simpa only [signaturesEq] using interfaces) coercionsRetained
      activeCatalog binders invariant.residual
      (by simpa only [finalSubstitutionEq] using range) activeSignaturesEq
      resources.solve_success resources.solved_context_eq resources.ledger resources.ownership
      invariant.signaturesEq invariant.solvedRequirementsEq invariant.assumptionsMono covered)

end Solcore.SourceSemantics.SourceInferenceSoundness
