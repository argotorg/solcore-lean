import Solcore.SourceSemantics.SourceInferenceExecutableCoercionFitting

/-! Actual retained leaf expressions obtain their optional coercion profile
from the selected source body's executable interfaces. Ordinary bodies without
coercions do not need a Coerce declaration. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem
    inferExprFuel_success_numericLiteral_expressionTypingBase_selected
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      wholeContext.signatures finalized.solvedRequirements finalized.typedSource)
    {fuel : Nat} {expression : Syntax.Expr}
    {literal : Syntax.CoreLiteral} {source : Syntax.CoreLiteralValue}
    {rawValue : Nat} {expected : Option Ty}
    {initial allocated : State} {id : ExpressionId}
    {inferred : InferredExpression} {resultState : State}
    {semanticSource : TypedSource}
    {active : SourceSemantics.Context}
    (expressionEq : expression.value = .literal literal)
    (literalEq : literal.value = source)
    (decoded : Frontend.numericLiteralValue? source = some rawValue)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok (inferred, resultState))
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆
      evidenceState.requirements)
    (integerLiteralsSubset : resultState.integerLiterals ⊆
      evidenceState.integerLiterals)
    (retained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (canonical : SignatureParametersWellFormed
      wholeContext.scope.genericOwner wholeContext.typeParameters)
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial
      active)
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression inferred.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      active finalized.substitution inferred := by
  let rawType := allocated.fresh.1
  let freshState := allocated.fresh.2
  let addition := freshState.addRequirementWithId
    (ProgramSignatures.builtinIntPredicate rawType)
  let origin : IntegerLiteralOrigin := {
    metavariable := ⟨allocated.inference.next⟩
    expression := id
    requirement := addition.1
  }
  let literalState : State := {
    addition.2 with
    integerLiterals := addition.2.integerLiterals ++ [origin]
  }
  let resolution : IntegerLiteralResolution := {
    rawValue
    targetType := rawType
    requirement := addition.1
  }
  obtain ⟨recorded, originMember, requirementMember⟩ :=
    Detail.inferExprFuel_success_numericLiteral_record expressionEq literalEq
      decoded allocationEq success
  have originMemberFinal : origin ∈ evidenceState.integerLiterals :=
    integerLiteralsSubset originMember
  have requirementMemberFinal :
      ({ id := origin.requirement
         predicate := ProgramSignatures.builtinIntPredicate
           (.variable origin.metavariable) } : Requirement) ∈
        evidenceState.requirements := by
    apply requirementsSubset
    simpa [origin, addition, freshState, rawType,
      State.fresh, TypeSystem.InferState.fresh] using requirementMember
  obtain ⟨coercions, recordedContains⟩ :=
    recordExpressionWithExpected_success_containsExpression recorded roots
  have occurs : PrimaryRequirementOccursAt finalized.typedSource
      (.expression inferred.id) resolution.requirement := by
    apply retained recordedContains
    change resolution.requirement ∈
      [addition.1] ++ Detail.coercionRequirements coercions
    simp [resolution]
  have literalValid : IntegerLiteralValid active source
      (resolution.applySubstitution finalized.substitution) := by
    apply resources.integerLiteralValidAt
      (origin := origin) (decoded := by simpa [resolution] using decoded)
    · simp [resolution, origin, rawType, State.fresh,
        TypeSystem.InferState.fresh]
    · rfl
    · exact originMemberFinal
    · exact requirementMemberFinal
    · exact invariant.signaturesEq
    · exact invariant.solvedRequirementsEq
    · exact invariant.assumptionsMono
    · exact covered
    · exact occurs
  have formType : ExpressionFormHasRawType semanticSource active
      ((ExpressionForm.integerLiteral source resolution).applySubstitution
        finalized.substitution)
      (finalized.substitution.apply rawType) (.ordinary [addition.1]) := by
    simpa [ExpressionForm.applySubstitution, resolution,
      IntegerLiteralResolution.applySubstitution] using
        (ExpressionFormHasRawType.integerLiteral literalValid)
  have rawAdmissible : TypeAdmissible active
      (finalized.substitution.apply rawType) := by
    simpa [resolution, IntegerLiteralResolution.applySubstitution] using
      literalValid.target_type_admissible
        (invariant.typeParameterBinders canonical)
  have finalSubstitutionEq :
      resources.finalState.inference.substitution = finalized.substitution :=
    resources.substitution_eq.symm
  have finalSubstitutionExtends :
      resources.finalState.inference.substitution.SemanticallyExtends
        resultState.inference.substitution := by
    simpa only [finalSubstitutionEq] using resultSubstitutionExtension
  have requirementsSubsetFinal :
      resultState.requirements ⊆ resources.finalState.requirements := by
    intro requirement member
    rw [resources.requirements_eq]
    exact requirementsSubset member
  have activeSignaturesEq : active.signatures =
      inferenceContext.signatures :=
    invariant.signatures_eq_whole.trans signaturesEq.symm
  have activeCatalog : SignatureCatalogWellFormed active.signatures := by
    rw [activeSignaturesEq]
    exact catalog
  simpa only [finalSubstitutionEq] using
    (recordExpressionWithExpected_success_ordinaryExpressionTypingBase_from_interfaces
      (later := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      recorded finalSubstitutionExtends requirementsSubsetFinal retained
      (by simpa only [finalSubstitutionEq] using formType)
      (by simpa only [finalSubstitutionEq] using rawAdmissible)
      (by simpa only [signaturesEq] using interfaces) coercionsRetained
      activeCatalog activeSignaturesEq
      resources.solve_success resources.solved_context_eq resources.ledger
      resources.ownership invariant.signaturesEq
      invariant.solvedRequirementsEq invariant.assumptionsMono covered)

/-- The builtin-Boolean identifier is source-independent; only its optional
output coercion consults the whole finalized ledger. -/
theorem
    inferExprFuel_success_builtinBooleanIdentifier_expressionTypingBase_selected
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      wholeContext.signatures finalized.solvedRequirements finalized.typedSource)
    {fuel : Nat} {expression : Syntax.Expr} {expected : Option Ty}
    {initial allocated resultState : State}
    {id : ExpressionId} {name : Syntax.Identifier}
    {inferred : InferredExpression}
    {semanticSource : TypedSource} {active : SourceSemantics.Context}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = none)
    (isBoolean :
      (name.value == "true" || name.value == "false") = true)
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok (inferred, resultState))
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆
      evidenceState.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (canonical : SignatureParametersWellFormed
      wholeContext.scope.genericOwner wholeContext.typeParameters)
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial
      active)
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression inferred.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      active finalized.substitution inferred := by
  have recorded : Detail.recordExpressionWithExpected inferenceContext
      expression id .bool
      (.reference name.value (.builtinBoolean (name.value == "true"))) []
      expected allocated = .ok (inferred, resultState) :=
    Detail.inferExprFuel_success_builtinBooleanIdentifier_record expressionEq
      allocationEq lookupEq isBoolean success
  have formType : ExpressionFormHasRawType semanticSource active
      ((ExpressionForm.reference name.value
        (.builtinBoolean (name.value == "true"))).applySubstitution
          finalized.substitution)
      (finalized.substitution.apply .bool) (.ordinary []) := by
    simpa [ExpressionForm.applySubstitution,
      ReferenceResolution.applySubstitution] using
      (ExpressionFormHasRawType.reference (source := semanticSource)
        (ReferenceUseValid.builtinBoolean (context := active)
          (name.value == "true")))
  have rawAdmissible : TypeAdmissible active
      (finalized.substitution.apply .bool) := by
    simpa using TypeAdmissible.bool
      (invariant.typeParameterBinders canonical)
  have finalSubstitutionEq :
      resources.finalState.inference.substitution = finalized.substitution :=
    resources.substitution_eq.symm
  have requirementsSubsetFinal :
      resultState.requirements ⊆ resources.finalState.requirements := by
    intro requirement member
    rw [resources.requirements_eq]
    exact requirementsSubset member
  have activeSignaturesEq : active.signatures =
      inferenceContext.signatures :=
    invariant.signatures_eq_whole.trans signaturesEq.symm
  have activeCatalog : SignatureCatalogWellFormed active.signatures := by
    rw [activeSignaturesEq]
    exact catalog
  simpa only [finalSubstitutionEq] using
    (recordExpressionWithExpected_success_ordinaryExpressionTypingBase_from_interfaces
      (later := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      recorded
      (by simpa only [finalSubstitutionEq] using resultSubstitutionExtension)
      requirementsSubsetFinal retained
      (by simpa only [finalSubstitutionEq] using formType)
      (by simpa only [finalSubstitutionEq] using rawAdmissible)
      (by simpa only [signaturesEq] using interfaces) coercionsRetained
      activeCatalog activeSignaturesEq
      resources.solve_success resources.solved_context_eq resources.ledger
      resources.ownership invariant.signaturesEq
      invariant.solvedRequirementsEq invariant.assumptionsMono covered)

/-- A builtin-function identifier has a closed, catalog-independent raw
reference type in the active context. -/
theorem
    inferExprFuel_success_builtinFunctionIdentifier_expressionTypingBase_selected
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      wholeContext.signatures finalized.solvedRequirements finalized.typedSource)
    {fuel : Nat} {expression : Syntax.Expr} {expected : Option Ty}
    {initial allocated resultState : State}
    {id : ExpressionId} {name : Syntax.Identifier}
    {function : BuiltinFunctionId} {inferred : InferredExpression}
    {semanticSource : TypedSource} {active : SourceSemantics.Context}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = none)
    (notBoolean :
      (name.value == "true" || name.value == "false") = false)
    (functionsEq : Detail.functionsNamed inferenceContext name.value =
      .ok [])
    (builtinEq : Frontend.builtinFunctionNamed? name.value = some function)
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok (inferred, resultState))
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆
      evidenceState.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (canonical : SignatureParametersWellFormed
      wholeContext.scope.genericOwner wholeContext.typeParameters)
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial
      active)
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression inferred.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      active finalized.substitution inferred := by
  have recorded : Detail.recordExpressionWithExpected inferenceContext
      expression id function.type
      (.reference name.value (.builtinFunction function)) [] expected
      allocated = .ok (inferred, resultState) :=
    Detail.inferExprFuel_success_builtinFunctionIdentifier_record expressionEq
      allocationEq lookupEq notBoolean functionsEq builtinEq success
  have fixedType : finalized.substitution.apply function.type =
      function.type := by
    cases function <;>
      simp [BuiltinFunctionId.type, BuiltinFunctionId.parameterTypes,
        BuiltinFunctionId.returnType, Ty.productMany]
  have formType : ExpressionFormHasRawType semanticSource active
      ((ExpressionForm.reference name.value
        (.builtinFunction function)).applySubstitution
          finalized.substitution)
      (finalized.substitution.apply function.type) (.ordinary []) := by
    rw [fixedType]
    simpa [ExpressionForm.applySubstitution,
      ReferenceResolution.applySubstitution] using
      (ExpressionFormHasRawType.reference (source := semanticSource)
        (ReferenceUseValid.builtinFunction (context := active) function))
  have rawAdmissible : TypeAdmissible active
      (finalized.substitution.apply function.type) := by
    rw [fixedType]
    exact TypeAdmissible.builtinFunction
      (invariant.typeParameterBinders canonical) function
  have finalSubstitutionEq :
      resources.finalState.inference.substitution = finalized.substitution :=
    resources.substitution_eq.symm
  have requirementsSubsetFinal :
      resultState.requirements ⊆ resources.finalState.requirements := by
    intro requirement member
    rw [resources.requirements_eq]
    exact requirementsSubset member
  have activeSignaturesEq : active.signatures =
      inferenceContext.signatures :=
    invariant.signatures_eq_whole.trans signaturesEq.symm
  have activeCatalog : SignatureCatalogWellFormed active.signatures := by
    rw [activeSignaturesEq]
    exact catalog
  simpa only [finalSubstitutionEq] using
    (recordExpressionWithExpected_success_ordinaryExpressionTypingBase_from_interfaces
      (later := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      recorded
      (by simpa only [finalSubstitutionEq] using resultSubstitutionExtension)
      requirementsSubsetFinal retained
      (by simpa only [finalSubstitutionEq] using formType)
      (by simpa only [finalSubstitutionEq] using rawAdmissible)
      (by simpa only [signaturesEq] using interfaces) coercionsRetained
      activeCatalog activeSignaturesEq
      resources.solve_success resources.solved_context_eq resources.ledger
      resources.ownership invariant.signaturesEq
      invariant.solvedRequirementsEq invariant.assumptionsMono covered)

/-- Canonical local-scheme instantiation closes directly in the active
recursive context.  The allocation and no-capture certificates remain
explicit because they are supplied by the recursive ledger/provenance
invariants rather than by a fixed source-side substitution context. -/
theorem
    inferExprFuel_success_localIdentifier_expressionTypingBase_selected
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      wholeContext.signatures finalized.solvedRequirements finalized.typedSource)
    {fuel : Nat} {expression : Syntax.Expr} {expected : Option Ty}
    {initial allocated resultState : State}
    {id : ExpressionId} {name : Syntax.Identifier} {binder : TypedBinder}
    {inferred : InferredExpression}
    {semanticSource : TypedSource} {active : SourceSemantics.Context}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = some binder)
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok (inferred, resultState))
    (certificate :
      let instantiationStart := allocated.inference.next
      let instantiated :=
        binder.scheme.instantiateWithSubstitution instantiationStart
      let inference := { allocated.inference with next := instantiated.next }
      let advanced : State := { allocated with inference }
      let predicates := binder.schemeRequirements.map fun requirement =>
        Detail.applyPredicate advanced
          (TypedTraitResolution.applySubstitution instantiated.substitution
            requirement.predicate)
      State.LookupBinderRequirementAllocationCertificate advanced binder
        predicates)
    (noCapture : Detail.LocalBinderInstantiationNoCapture
      finalized.substitution binder)
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆
      evidenceState.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (canonical : SignatureParametersWellFormed
      wholeContext.scope.genericOwner wholeContext.typeParameters)
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial
      active)
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression inferred.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      active finalized.substitution inferred := by
  let instantiationStart := allocated.inference.next
  let instantiated :=
    binder.scheme.instantiateWithSubstitution instantiationStart
  let inference := { allocated.inference with next := instantiated.next }
  let advanced : State := { allocated with inference }
  let predicates := binder.schemeRequirements.map fun requirement =>
    Detail.applyPredicate advanced
      (TypedTraitResolution.applySubstitution instantiated.substitution
        requirement.predicate)
  let allocation := advanced.addRequirementsWithIds predicates
  change State.LookupBinderRequirementAllocationCertificate advanced binder
    predicates at certificate
  have recorded : Detail.recordExpressionWithExpected inferenceContext
      expression id (advanced.resolve instantiated.body)
      (.reference name.value (.local binder.id)) allocation.1 expected
      allocation.2
      (localSchemeInstantiationStart := some instantiationStart) =
        .ok (inferred, resultState) := by
    simpa only [instantiationStart, instantiated, inference, advanced,
      predicates, allocation] using
        (Detail.inferExprFuel_success_localIdentifier_record expressionEq
          allocationEq lookupEq success)
  have branchFacts := inferExprFuel_success_localIdentifier_facts
    expressionEq allocationEq lookupEq success certificate roots
  change ∃ coercions,
      ContainsExpression (resultState.toTypedSource roots) inferred.id {
        id := inferred.id
        span := expression.span
        type := inferred.type
        form := .reference name.value (.local binder.id)
        requirements := allocation.1 ++
          Detail.coercionRequirements coercions
        coercions
        localSchemeInstantiationStart := some instantiationStart
      } ∧
      allocation.1.Nodup ∧
      (∀ requirement, requirement ∈ allocation.1 →
        requirement ∉ localSchemeTemplateIds binder) ∧
      RequirementPredicatesCorrespond resultState.requirements
        ((instantiateLocalSchemePredicates instantiated.substitution
          binder).map (Detail.applyPredicate advanced)) allocation.1
    at branchFacts
  obtain ⟨coercions, recordedContains, actualUnique, actualDisjoint,
      resultCorresponds⟩ := branchFacts
  have evidenceCorresponds :
      RequirementPredicatesCorrespond evidenceState.requirements
        ((instantiateLocalSchemePredicates instantiated.substitution
          binder).map (Detail.applyPredicate advanced)) allocation.1 :=
    resultCorresponds.mono requirementsSubset
  have finalCorresponds :
      RequirementPredicatesCorrespond resources.finalState.requirements
        ((instantiateLocalSchemePredicates instantiated.substitution
          binder).map (Detail.applyPredicate advanced)) allocation.1 := by
    rw [resources.requirements_eq]
    exact evidenceCorresponds
  have occurs : ∀ requirement, requirement ∈ allocation.1 →
      PrimaryRequirementOccursAt finalized.typedSource
        (.expression inferred.id) requirement := by
    intro requirement member
    apply retained recordedContains
    change requirement ∈
      allocation.1 ++ Detail.coercionRequirements coercions
    exact List.mem_append_left _ member
  have allocationInferenceEq : allocated.inference = initial.inference := by
    have projection := congrArg
      (fun pair : ExpressionId × State => pair.2.inference) allocationEq
    change initial.inference = allocated.inference at projection
    exact projection.symm
  have finalExtendsAdvanced :
      finalized.substitution.SemanticallyExtends
        advanced.inference.substitution := by
    simpa [advanced, inference, allocationInferenceEq] using
      invariant.substitutionExtension
  have finalSubstitutionEq :
      resources.finalState.inference.substitution = finalized.substitution :=
    resources.substitution_eq.symm
  have requirements :=
    localReferenceRequirementSequenceProves_afterSemanticExtension
      (finalState := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      (active := active) (source := finalized.typedSource)
      (occurrence := .expression inferred.id)
      (by simpa only [finalSubstitutionEq] using finalExtendsAdvanced)
      finalCorresponds resources.solve_success resources.solved_context_eq
      resources.ledger resources.ownership invariant.signaturesEq
      invariant.solvedRequirementsEq invariant.assumptionsMono covered occurs
  have allocatedInvariant :=
    (invariant.allocateExpressionId allocationEq).active
  have environment := localReferenceEnvironmentFacts_of_lookupBinder?
    allocatedInvariant.aligned allocatedInvariant.formation lookupEq
  have appliedDisjoint : ∀ requirement,
      requirement ∈ allocation.1 →
        requirement ∉
          localSchemeTemplateIds
            (binder.applySubstitution finalized.substitution) := by
    simpa only
      [FlexibleSubstitution.localSchemeTemplateIds_applySubstitution] using
        actualDisjoint
  have binders := invariant.typeParameterBinders canonical
  have range := resources.substitutionRangeAdmissible binders
    invariant.signatures_eq_whole invariant.typeParametersEq
    invariant.declarationEq invariant.residual
  have instantiationValid :=
    canonicalLocalSchemeInstantiationValid_afterSubstitution binders
      invariant.residual range environment.2.2.2 environment.2.2.1
      noCapture instantiationStart actualUnique appliedDisjoint
      (by simpa only [finalSubstitutionEq] using requirements)
  have referenceValid : ReferenceUseValid active (.local binder.id)
      (finalized.substitution.apply instantiated.body) allocation.1 := by
    simpa only [FlexibleSubstitution.applyTypedBinder_id] using
      (ReferenceUseValid.local environment.1 environment.2.1
        instantiationValid)
  have rawEndpointEq :
      finalized.substitution.apply
          (advanced.resolve instantiated.body) =
        finalized.substitution.apply instantiated.body := by
    simpa [State.resolve, TypeSystem.InferState.resolve] using
      finalExtendsAdvanced instantiated.body
  have formType : ExpressionFormHasRawType semanticSource active
      ((ExpressionForm.reference name.value (.local binder.id)
        ).applySubstitution finalized.substitution)
      (finalized.substitution.apply
        (advanced.resolve instantiated.body))
      (.ordinary allocation.1) := by
    rw [rawEndpointEq]
    simpa [ExpressionForm.applySubstitution,
      ReferenceResolution.applySubstitution] using
        (ExpressionFormHasRawType.reference (source := semanticSource)
          referenceValid)
  have rawAdmissible : TypeAdmissible active
      (finalized.substitution.apply
        (advanced.resolve instantiated.body)) := by
    rw [rawEndpointEq]
    exact instantiationValid.type_admissible
  have requirementsSubsetFinal : resultState.requirements ⊆
      resources.finalState.requirements := by
    intro requirement member
    rw [resources.requirements_eq]
    exact requirementsSubset member
  have activeSignaturesEq : active.signatures =
      inferenceContext.signatures :=
    invariant.signatures_eq_whole.trans signaturesEq.symm
  have activeCatalog : SignatureCatalogWellFormed active.signatures := by
    rw [activeSignaturesEq]
    exact catalog
  simpa only [finalSubstitutionEq] using
    (recordExpressionWithExpected_success_ordinaryExpressionTypingBase_from_interfaces
      (later := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      recorded
      (by simpa only [finalSubstitutionEq] using resultSubstitutionExtension)
      requirementsSubsetFinal retained
      (by simpa only [finalSubstitutionEq] using formType)
      (by simpa only [finalSubstitutionEq] using rawAdmissible)
      (by simpa only [signaturesEq] using interfaces) coercionsRetained
      activeCatalog activeSignaturesEq
      resources.solve_success resources.solved_context_eq resources.ledger
      resources.ownership invariant.signaturesEq
      invariant.solvedRequirementsEq invariant.assumptionsMono covered)

/-- A resolved proxy annotation is rigidly formed and therefore fixed by the
whole inference substitution.  Its branch closes in the active recursive
context without a source-side context-closure certificate. -/
theorem inferExprFuel_success_proxy_expressionTypingBase_selected
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      wholeContext.signatures finalized.solvedRequirements finalized.typedSource)
    {fuel : Nat} {expression : Syntax.Expr} {marker : Syntax.SourceSpan}
    {sourceType : Syntax.TypeExpr} {expected : Option Ty}
    {initial allocated resultState : State} {id : ExpressionId}
    {inferred : InferredExpression}
    {semanticSource : TypedSource} {active : SourceSemantics.Context}
    (expressionEq : expression.value = .proxy marker sourceType)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok (inferred, resultState))
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆
      evidenceState.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (canonical : SignatureParametersWellFormed
      wholeContext.scope.genericOwner wholeContext.typeParameters)
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial
      active)
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression inferred.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      active finalized.substitution inferred := by
  obtain ⟨inner, resolution, recorded⟩ :=
    Detail.inferExprFuel_success_proxy_facts expressionEq allocationEq success
  have canonicalInference : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters := by
    simpa [ownerEq, parametersEq] using canonical
  have activeSignaturesEq : active.signatures =
      inferenceContext.signatures :=
    invariant.signatures_eq_whole.trans signaturesEq.symm
  have activeParametersEq : active.typeParameters =
      inferenceContext.typeParameters :=
    invariant.typeParametersEq.trans parametersEq.symm
  have activeOwnerEq : active.currentDeclaration =
      some inferenceContext.scope.genericOwner := by
    simpa [ownerEq] using invariant.declarationEq
  have innerWellFormed : TypeWellFormed active inner :=
    resolveSourceType_success_typeWellFormed canonicalInference
      activeSignaturesEq activeParametersEq activeOwnerEq resolution
  have fixedInner : finalized.substitution.apply inner = inner :=
    Detail.resolveSourceType_success_apply_eq_self finalized.substitution
      resolution
  have innerAdmissible : TypeAdmissible active
      (finalized.substitution.apply inner) := by
    rw [fixedInner]
    exact TypeAdmissible.ofWellFormed innerWellFormed
  have formType : ExpressionFormHasRawType semanticSource active
      ((ExpressionForm.proxy inner).applySubstitution
        finalized.substitution)
      (finalized.substitution.apply (.proxy inner)) (.ordinary []) := by
    simpa [ExpressionForm.applySubstitution, fixedInner] using
      ExpressionFormHasRawType.proxy innerAdmissible
  have rawAdmissible : TypeAdmissible active
      (finalized.substitution.apply (.proxy inner)) := by
    simpa [fixedInner] using TypeAdmissible.proxy innerAdmissible
  have finalSubstitutionEq :
      resources.finalState.inference.substitution = finalized.substitution :=
    resources.substitution_eq.symm
  have requirementsSubsetFinal : resultState.requirements ⊆
      resources.finalState.requirements := by
    intro requirement member
    rw [resources.requirements_eq]
    exact requirementsSubset member
  have activeCatalog : SignatureCatalogWellFormed active.signatures := by
    rw [activeSignaturesEq]
    exact catalog
  simpa only [finalSubstitutionEq] using
    (recordExpressionWithExpected_success_ordinaryExpressionTypingBase_from_interfaces
      (later := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      recorded
      (by simpa only [finalSubstitutionEq] using resultSubstitutionExtension)
      requirementsSubsetFinal retained
      (by simpa only [finalSubstitutionEq] using formType)
      (by simpa only [finalSubstitutionEq] using rawAdmissible)
      (by simpa only [signaturesEq] using interfaces) coercionsRetained
      activeCatalog activeSignaturesEq
      resources.solve_success resources.solved_context_eq resources.ledger
      resources.ownership invariant.signaturesEq
      invariant.solvedRequirementsEq invariant.assumptionsMono covered)

end Solcore.SourceSemantics.SourceInferenceSoundness
