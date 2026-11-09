import Solcore.SourceSemantics.Internal.Inference.CoercionFitting
import Solcore.SourceSemantics.Internal.Selected.State

/-!
# Leaves and operators

Retained leaves take their coercion profile from the selected body, and operators are read in the
final lexical context.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedLeafSoundness
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedDeclaration
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedIndirectFitting
/-! Indirect calls retain their bundled-argument coercion path in call
metadata. The actual selected interfaces validate both that path and the
output path while child typing remains in its own semantic source. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

private theorem functionParts?_success_eq
    {type parameter result : Ty}
    (success : Detail.functionParts? type = some (parameter, result)) :
    type = .function parameter result := by
  cases type <;> simp_all [Detail.functionParts?]

theorem
    applyFunctionType_recordIndirectCall_typing_from_interfaces
    {inferenceContext solverContext : Frontend.SourceInference.Context}
    {calleeState resultState later : Frontend.SourceInference.State}
    {arguments : List InferredExpression}
    {source : Syntax.Expr}
    {callee : InferredExpression}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {application : Detail.IndirectApplicationResult}
    {result : InferredExpression}
    {roots : List NodeId}
    {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context}
    {semanticSource ledgerSource : TypedSource}
    (applicationSuccess : Detail.applyFunctionType inferenceContext call
      callee.type arguments expected calleeState = .ok application)
    (recordEq : Detail.recordIndirectCall source callee arguments application =
      (result, resultState))
    (applicationReady : calleeState.InferenceReady)
    (calleeBelow : callee.type.VariablesBelow
      calleeState.inference.next)
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.type.VariablesBelow calleeState.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow calleeState.inference.next)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆ later.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) ledgerSource result.id)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt
      (resultState.toTypedSource roots) ledgerSource result.id)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      inferenceContext.signatures solved ledgerSource)
    (argumentsType : ExpressionsHaveTypes semanticSource active
      (arguments.map (·.id))
      (arguments.map fun argument =>
        later.inference.substitution.apply argument.type))
    (calleeType : ExpressionHasType semanticSource active callee.id
      (later.inference.substitution.apply callee.type))
    (catalog : SignatureCatalogWellFormed active.signatures)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (solveSuccess : Detail.solveRequirements solverContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base ledgerSource)
    (ownership : RequirementOwnership base ledgerSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (callCovered : TemplateScopeCovered ledgerSource active
      (.expression result.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource active
      later.inference.substitution result := by
  have resultEq := congrArg Prod.fst recordEq
  have resultStateEq := congrArg Prod.snd recordEq
  simp only at resultEq resultStateEq
  subst result
  subst resultState
  have applicationProperties := Detail.applyFunctionType_inferenceProperties
    applicationReady calleeBelow argumentsBelow expectedBelow
      applicationSuccess
  have recordProperties := Detail.recordIndirectCall_inferenceProperties
    source callee arguments application applicationProperties.2.1
      applicationProperties.2.2
  have outerApplication : later.inference.substitution.SemanticallyExtends
      application.state.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans substitutionExtends
      recordProperties.1.substitution_extends
  have outerCalleeState : later.inference.substitution.SemanticallyExtends
      calleeState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans outerApplication
      applicationProperties.1.substitution_extends
  have applicationRequirementsSubset :
      application.state.requirements ⊆ later.requirements :=
    List.Subset.trans
      (Detail.recordIndirectCall_requirements_subset source callee arguments
        application)
      requirementsSubset
  let argumentType := TypeSystem.Ty.productMany (arguments.map (·.type))
  let coercedArgumentType := application.argumentCoercions.foldl
    (fun _ step => step.target) argumentType
  let metadata : IndirectCallResolution := {
    argumentCount := arguments.length
    argumentTypeBeforeCoercion := argumentType
    argumentTypeAfterCoercion := coercedArgumentType
    argumentCoercions := application.argumentCoercions
  }
  let callNode : ExpressionNode := {
    id := application.result.id
    span := source.span
    type := application.result.type
    form := .call callee.id (arguments.map (·.id)) (.indirect metadata)
    requirements :=
      Detail.coercionRequirements application.argumentCoercions ++
        Detail.coercionRequirements application.callCoercions
    coercions := application.callCoercions
  }
  have rawContains : ContainsExpression
      ((Detail.recordIndirectCall source callee arguments application).2
        |>.toTypedSource roots)
      application.result.id callNode := by
    simpa only [Detail.recordIndirectCall, argumentType,
      coercedArgumentType, metadata, callNode] using
        (recordExpression_containsExpression source application.result
          (.call callee.id (arguments.map (·.id)) (.indirect metadata))
          (Detail.coercionRequirements application.argumentCoercions ++
            Detail.coercionRequirements application.callCoercions)
          application.callCoercions application.state roots)
  have covered : TemplateScopeCovered ledgerSource active
      (.expression application.result.id) := by
    simpa only [Detail.recordIndirectCall_fst] using callCovered
  have argumentOccurs : ∀ requirement,
      requirement ∈ coercionRequirementIds application.argumentCoercions →
        PrimaryRequirementOccursAt ledgerSource
          (.expression application.result.id) requirement := by
    intro requirement member
    apply retained rawContains
    change requirement ∈
      Detail.coercionRequirements application.argumentCoercions ++
        Detail.coercionRequirements application.callCoercions
    apply List.mem_append_left
    simpa [Detail.coercionRequirements, coercionRequirementIds] using member
  have outputOccurs : ∀ requirement,
      requirement ∈ coercionRequirementIds application.callCoercions →
        PrimaryRequirementOccursAt ledgerSource
          (.expression application.result.id) requirement := by
    intro requirement member
    apply retained rawContains
    change requirement ∈
      Detail.coercionRequirements application.argumentCoercions ++
        Detail.coercionRequirements application.callCoercions
    apply List.mem_append_right
    simpa [Detail.coercionRequirements, coercionRequirementIds] using member
  have argumentPresent : CoercionPrimariesPresent ledgerSource application.argumentCoercions := by
    intro step member
    exact coercionsRetained.present rawContains step (List.mem_append_right _ member)
  have outputPresent : CoercionPrimariesPresent ledgerSource application.callCoercions := by
    intro step member
    exact coercionsRetained.present rawContains step (List.mem_append_left _ member)
  have argumentTypesBelow : ∀ type ∈ arguments.map (·.type),
      type.VariablesBelow calleeState.inference.next := by
    intro type member
    rcases List.mem_map.mp member with ⟨argument, argumentMember, rfl⟩
    exact argumentsBelow argument argumentMember
  have argumentTypeBelow : argumentType.VariablesBelow
      calleeState.inference.next :=
    TypeSystem.Ty.variablesBelow_productMany argumentTypesBelow
  rcases Detail.applyFunctionType_success_facts applicationSuccess with
      known | fresh
  · rcases known with ⟨parameterType, resultType, fittedArgument,
      fittedResult, partsResult, argumentSuccess, outputSuccess,
      applicationEq⟩
    subst application
    have resolvedCalleeBelow :
        (calleeState.resolve callee.type).VariablesBelow
          calleeState.inference.next :=
      applicationReady.solved.variablesBelow_apply calleeBelow
    have partsBelow := Detail.functionParts?_success_variablesBelow
      resolvedCalleeBelow partsResult
    have argumentProperties := Detail.withExpected_inferenceProperties
      applicationReady argumentTypeBelow (by
        intro expectedType expectedMember
        simp at expectedMember
        subst expectedType
        exact partsBelow.1) argumentSuccess
    have resultTypeBelow : resultType.VariablesBelow
        fittedArgument.state.inference.next :=
      partsBelow.2.weaken argumentProperties.1.next_le
    have expectedAtArgument : ∀ expectedType ∈ expected,
        expectedType.VariablesBelow fittedArgument.state.inference.next := by
      intro expectedType expectedMember
      exact (expectedBelow expectedType expectedMember).weaken
        argumentProperties.1.next_le
    have outputProperties := Detail.withExpected_inferenceProperties
      argumentProperties.2.1 resultTypeBelow expectedAtArgument outputSuccess
    have outerFittedArgument :
        later.inference.substitution.SemanticallyExtends
          fittedArgument.state.inference.substitution :=
      TypeSystem.Substitution.SemanticallyExtends.trans outerApplication
        outputProperties.1.substitution_extends
    have argumentRequirementsSubset :
        fittedArgument.state.requirements ⊆ later.requirements :=
      List.Subset.trans (Detail.withExpected_requirements_subset outputSuccess)
        applicationRequirementsSubset
    have rawArgumentPath :=
      withExpected_success_coercionPathValid_from_interfaces
        argumentSuccess interfaces argumentPresent
        argumentRequirementsSubset catalog signaturesEq
        solveSuccess solvedEq ledger ownership activeSignaturesEq
        activeRequirementsEq assumptionsMono covered argumentOccurs
    have argumentSourceEq : later.inference.substitution.apply
        (fittedArgument.state.resolve argumentType) =
        later.inference.substitution.apply argumentType :=
      TypeSystem.InferState.apply_resolve_eq_apply outerFittedArgument _
    have argumentTargetEq : later.inference.substitution.apply
        fittedArgument.expression.type =
        later.inference.substitution.apply parameterType :=
      Detail.withExpected_some_apply_eq argumentSuccess outerFittedArgument
    have argumentPath : CoercionPathValid active
        (later.inference.substitution.apply argumentType)
        (later.inference.substitution.apply parameterType)
        (fittedArgument.coercions.map
          (CoercionStep.applySubstitution later.inference.substitution)) := by
      rw [← argumentSourceEq, ← argumentTargetEq]
      exact rawArgumentPath
    have rawOutputPath :=
      withExpected_success_coercionPathValid_from_interfaces
        outputSuccess interfaces outputPresent
        applicationRequirementsSubset catalog signaturesEq solveSuccess solvedEq ledger ownership activeSignaturesEq
        activeRequirementsEq assumptionsMono covered outputOccurs
    have outputSourceEq : later.inference.substitution.apply
        (fittedResult.state.resolve resultType) =
        later.inference.substitution.apply resultType :=
      TypeSystem.InferState.apply_resolve_eq_apply outerApplication _
    have outputPath : CoercionPathValid active
        (later.inference.substitution.apply resultType)
        (later.inference.substitution.apply fittedResult.expression.type)
        (fittedResult.coercions.map
          (CoercionStep.applySubstitution later.inference.substitution)) := by
      rw [← outputSourceEq]
      exact rawOutputPath
    have calleeShape : calleeState.resolve callee.type =
        .function parameterType resultType :=
      functionParts?_success_eq partsResult
    have calleeFunctionEq : later.inference.substitution.apply callee.type =
        .function (later.inference.substitution.apply parameterType)
          (later.inference.substitution.apply resultType) := by
      calc
        later.inference.substitution.apply callee.type =
            later.inference.substitution.apply
              (calleeState.resolve callee.type) :=
          (TypeSystem.InferState.apply_resolve_eq_apply outerCalleeState _).symm
        _ = later.inference.substitution.apply
              (.function parameterType resultType) :=
          congrArg later.inference.substitution.apply calleeShape
        _ = .function (later.inference.substitution.apply parameterType)
              (later.inference.substitution.apply resultType) := rfl
    have calleeFunctionType : ExpressionHasType semanticSource active callee.id
        (.function (later.inference.substitution.apply parameterType)
          (later.inference.substitution.apply resultType)) := by
      rw [← calleeFunctionEq]
      exact calleeType
    simpa only [argumentType] using
      (ExpressionTypingBase.ofRecordIndirectCall
        (source := source) (callee := callee) (arguments := arguments)
        (application := {
          result := fittedResult.expression
          argumentCoercions := fittedArgument.coercions
          callCoercions := fittedResult.coercions
          state := fittedResult.state
        }) (roots := roots) calleeFunctionType argumentsType argumentPath
          outputPath)
  · rcases fresh with ⟨resultType, freshState, unifiedState, fittedResult,
      _, freshEq, unifySuccess, outputSuccess, applicationEq⟩
    subst application
    have freshProgress : calleeState.InferenceProgress freshState := by
      have progress := Frontend.SourceInference.State.InferenceProgress.fresh
        calleeState applicationReady.solved
      rw [freshEq] at progress
      exact progress
    have freshReady : freshState.InferenceReady := by
      have ready := Frontend.SourceInference.State.InferenceReady.fresh
        applicationReady
      rw [freshEq] at ready
      exact ready
    have freshTypeBelow : resultType.VariablesBelow
        freshState.inference.next := by
      have below : calleeState.fresh.1.VariablesBelow
          calleeState.fresh.2.inference.next := by
        change TypeSystem.Ty.VariablesBelow
          (calleeState.inference.next + 1)
          (.variable ⟨calleeState.inference.next⟩)
        exact (TypeSystem.Ty.variablesBelow_variable_iff _ _).2
          (Nat.lt_succ_self _)
      rw [freshEq] at below
      exact below
    have calleeAtFresh : callee.type.VariablesBelow
        freshState.inference.next :=
      calleeBelow.weaken freshProgress.next_le
    have argumentTypeAtFresh : argumentType.VariablesBelow
        freshState.inference.next :=
      argumentTypeBelow.weaken freshProgress.next_le
    have functionTypeBelow :
        (TypeSystem.Ty.function argumentType resultType).VariablesBelow
          freshState.inference.next :=
      (TypeSystem.Ty.variablesBelow_function_iff _ _ _).2
        ⟨argumentTypeAtFresh, freshTypeBelow⟩
    have unifyProgress := Detail.unify_inferenceProgress freshReady.solved
      calleeAtFresh functionTypeBelow unifySuccess
    have unifiedReady := Detail.unify_preserves_inferenceReady freshReady
      calleeAtFresh functionTypeBelow unifySuccess
    have resultTypeAtUnified : resultType.VariablesBelow
        unifiedState.inference.next :=
      freshTypeBelow.weaken unifyProgress.next_le
    have expectedAtUnified : ∀ expectedType ∈ expected,
        expectedType.VariablesBelow unifiedState.inference.next := by
      intro expectedType expectedMember
      exact (expectedBelow expectedType expectedMember).weaken
        (freshProgress.trans unifyProgress).next_le
    have outputProperties := Detail.withExpected_inferenceProperties
      unifiedReady resultTypeAtUnified expectedAtUnified outputSuccess
    have outerUnified : later.inference.substitution.SemanticallyExtends
        unifiedState.inference.substitution :=
      TypeSystem.Substitution.SemanticallyExtends.trans outerApplication
        outputProperties.1.substitution_extends
    have rawOutputPath :=
      withExpected_success_coercionPathValid_from_interfaces
        outputSuccess interfaces outputPresent
        applicationRequirementsSubset catalog signaturesEq solveSuccess solvedEq ledger ownership activeSignaturesEq
        activeRequirementsEq assumptionsMono covered outputOccurs
    have outputSourceEq : later.inference.substitution.apply
        (fittedResult.state.resolve resultType) =
        later.inference.substitution.apply resultType :=
      TypeSystem.InferState.apply_resolve_eq_apply outerApplication _
    have outputPath : CoercionPathValid active
        (later.inference.substitution.apply resultType)
        (later.inference.substitution.apply fittedResult.expression.type)
        (fittedResult.coercions.map
          (CoercionStep.applySubstitution later.inference.substitution)) := by
      rw [← outputSourceEq]
      exact rawOutputPath
    have unifiedEq := Detail.unify_resolve_eq unifySuccess
    have calleeFunctionEq : later.inference.substitution.apply callee.type =
        .function (later.inference.substitution.apply argumentType)
          (later.inference.substitution.apply resultType) := by
      calc
        later.inference.substitution.apply callee.type =
            later.inference.substitution.apply
              (unifiedState.resolve callee.type) :=
          (TypeSystem.InferState.apply_resolve_eq_apply outerUnified _).symm
        _ = later.inference.substitution.apply
              (unifiedState.resolve
                (.function argumentType resultType)) :=
          congrArg later.inference.substitution.apply unifiedEq
        _ = later.inference.substitution.apply
              (.function argumentType resultType) :=
          TypeSystem.InferState.apply_resolve_eq_apply outerUnified _
        _ = .function (later.inference.substitution.apply argumentType)
              (later.inference.substitution.apply resultType) := rfl
    have calleeFunctionType : ExpressionHasType semanticSource active callee.id
        (.function (later.inference.substitution.apply argumentType)
          (later.inference.substitution.apply resultType)) := by
      rw [← calleeFunctionEq]
      exact calleeType
    have argumentPath : CoercionPathValid active
        (later.inference.substitution.apply argumentType)
        (later.inference.substitution.apply argumentType) [] := .nil _
    simpa only [argumentType] using
      (ExpressionTypingBase.ofRecordIndirectCall
        (source := source) (callee := callee) (arguments := arguments)
        (application := {
          result := fittedResult.expression
          argumentCoercions := []
          callCoercions := fittedResult.coercions
          state := fittedResult.state
        }) (roots := roots) calleeFunctionType argumentsType argumentPath
          outputPath)

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedOrdinaryRecorder
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem recordExpressionWithExpected_success_expressionTypingBase_actual
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      wholeContext.signatures finalized.solvedRequirements finalized.typedSource)
    {expression : Syntax.Expr} {expected : Option Ty}
    {initial recordedState resultState : State} {id : ExpressionId}
    {rawType : Ty} {form : ExpressionForm} {owned : List RequirementId}
    {instantiationStart : Option Nat} {inferred : InferredExpression}
    {semanticSource : TypedSource} {active : SourceSemantics.Context}
    (recorded : Detail.recordExpressionWithExpected inferenceContext expression id
      rawType form owned expected recordedState instantiationStart = .ok (inferred, resultState))
    (extension : finalized.substitution.SemanticallyExtends resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆ evidenceState.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial active)
    (formType : ExpressionFormHasRawType semanticSource active
      (form.applySubstitution finalized.substitution) (finalized.substitution.apply rawType)
      (.ordinary owned))
    (rawAdmissible : TypeAdmissible active (finalized.substitution.apply rawType))
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
  simpa only [finalSubstitutionEq] using
    (recordExpressionWithExpected_success_ordinaryExpressionTypingBase_from_interfaces
      (base := finalizedRequirementContext wholeContext finalized)
      recorded finalExtension finalRequirements retained
      (by simpa only [finalSubstitutionEq] using formType)
      (by simpa only [finalSubstitutionEq] using rawAdmissible)
      (by simpa only [signaturesEq] using interfaces) coercionsRetained
      activeCatalog activeSignaturesEq resources.solve_success resources.solved_context_eq
      resources.ledger resources.ownership invariant.signaturesEq invariant.solvedRequirementsEq
      invariant.assumptionsMono covered)

theorem recordExpressionWithExpected_success_nodesPrefix
    {inferenceContext : Frontend.SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId}
    {type : TypeSystem.Ty} {form : ExpressionForm}
    {requirements : List RequirementId}
    {expected : Option TypeSystem.Ty}
    {initial : Frontend.SourceInference.State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × Frontend.SourceInference.State}
    (success : Detail.recordExpressionWithExpected inferenceContext source id
      type form requirements expected initial localSchemeInstantiationStart =
        .ok result) :
    initial.nodes <+: result.2.nodes := by
  obtain ⟨fitted, fittedSuccess, _, resultStateEq⟩ :=
    Detail.recordExpressionWithExpected_success_record success
  have fittedPrefix : initial.nodes <+: fitted.state.nodes := by
    rw [(Detail.withExpected_occurrenceState_eq fittedSuccess).1]
    exact List.prefix_rfl
  rw [resultStateEq]
  exact fittedPrefix.trans
    (Frontend.SourceInference.State.recordNode_nodesPrefix fitted.state _)


end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedOperatorTyping
/-! Operator inference is interpreted in the actual final lexical context.
Profile substitution uses the unchanged signature catalog; no substitution
certificate for an unrelated whole lexical context is required. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open FlexibleSubstitution

theorem operatorProfile_applySubstitution_signatures
    {substitution : Substitution}
    {source target : Context} {traitName methodName : String}
    {operand : Ty} {parameterTypes returnTypes : List Ty}
    {predicates : List ProgramPredicate}
    (catalog : SignatureCatalogWellFormed source.signatures)
    (signatures : target.signatures = source.signatures)
    (profile : OperatorProfileInstantiates source traitName methodName operand
      parameterTypes returnTypes predicates) :
    OperatorProfileInstantiates target traitName methodName
      (substitution.apply operand) (parameterTypes.map substitution.apply)
      (returnTypes.map substitution.apply)
      (predicates.map
        (TypedTraitResolution.applySubstitution substitution)) := by
  cases profile with
  | @intro signature method parameter signatureMem traitNameEq parametersEq
      methodUnique parameterTypesEq returnTypesEq =>
      have signatureWellFormed := catalog.traits_semantic signature signatureMem
      have methodFiltered : method ∈
          signature.methods.filter
            (fun candidate => candidate.name == methodName) := by
        rw [methodUnique]
        simp
      have methodMem : method ∈ signature.methods :=
        (List.mem_filter.mp methodFiltered).1
      have methodWellFormed := signatureWellFormed.methods method methodMem
      have innerExact : SourceSemantics.ParameterSubstitution.Exact
          [(parameter, operand)] signature.parameters := by
        constructor
        · exact signatureWellFormed.parameters_nodup
        · rw [parametersEq]
          simp [SourceSemantics.ParameterSubstitution.domain]
      have parameterCompose :=
        TypesWellScoped.applyFlexible_composeParameters
          (context := signatureContext source.signatures signature.id
            signature.parameters
            (signature.wherePredicates ++ method.wherePredicates))
          substitution [(parameter, operand)] innerExact
          (StructuralSubstitution.TypesWellFormed.toTypesWellScoped
            methodWellFormed.parameter_types)
      have returnCompose :=
        TypesWellScoped.applyFlexible_composeParameters
          (context := signatureContext source.signatures signature.id
            signature.parameters
            (signature.wherePredicates ++ method.wherePredicates))
          substitution [(parameter, operand)] innerExact
          (StructuralSubstitution.TypesWellFormed.toTypesWellScoped
            methodWellFormed.return_types)
      have predicateCompose :=
        PredicatesWellFormed.applyFlexible_composeParameters
          (context := signatureContext source.signatures signature.id
            signature.parameters
            (signature.wherePredicates ++ method.wherePredicates))
          substitution [(parameter, operand)] innerExact
          methodWellFormed.predicates
      change OperatorProfileInstantiates target traitName methodName
        (substitution.apply operand) (parameterTypes.map substitution.apply)
        (returnTypes.map substitution.apply)
        ({ trait := .declaration signature.id
           subject := substitution.apply operand
           arguments := [] } ::
          (method.wherePredicates.map
            (ProgramPredicate.applyParameters [(parameter, operand)])).map
              (TypedTraitResolution.applySubstitution substitution))
      rw [predicateCompose]
      exact .intro
        (by
          rw [signatures]
          exact signatureMem)
        traitNameEq parametersEq methodUnique
        (by
          change method.parameterTypes.map
              (ParameterSubstitution.mapRange substitution
                [(parameter, operand)]).apply =
            parameterTypes.map substitution.apply
          rw [← parameterCompose, parameterTypesEq])
        (by
          change method.returnTypes.map
              (ParameterSubstitution.mapRange substitution
                [(parameter, operand)]).apply =
            returnTypes.map substitution.apply
          rw [← returnCompose, returnTypesEq])

private theorem emptyLedger_sequence_false {context : SourceSemantics.Context}
    (empty : context.solvedRequirements = []) {ids : List RequirementId}
    {head : ProgramPredicate} {tail : List ProgramPredicate}
    (sequence : RequirementSequenceProves context ids (head :: tail)) : False := by
  cases sequence with
  | cons evidence rest =>
    obtain ⟨row, ⟨member, _⟩, _⟩ := evidence
    rw [empty] at member
    cases member

private theorem unary_primitive_substitution {context target : SourceSemantics.Context}
    (empty : context.solvedRequirements = []) {substitution : Substitution}
    {operator : Syntax.UnaryOp} {operand result : Ty} {requirements : List RequirementId}
    (typed : UnaryOperatorHasType context operator operand result requirements) :
    UnaryOperatorHasType target operator (substitution.apply operand)
      (substitution.apply result) requirements := by
  cases typed with
  | logicalNot => exact .logicalNot
  | wordBitNot => exact .wordBitNot
  | integerBitNot => exact .integerBitNot
  | trait dispatch profile evidence =>
    cases profile
    exact False.elim (emptyLedger_sequence_false empty evidence)

private theorem binary_primitive_substitution {context target : SourceSemantics.Context}
    (empty : context.solvedRequirements = []) {substitution : Substitution}
    {operator : Syntax.BinaryOp} {left right result : Ty} {requirements : List RequirementId}
    (typed : BinaryOperatorHasType context operator left right result requirements) :
    BinaryOperatorHasType target operator (substitution.apply left)
      (substitution.apply right) (substitution.apply result) requirements := by
  cases typed with
  | wordArithmetic kind => exact .wordArithmetic kind
  | wordShift kind => exact .wordShift kind
  | wordUnchecked kind => exact .wordUnchecked kind
  | integerArithmetic kind => exact .integerArithmetic kind
  | wordComparison kind => exact .wordComparison kind
  | integerComparison kind => exact .integerComparison kind
  | fixedComparison kind => exact .fixedComparison kind
  | fixedBitwise kind => exact .fixedBitwise kind
  | booleanAnd => exact .booleanAnd
  | booleanOr => exact .booleanOr
  | trait dispatch profile evidence =>
    cases profile
    exact False.elim (emptyLedger_sequence_false empty evidence)

theorem unaryOperatorInferenceCase_hasType_in_active
    {inferenceContext solverContext : Frontend.SourceInference.Context}
    {base active : SourceSemantics.Context}
    {initial later : Frontend.SourceInference.State}
    {solved : List SolvedRequirement}
    {ledgerSource : TypedSource} {occurrence : NodeId}
    {operator : Syntax.UnaryOp} {operandType : TypeSystem.Ty}
    {integerLiterals : List IntegerLiteralOrigin}
    {result : Detail.OperatorInferenceResult}
    (inferenceCase : UnaryOperatorInferenceCase inferenceContext (Context.ofSignatures inferenceContext.signatures)
      initial operator operandType integerLiterals result)
    (progress : initial.InferenceProgress result.state)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        result.state.inference.substitution)
    (requirementsSubset : result.state.requirements ⊆ later.requirements)
    (integerLiteralTargetsSupported : ∀ origin,
      origin ∈ integerLiterals →
        later.inference.substitution.apply
            (.variable origin.metavariable) = .word ∨
          later.inference.substitution.apply
            (.variable origin.metavariable) = .integer)
    (catalog : SignatureCatalogWellFormed active.signatures)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (operatorNames : OperatorNamesAt inferenceContext.signatures solved result.requirements
      (fun name => ∃ method, UnaryTraitDispatch operator name method))
    (solveSuccess : Detail.solveRequirements solverContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base ledgerSource)
    (ownership : RequirementOwnership base ledgerSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (covered : TemplateScopeCovered ledgerSource active occurrence)
    (occurs : ∀ requirement, requirement ∈ result.requirements →
      PrimaryRequirementOccursAt ledgerSource occurrence requirement) :
    UnaryOperatorHasType active operator
      (later.inference.substitution.apply operandType)
      (later.inference.substitution.apply result.type)
      result.requirements := by
  have laterExtendsInitial :
      later.inference.substitution.SemanticallyExtends
        initial.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans substitutionExtends
      progress.substitution_extends
  have resolvedOperandEq :
      later.inference.substitution.apply
          (result.state.resolve operandType) =
        later.inference.substitution.apply operandType :=
    TypeSystem.InferState.apply_resolve_eq_apply substitutionExtends
      operandType
  cases inferenceCase with
  | primitive typing =>
      have mapped :=
        unary_primitive_substitution (target := active) (substitution := later.inference.substitution) rfl typing
      simpa only [resolvedOperandEq] using mapped
  | deferredBitNot operatorEq requirementsEq typeEq deferred =>
      have openTarget : Detail.isOpenIntegerLiteralTarget initial
          integerLiterals operandType = true := by
        unfold Detail.isDeferredBuiltinOperatorTarget at deferred
        split at deferred <;> simp_all
      obtain ⟨_, origin, _, originMember, originResolveEq⟩ :=
        Detail.isOpenIntegerLiteralTarget_true_witness openTarget
      have originTargetEq :
          later.inference.substitution.apply
              (.variable origin.metavariable) =
            later.inference.substitution.apply operandType := by
        calc
          later.inference.substitution.apply
                (.variable origin.metavariable) =
              later.inference.substitution.apply
                (initial.resolve (.variable origin.metavariable)) :=
            (TypeSystem.InferState.apply_resolve_eq_apply
              laterExtendsInitial (.variable origin.metavariable)).symm
          _ = later.inference.substitution.apply
                (initial.resolve operandType) :=
            congrArg later.inference.substitution.apply originResolveEq
          _ = later.inference.substitution.apply operandType :=
            TypeSystem.InferState.apply_resolve_eq_apply laterExtendsInitial
              operandType
      have resultTargetEq : later.inference.substitution.apply result.type =
          later.inference.substitution.apply operandType := by
        rw [typeEq]
        exact resolvedOperandEq
      have supported := integerLiteralTargetsSupported origin
        originMember
      rcases supported with originWord | originInteger
      · have operandWord : later.inference.substitution.apply operandType =
            .word := originTargetEq.symm.trans originWord
        have resultWord : later.inference.substitution.apply result.type =
            .word := resultTargetEq.trans operandWord
        simpa only [operatorEq, operandWord, resultWord, requirementsEq] using
          (UnaryOperatorHasType.wordBitNot (context := active))
      · have operandInteger : later.inference.substitution.apply operandType =
            .integer := originTargetEq.symm.trans originInteger
        have resultInteger : later.inference.substitution.apply result.type =
            .integer := resultTargetEq.trans operandInteger
        simpa only [operatorEq, operandInteger, resultInteger,
          requirementsEq] using
            (UnaryOperatorHasType.integerBitNot (context := active))
  | @trait trait traitName methodName predicates dispatch selected profile
      corresponds =>
      obtain ⟨companions, predicateEq⟩ := operatorTraitPredicates_primary profile
      have traitNameEq := operatorNames.traitName solveSuccess
        (by simpa only [predicateEq] using corresponds.mono requirementsSubset) ⟨methodName, dispatch⟩
      apply UnaryOperatorHasType.trait dispatch
      · have instantiated :=
          operatorProfile_applySubstitution_signatures (substitution := later.inference.substitution) catalog rfl
            (operatorTraitPredicates_instantiates signaturesEq traitNameEq profile)
        simpa only [List.map_cons, List.map_nil, resolvedOperandEq] using
          instantiated
      · have laterCorresponds :=
          corresponds.mono requirementsSubset
        have sequence := solveRequirements_correspondingSequenceProvesAt
          laterCorresponds solveSuccess solvedEq ledger ownership
          activeSignaturesEq activeRequirementsEq assumptionsMono covered
          occurs
        change RequirementSequenceProves active result.requirements
          (predicates.map (TypedTraitResolution.applySubstitution
            later.inference.substitution)) at sequence
        exact sequence


theorem binaryOperatorInferenceCase_hasType_in_active
    {inferenceContext solverContext : Frontend.SourceInference.Context}
    {base active : SourceSemantics.Context}
    {initial later : Frontend.SourceInference.State}
    {solved : List SolvedRequirement}
    {ledgerSource : TypedSource} {occurrence : NodeId}
    {operator : Syntax.BinaryOp} {left right : TypeSystem.Ty}
    {integerLiterals : List IntegerLiteralOrigin}
    {result : Detail.OperatorInferenceResult}
    (inferenceCase : BinaryOperatorInferenceCase inferenceContext (Context.ofSignatures inferenceContext.signatures)
      initial operator left right integerLiterals result)
    (progress : initial.InferenceProgress result.state)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        result.state.inference.substitution)
    (requirementsSubset : result.state.requirements ⊆ later.requirements)
    (integerLiteralTargetsSupported : ∀ origin,
      origin ∈ integerLiterals →
        later.inference.substitution.apply
            (.variable origin.metavariable) = .word ∨
          later.inference.substitution.apply
            (.variable origin.metavariable) = .integer)
    (catalog : SignatureCatalogWellFormed active.signatures)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (operatorNames : OperatorNamesAt inferenceContext.signatures solved result.requirements
      (fun name => ∃ method, BinaryTraitDispatch operator name method))
    (solveSuccess : Detail.solveRequirements solverContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base ledgerSource)
    (ownership : RequirementOwnership base ledgerSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (covered : TemplateScopeCovered ledgerSource active occurrence)
    (occurs : ∀ requirement, requirement ∈ result.requirements →
      PrimaryRequirementOccursAt ledgerSource occurrence requirement) :
    BinaryOperatorHasType active operator
      (later.inference.substitution.apply left)
      (later.inference.substitution.apply right)
      (later.inference.substitution.apply result.type)
      result.requirements := by
  have laterExtendsInitial :
      later.inference.substitution.SemanticallyExtends
        initial.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans substitutionExtends
      progress.substitution_extends
  have resolvedLeftEq :
      later.inference.substitution.apply (result.state.resolve left) =
        later.inference.substitution.apply left :=
    TypeSystem.InferState.apply_resolve_eq_apply substitutionExtends left
  have resolvedRightEq :
      later.inference.substitution.apply (result.state.resolve right) =
        later.inference.substitution.apply right :=
    TypeSystem.InferState.apply_resolve_eq_apply substitutionExtends right
  cases inferenceCase with
  | primitive typing =>
      have mapped :=
        binary_primitive_substitution (target := active) (substitution := later.inference.substitution) rfl typing
      simpa only [resolvedLeftEq, resolvedRightEq] using mapped
  | literalFallback requirementsEq operandsEq typeEq fallback notShift notUnchecked =>
      have finalOperandsEq :
          later.inference.substitution.apply left =
            later.inference.substitution.apply right := by
        calc
          later.inference.substitution.apply left =
              later.inference.substitution.apply
                (result.state.resolve left) := resolvedLeftEq.symm
          _ = later.inference.substitution.apply
                (result.state.resolve right) :=
            congrArg later.inference.substitution.apply operandsEq
          _ = later.inference.substitution.apply right := resolvedRightEq
      have resultTypeEq :
          later.inference.substitution.apply result.type =
            if Detail.binaryResultIsBool operator then .bool
            else later.inference.substitution.apply left := by
        rw [typeEq]
        by_cases returnsBool : Detail.binaryResultIsBool operator = true
        · simp [returnsBool, TypeSystem.Ty.bool]
        · simp [returnsBool, resolvedLeftEq]
      rcases fallback with deferred | staged
      · have deferredFacts :
            Detail.binaryBuiltinType operator = .word ∧
              (Detail.isOpenIntegerLiteralTarget initial integerLiterals left ||
                Detail.isOpenIntegerLiteralTarget initial integerLiterals
                  right) = true := by
          unfold Detail.isDeferredBuiltinOperatorTarget at deferred
          split at deferred <;> simp_all
        have openEither := Bool.or_eq_true_iff.mp deferredFacts.2
        obtain ⟨origin, originMember, originResolveEq⟩ :
            ∃ origin, origin ∈ integerLiterals ∧
              (initial.resolve (.variable origin.metavariable) =
                  initial.resolve left ∨
                initial.resolve (.variable origin.metavariable) =
                  initial.resolve right) := by
          rcases openEither with leftOpen | rightOpen
          · obtain ⟨_, origin, _, member, equal⟩ :=
              Detail.isOpenIntegerLiteralTarget_true_witness leftOpen
            exact ⟨origin, member, .inl equal⟩
          · obtain ⟨_, origin, _, member, equal⟩ :=
              Detail.isOpenIntegerLiteralTarget_true_witness rightOpen
            exact ⟨origin, member, .inr equal⟩
        have originOperandEq :
            later.inference.substitution.apply
                (.variable origin.metavariable) =
              later.inference.substitution.apply left := by
          rcases originResolveEq with leftEq | rightEq
          · calc
              later.inference.substitution.apply
                    (.variable origin.metavariable) =
                  later.inference.substitution.apply
                    (initial.resolve (.variable origin.metavariable)) :=
                (TypeSystem.InferState.apply_resolve_eq_apply
                  laterExtendsInitial (.variable origin.metavariable)).symm
              _ = later.inference.substitution.apply
                    (initial.resolve left) :=
                congrArg later.inference.substitution.apply leftEq
              _ = later.inference.substitution.apply left :=
                TypeSystem.InferState.apply_resolve_eq_apply
                  laterExtendsInitial left
          · calc
              later.inference.substitution.apply
                    (.variable origin.metavariable) =
                  later.inference.substitution.apply
                    (initial.resolve (.variable origin.metavariable)) :=
                (TypeSystem.InferState.apply_resolve_eq_apply
                  laterExtendsInitial (.variable origin.metavariable)).symm
              _ = later.inference.substitution.apply
                    (initial.resolve right) :=
                congrArg later.inference.substitution.apply rightEq
              _ = later.inference.substitution.apply right :=
                TypeSystem.InferState.apply_resolve_eq_apply
                  laterExtendsInitial right
              _ = later.inference.substitution.apply left :=
                finalOperandsEq.symm
        have supported := integerLiteralTargetsSupported origin
          originMember
        rcases supported with originWord | originInteger
        · have leftWord : later.inference.substitution.apply left = .word :=
            originOperandEq.symm.trans originWord
          have rightWord : later.inference.substitution.apply right = .word :=
            finalOperandsEq.symm.trans leftWord
          have resultWord : later.inference.substitution.apply result.type =
              if Detail.binaryResultIsBool operator then .bool
              else .word := by
            rw [resultTypeEq, leftWord]
          have typing := binaryBuiltin_hasType active operator
          rw [deferredFacts.1] at typing
          simpa only [leftWord, rightWord, resultWord, requirementsEq] using
            typing
        · have leftInteger : later.inference.substitution.apply left =
              .integer := originOperandEq.symm.trans originInteger
          have rightInteger : later.inference.substitution.apply right =
              .integer := finalOperandsEq.symm.trans leftInteger
          have resultInteger : later.inference.substitution.apply result.type =
              if Detail.binaryResultIsBool operator then .bool
              else .integer := by
            rw [resultTypeEq, leftInteger]
          have typing := binaryInteger_hasType active operator deferredFacts.1 notShift notUnchecked
          simpa only [leftInteger, rightInteger, resultInteger,
            requirementsEq] using typing
      · have stagedFacts :
            Detail.binaryBuiltinType operator = .word ∧
              result.state.resolve (result.state.resolve left) = .integer := by
          unfold Detail.isStagedIntegerOperatorTarget at staged
          simp_all
        have resolvedLeftInteger :
            later.inference.substitution.apply
                (result.state.resolve left) = .integer := by
          calc
            later.inference.substitution.apply
                  (result.state.resolve left) =
                later.inference.substitution.apply
                  (result.state.resolve (result.state.resolve left)) :=
              (TypeSystem.InferState.apply_resolve_eq_apply
                substitutionExtends (result.state.resolve left)).symm
            _ = later.inference.substitution.apply (.integer) :=
              congrArg later.inference.substitution.apply stagedFacts.2
            _ = .integer := by rfl
        have leftInteger : later.inference.substitution.apply left =
            .integer := resolvedLeftEq.symm.trans resolvedLeftInteger
        have rightInteger : later.inference.substitution.apply right =
            .integer := finalOperandsEq.symm.trans leftInteger
        have resultInteger : later.inference.substitution.apply result.type =
            if Detail.binaryResultIsBool operator then .bool
            else .integer := by
          rw [resultTypeEq, leftInteger]
        have typing := binaryInteger_hasType active operator stagedFacts.1 notShift notUnchecked
        simpa only [leftInteger, rightInteger, resultInteger,
          requirementsEq] using typing
  | @trait trait traitName methodName predicates operandsEq dispatch selected
      profile corresponds =>
      obtain ⟨companions, predicateEq⟩ := operatorTraitPredicates_primary profile
      have traitNameEq := operatorNames.traitName solveSuccess
        (by simpa only [predicateEq] using corresponds.mono requirementsSubset) ⟨methodName, dispatch⟩
      have finalOperandsEq :
          later.inference.substitution.apply left =
            later.inference.substitution.apply right := by
        calc
          later.inference.substitution.apply left =
              later.inference.substitution.apply
                (result.state.resolve left) := resolvedLeftEq.symm
          _ = later.inference.substitution.apply
                (result.state.resolve right) :=
            congrArg later.inference.substitution.apply operandsEq
          _ = later.inference.substitution.apply right := resolvedRightEq
      have instantiated :=
        operatorProfile_applySubstitution_signatures (substitution := later.inference.substitution) catalog rfl
          (operatorTraitPredicates_instantiates signaturesEq traitNameEq profile)
      have finalProfile : OperatorProfileInstantiates active traitName
          methodName (later.inference.substitution.apply left)
          [later.inference.substitution.apply left,
            later.inference.substitution.apply left]
          [later.inference.substitution.apply result.type]
          (predicates.map (TypedTraitResolution.applySubstitution
            later.inference.substitution)) := by
        simpa only [List.map_cons, List.map_nil, resolvedLeftEq] using
          instantiated
      have laterCorresponds := corresponds.mono requirementsSubset
      have sequence := solveRequirements_correspondingSequenceProvesAt
        laterCorresponds solveSuccess solvedEq ledger ownership
        activeSignaturesEq activeRequirementsEq assumptionsMono covered occurs
      change RequirementSequenceProves active result.requirements
        (predicates.map (TypedTraitResolution.applySubstitution
          later.inference.substitution)) at sequence
      have common : BinaryOperatorHasType active operator
          (later.inference.substitution.apply left)
          (later.inference.substitution.apply left)
          (later.inference.substitution.apply result.type)
          result.requirements :=
        .trait dispatch finalProfile sequence
      simpa only [finalOperandsEq] using common


end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedOperatorRecording
/-! Primitive and trait operator tails consume the actual typed operands and
retained requirement sites in the final lexical context. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem inferUnaryOperator_recordExpressionWithExpected_typing_from_interfaces
    {inferenceContext solverContext : Frontend.SourceInference.Context}
    {expression : Syntax.Expr} {id : ExpressionId}
    {operator : Syntax.UnaryOp} {operand : InferredExpression}
    {expected : Option TypeSystem.Ty}
    {integerLiterals : List IntegerLiteralOrigin}
    {operandState later : Frontend.SourceInference.State}
    {inferred : Detail.OperatorInferenceResult}
    {result : InferredExpression × Frontend.SourceInference.State}
    {roots : List NodeId}
    {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context}
    {semanticSource evidenceSource : TypedSource}
    (operatorSuccess : Detail.inferUnaryOperator inferenceContext operator
      operand.type expected integerLiterals operandState = .ok inferred)
    (recordSuccess : Detail.recordExpressionWithExpected inferenceContext
      expression id inferred.type (.unary operator operand.id)
      inferred.requirements expected inferred.state = .ok result)
    (operandType : ExpressionHasType semanticSource active operand.id
      (later.inference.substitution.apply operand.type))
    (operandReady : operandState.InferenceReady)
    (operandBelow : operand.type.VariablesBelow
      operandState.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow operandState.inference.next)
    (integerLiteralTargetsSupported : ∀ origin,
      origin ∈ integerLiterals →
        later.inference.substitution.apply
            (.variable origin.metavariable) = .word ∨
          later.inference.substitution.apply
            (.variable origin.metavariable) = .integer)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        result.2.inference.substitution)
    (requirementsSubset : result.2.requirements ⊆ later.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (result.2.toTypedSource roots) evidenceSource result.1.id)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces inferenceContext.signatures solved evidenceSource)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt
      (result.2.toTypedSource roots) evidenceSource result.1.id)
    (operatorsRetained : ExpressionOperatorSiteRetainedAt
      (result.2.toTypedSource roots) evidenceSource result.1.id)
    (activeCatalog : SignatureCatalogWellFormed active.signatures)
    (activeBinders : TypeParameterBindersWellFormed active)
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
  have operatorProperties := Detail.inferUnaryOperator_inferenceProperties
    operandReady operandBelow expectedBelow operatorSuccess
  have inferenceCase : UnaryOperatorInferenceCase inferenceContext
      (Context.ofSignatures inferenceContext.signatures) operandState operator operand.type integerLiterals inferred :=
    inferUnaryOperator_success_case operatorSuccess
      operatorProperties.2.1.solved
  have expectedBelowInferred : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow inferred.state.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken operatorProperties.1.next_le
  have recordProperties :=
    Detail.recordExpressionWithExpected_inferenceProperties
      operatorProperties.2.1 operatorProperties.2.2 expectedBelowInferred
      recordSuccess
  have inferredSubstitutionExtends :
      later.inference.substitution.SemanticallyExtends
        inferred.state.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans substitutionExtends
      recordProperties.1.substitution_extends
  have inferredRequirementsSubset :
      inferred.state.requirements ⊆ later.requirements :=
    List.Subset.trans
      (Detail.recordExpressionWithExpected_requirements_subset recordSuccess)
      requirementsSubset
  obtain ⟨coercions, recordedContains⟩ :=
    recordExpressionWithExpected_success_containsExpression recordSuccess roots
  have operatorRequirementsOccur : ∀ requirement,
      requirement ∈ inferred.requirements →
        PrimaryRequirementOccursAt evidenceSource
          (.expression result.1.id) requirement := by
    intro requirement member
    apply retained recordedContains
    simp [member]
  have operatorNames : OperatorNamesAt inferenceContext.signatures solved inferred.requirements
      (fun name => ∃ method, UnaryTraitDispatch operator name method) :=
    OperatorNamesAt.of_retained operatorsRetained interfaces recordedContains rfl (by
      intro name selected
      obtain ⟨method, dispatch⟩ := selected
      cases dispatch <;> exact ⟨_, rfl⟩)
  have operatorType : UnaryOperatorHasType active operator
      (later.inference.substitution.apply operand.type)
      (later.inference.substitution.apply inferred.type)
      inferred.requirements :=
    unaryOperatorInferenceCase_hasType_in_active inferenceCase
      operatorProperties.1 inferredSubstitutionExtends
      inferredRequirementsSubset
      integerLiteralTargetsSupported activeCatalog signaturesEq
      operatorNames solveSuccess solvedEq ledger ownership
      activeSignaturesEq activeRequirementsEq assumptionsMono covered
      operatorRequirementsOccur
  have formType : ExpressionFormHasRawType semanticSource active
      ((ExpressionForm.unary operator operand.id).applySubstitution
        later.inference.substitution)
      (later.inference.substitution.apply inferred.type)
      (.ordinary inferred.requirements) := by
    simpa [ExpressionForm.applySubstitution] using
      (ExpressionFormHasRawType.unary operandType operatorType)
  have rawAdmissible : TypeAdmissible active
      (later.inference.substitution.apply inferred.type) :=
    operatorType.result_type_admissible activeCatalog activeBinders
      operandType.type_admissible
  exact
    recordExpressionWithExpected_success_ordinaryExpressionTypingBase_from_interfaces
      recordSuccess substitutionExtends requirementsSubset retained formType
      rawAdmissible interfaces coercionsRetained activeCatalog
      signaturesEq solveSuccess solvedEq ledger ownership
      activeSignaturesEq activeRequirementsEq assumptionsMono covered


private theorem binaryOperatorHasType_operand_types_eq
    {context : SourceSemantics.Context} {operator : Syntax.BinaryOp}
    {left right result : TypeSystem.Ty}
    {requirements : List RequirementId}
    (typing : BinaryOperatorHasType context operator left right result
      requirements) :
    left = right := by
  cases typing <;> rfl


theorem inferBinaryOperator_recordExpressionWithExpected_typing_from_interfaces
    {inferenceContext solverContext : Frontend.SourceInference.Context}
    {expression : Syntax.Expr} {id : ExpressionId}
    {operator : Syntax.BinaryOp}
    {left right : InferredExpression}
    {expected : Option TypeSystem.Ty}
    {integerLiterals : List IntegerLiteralOrigin}
    {operandState later : Frontend.SourceInference.State}
    {inferred : Detail.OperatorInferenceResult}
    {result : InferredExpression × Frontend.SourceInference.State}
    {roots : List NodeId}
    {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context}
    {semanticSource evidenceSource : TypedSource}
    (operatorSuccess : Detail.inferBinaryOperator inferenceContext operator
      left.type right.type expected integerLiterals operandState = .ok inferred)
    (recordSuccess : Detail.recordExpressionWithExpected inferenceContext
      expression id inferred.type (.binary left.id operator right.id)
      inferred.requirements expected inferred.state = .ok result)
    (leftType : ExpressionHasType semanticSource active left.id
      (later.inference.substitution.apply left.type))
    (rightType : ExpressionHasType semanticSource active right.id
      (later.inference.substitution.apply right.type))
    (operandReady : operandState.InferenceReady)
    (leftBelow : left.type.VariablesBelow operandState.inference.next)
    (rightBelow : right.type.VariablesBelow operandState.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow operandState.inference.next)
    (integerLiteralTargetsSupported : ∀ origin,
      origin ∈ integerLiterals →
        later.inference.substitution.apply
            (.variable origin.metavariable) = .word ∨
          later.inference.substitution.apply
            (.variable origin.metavariable) = .integer)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        result.2.inference.substitution)
    (requirementsSubset : result.2.requirements ⊆ later.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (result.2.toTypedSource roots) evidenceSource result.1.id)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces inferenceContext.signatures solved evidenceSource)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt
      (result.2.toTypedSource roots) evidenceSource result.1.id)
    (operatorsRetained : ExpressionOperatorSiteRetainedAt
      (result.2.toTypedSource roots) evidenceSource result.1.id)
    (activeCatalog : SignatureCatalogWellFormed active.signatures)
    (activeBinders : TypeParameterBindersWellFormed active)
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
  have operatorProperties := Detail.inferBinaryOperator_inferenceProperties
    operandReady leftBelow rightBelow expectedBelow operatorSuccess
  have inferenceCase : BinaryOperatorInferenceCase inferenceContext
      (Context.ofSignatures inferenceContext.signatures) operandState operator left.type right.type integerLiterals
      inferred :=
    inferBinaryOperator_success_case operatorSuccess
  have expectedBelowInferred : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow inferred.state.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken operatorProperties.1.next_le
  have recordProperties :=
    Detail.recordExpressionWithExpected_inferenceProperties
      operatorProperties.2.1 operatorProperties.2.2 expectedBelowInferred
      recordSuccess
  have inferredSubstitutionExtends :
      later.inference.substitution.SemanticallyExtends
        inferred.state.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans substitutionExtends
      recordProperties.1.substitution_extends
  have inferredRequirementsSubset :
      inferred.state.requirements ⊆ later.requirements :=
    List.Subset.trans
      (Detail.recordExpressionWithExpected_requirements_subset recordSuccess)
      requirementsSubset
  obtain ⟨coercions, recordedContains⟩ :=
    recordExpressionWithExpected_success_containsExpression recordSuccess roots
  have operatorRequirementsOccur : ∀ requirement,
      requirement ∈ inferred.requirements →
        PrimaryRequirementOccursAt evidenceSource
          (.expression result.1.id) requirement := by
    intro requirement member
    apply retained recordedContains
    simp [member]
  have operatorNames : OperatorNamesAt inferenceContext.signatures solved inferred.requirements
      (fun name => ∃ method, BinaryTraitDispatch operator name method) :=
    OperatorNamesAt.of_retained operatorsRetained interfaces recordedContains rfl (by
      intro name selected
      obtain ⟨method, dispatch⟩ := selected
      cases dispatch <;> exact ⟨_, rfl⟩)
  have operatorType : BinaryOperatorHasType active operator
      (later.inference.substitution.apply left.type)
      (later.inference.substitution.apply right.type)
      (later.inference.substitution.apply inferred.type)
      inferred.requirements :=
    binaryOperatorInferenceCase_hasType_in_active inferenceCase
      operatorProperties.1 inferredSubstitutionExtends
      inferredRequirementsSubset
      integerLiteralTargetsSupported activeCatalog signaturesEq
      operatorNames solveSuccess solvedEq ledger ownership
      activeSignaturesEq activeRequirementsEq assumptionsMono covered
      operatorRequirementsOccur
  have operandTypesEq :
      later.inference.substitution.apply left.type =
        later.inference.substitution.apply right.type :=
    binaryOperatorHasType_operand_types_eq operatorType
  have rightTypeAsLeft : ExpressionHasType semanticSource active right.id
      (later.inference.substitution.apply left.type) := by
    rw [operandTypesEq]
    exact rightType
  have operatorTypeAsLeft : BinaryOperatorHasType active operator
      (later.inference.substitution.apply left.type)
      (later.inference.substitution.apply left.type)
      (later.inference.substitution.apply inferred.type)
      inferred.requirements := by
    rwa [← operandTypesEq] at operatorType
  have formType : ExpressionFormHasRawType semanticSource active
      ((ExpressionForm.binary left.id operator right.id).applySubstitution
        later.inference.substitution)
      (later.inference.substitution.apply inferred.type)
      (.ordinary inferred.requirements) := by
    simpa [ExpressionForm.applySubstitution] using
      (ExpressionFormHasRawType.binary leftType rightTypeAsLeft
        operatorTypeAsLeft)
  have rawAdmissible : TypeAdmissible active
      (later.inference.substitution.apply inferred.type) :=
    operatorTypeAsLeft.result_type_admissible activeCatalog activeBinders
      leftType.type_admissible
  exact
    recordExpressionWithExpected_success_ordinaryExpressionTypingBase_from_interfaces
      recordSuccess substitutionExtends requirementsSubset retained formType
      rawAdmissible interfaces coercionsRetained activeCatalog
      signaturesEq solveSuccess solvedEq ledger ownership
      activeSignaturesEq activeRequirementsEq assumptionsMono covered


end Solcore.SourceSemantics.SourceInferenceSoundness
end
