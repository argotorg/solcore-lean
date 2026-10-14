import Solcore.SourceSemantics.SourceInferenceSelectedForItemTransport
import Solcore.SourceSemantics.SourceInferenceSelectedLetState

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferForItemFuelRootedSoundness_letAnnotatedUninitialized {fuel : Nat} :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {item : Syntax.ForItem} {name : Syntax.Identifier} {sourceType : Syntax.TypeExpr} {initial final : State}
    {inferred : ForItemForm} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    {control : ControlContext},
    item.value = .letDecl name (some sourceType) none →
    Detail.inferForItemFuel (fuel + 1) inferenceContext item initial =
      .ok (inferred, final) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource →
    inferenceContext.signatures = wholeContext.signatures →
    inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner →
    inferenceContext.typeParameters = wholeContext.typeParameters →
    inferenceContext.assumptions = wholeContext.assumptions →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters →
    RecursiveStatementInvariant wholeContext expectedReturn finalized
      initial semanticContext →
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn) →
    finalized.substitution.SemanticallyExtends final.inference.substitution →
    (∀ reference ∈ inferred.references, SubtreePreserved finalized.substitution
      (final.toTypedSource roots) semanticSource reference) →
    (∀ reference ∈ inferred.references, RawSubtreePreserved (final.toTypedSource roots)
      (evidenceState.toTypedSource roots) reference) →
    final.integerPatterns ⊆ evidenceState.integerPatterns →
    final.integerLiterals ⊆ evidenceState.integerLiterals →
    final.requirements ⊆ evidenceState.requirements →
    semanticSource.owner = initial.owner →
    ForItemReferencesCovered finalized.typedSource
      finalized.substitution semanticContext inferred →
    ForItemBindingRetained (evidenceState.toTypedSource roots) inferred →
    (∀ reference ∈ inferred.references, ActualContext.Covers finalized frames reference) →
    ActualForItemBindings finalized frames inferred →
    ∃ finalContext,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        final finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant final (evidenceState.toTypedSource roots) ∧
      ForItemHasType semanticSource control semanticContext
        (inferred.applySubstitution finalized.substitution)
        finalContext := by
  intro wholeContext inferenceContext wholeReturn expectedReturn item name sourceType initial final inferred
    evidenceState roots finalized semanticSource frames semanticContext control itemEq success resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions canonicalCatalog canonical invariant actual operational
    returnAdmissible extension semantic raw patterns literals requirements sourceOwner covered bindings actualCovered actualBindings
  have semanticSignatures : semanticContext.signatures = inferenceContext.signatures :=
    (RecursiveExpressionInvariant.ofStatement invariant).signatures_eq_whole.trans signaturesEq.symm
  have semanticParameters : semanticContext.typeParameters = inferenceContext.typeParameters :=
    invariant.typeParametersEq.trans parametersEq.symm
  have semanticOwner : semanticContext.currentDeclaration = some inferenceContext.scope.genericOwner := by
    rw [ownerEq]
    exact invariant.declarationEq
  obtain ⟨finalContext, finalInvariant, typing⟩ := inferForItemFuel_success_letAnnotatedUninitialized_scoped
    itemEq success formation functions canonical semanticSignatures semanticParameters semanticOwner invariant sourceOwner extension
  have finalOperational : ActualStateInvariant final (evidenceState.toTypedSource roots) := by
    obtain ⟨resolvedType, locals, valueType, generalized, binding,
      resolution, _localsEq, valueTypeEq, generalizedEq, bindingEq, resultEq⟩ :=
      inferForItemFuel_success_letAnnotatedUninitialized_facts itemEq success
    obtain ⟨typeWellFormed, _closedScheme, _closedRequirements, _generalizes⟩ :=
      resolvedAnnotationBinderFacts_afterSubstitution
        (target := semanticContext) (outer := finalized.substitution)
        resolution valueTypeEq generalizedEq bindingEq canonical semanticSignatures semanticParameters semanticOwner
    have resolvedByState : initial.resolve resolvedType = resolvedType := by
      simpa [State.resolve, InferState.resolve] using
        Detail.resolveSourceType_success_apply_eq_self initial.inference.substitution resolution
    have valueClosed : valueType.freeVariables = [] := by
      rw [valueTypeEq, resolvedByState]
      exact StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil typeWellFormed
    have schemeEq : generalized.scheme = .mono valueType := by
      rw [generalizedEq]
      exact (generalizeValue_closed_facts initial locals initial.nextRequirement valueType semanticContext valueClosed).1
    have requirementsEq : generalized.requirements = [] := by
      rw [generalizedEq]
      exact (generalizeValue_closed_facts initial locals initial.nextRequirement valueType semanticContext valueClosed).2.1
    have bindingOperational : ActualStateInvariant binding.2 (evidenceState.toTypedSource roots) := by
      rw [← bindingEq, schemeEq, requirementsEq]
      exact ((operational.withLocals locals).allocateMonoBinder name.value valueType (some name.span) false)
    have stateEq : final = binding.2 := congrArg Prod.snd resultEq
    rw [stateEq]
    exact bindingOperational
  exact ⟨finalContext, finalInvariant, actual.of_forItem typing, finalOperational, typing⟩

theorem actualInferForItemFuelRootedSoundness_letAnnotatedInitialized {fuel : Nat}
    (expressionSound : ActualInferExprFuelRootedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {item : Syntax.ForItem} {name : Syntax.Identifier} {sourceType : Syntax.TypeExpr} {initializer : Syntax.Expr} {initial final : State}
    {inferred : ForItemForm} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    {control : ControlContext},
    item.value = .letDecl name (some sourceType) (some initializer) →
    Detail.inferForItemFuel (fuel + 1) inferenceContext item initial =
      .ok (inferred, final) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource →
    inferenceContext.signatures = wholeContext.signatures →
    inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner →
    inferenceContext.typeParameters = wholeContext.typeParameters →
    inferenceContext.assumptions = wholeContext.assumptions →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters →
    RecursiveStatementInvariant wholeContext expectedReturn finalized
      initial semanticContext →
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn) →
    finalized.substitution.SemanticallyExtends final.inference.substitution →
    (∀ reference ∈ inferred.references, SubtreePreserved finalized.substitution
      (final.toTypedSource roots) semanticSource reference) →
    (∀ reference ∈ inferred.references, RawSubtreePreserved (final.toTypedSource roots)
      (evidenceState.toTypedSource roots) reference) →
    final.integerPatterns ⊆ evidenceState.integerPatterns →
    final.integerLiterals ⊆ evidenceState.integerLiterals →
    final.requirements ⊆ evidenceState.requirements →
    semanticSource.owner = initial.owner →
    ForItemReferencesCovered finalized.typedSource
      finalized.substitution semanticContext inferred →
    ForItemBindingRetained (evidenceState.toTypedSource roots) inferred →
    (∀ reference ∈ inferred.references, ActualContext.Covers finalized frames reference) →
    ActualForItemBindings finalized frames inferred →
    ∃ finalContext,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        final finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant final (evidenceState.toTypedSource roots) ∧
      ForItemHasType semanticSource control semanticContext
        (inferred.applySubstitution finalized.substitution)
        finalContext := by
  intro wholeContext inferenceContext wholeReturn expectedReturn item name sourceType initializer initial final inferred
    evidenceState roots finalized semanticSource frames semanticContext control itemEq success resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical invariant actual operational
    returnAdmissible extension semantic raw patterns literals requirements sourceOwner covered bindings actualCovered actualBindings
  have semanticSignatures : semanticContext.signatures = inferenceContext.signatures :=
    (RecursiveExpressionInvariant.ofStatement invariant).signatures_eq_whole.trans signaturesEq.symm
  have semanticParameters : semanticContext.typeParameters = inferenceContext.typeParameters :=
    invariant.typeParametersEq.trans parametersEq.symm
  have semanticOwner : semanticContext.currentDeclaration = some inferenceContext.scope.genericOwner := by
    rw [ownerEq]
    exact invariant.declarationEq
  obtain ⟨resolvedType, child, initializerState, locals, valueType, generalized, binding,
    resolution, childSuccess, localsEq, valueEq, generalizedEq, bindingEq, resultEq⟩ :=
    inferForItemFuel_success_letAnnotatedInitialized_facts itemEq success
  have sameItem : inferred = .letDecl binding.1 (some child.id) := congrArg Prod.fst resultEq
  have sameState : final = binding.2 := congrArg Prod.snd resultEq
  subst inferred
  subst final
  have expectedBelow : ∀ type ∈ (some resolvedType : Option Ty), type.VariablesBelow initial.inference.next := by
    intro type member
    cases Option.mem_def.mp member
    exact Detail.resolveSourceType_success_variablesBelow resolution _
  have childProperties := Detail.inferExprFuel_inferenceProperties invariant.ready formation functions expectedBelow childSuccess
  have rawExpected := inferExprFuel_success_expected_type_afterProgress childSuccess
    (State.InferenceProgress.refl childProperties.2.1.solved)
  have annotationValueEq : valueType = initializerState.resolve resolvedType := valueEq.trans rawExpected
  obtain ⟨typeWellFormed, closedScheme, closedRequirements, generalizes⟩ :=
    resolvedAnnotationBinderFacts_afterSubstitution (outer := finalized.substitution)
      resolution annotationValueEq generalizedEq bindingEq canonical semanticSignatures semanticParameters semanticOwner
  have childExpected : ∀ type ∈ (some resolvedType : Option Ty),
      TypeAdmissible semanticContext (finalized.substitution.apply type) := by
    intro type member
    cases Option.mem_def.mp member
    rw [Detail.resolveSourceType_success_apply_eq_self finalized.substitution resolution]
    exact TypeAdmissible.ofWellFormed typeWellFormed
  have childMember : (.expression child.id : NodeId) ∈ (ForItemForm.letDecl binding.1 (some child.id)).references := by
    simp [ForItemForm.references]
  have initializerContextEq : localSchemeInitializerContext semanticContext
      (binding.1.applySubstitution finalized.substitution) = semanticContext := by
    rw [localSchemeInitializerContext_eq_withTypeVariables _ _ closedRequirements]
    simp only [closedScheme, Scheme.mono, Context.withTypeVariables, List.append_nil]
  have childCovered : TemplateScopeCovered finalized.typedSource semanticContext (.expression child.id) := by
    have selectedCoverage := covered _ childMember
    simpa only [forItemCoverageContext, initializerContextEq] using selectedCoverage
  have childToFinal : TypingSourceExtends (initializerState.toTypedSource roots) (binding.2.toTypedSource roots) := by
    rw [← bindingEq]
    exact ⟨rfl, ⟨[], by simp [State.allocateBinder, State.withLocals, State.toTypedSource]⟩⟩
  have childExtension : finalized.substitution.SemanticallyExtends initializerState.inference.substitution := by
    simpa [← bindingEq, State.allocateBinder, State.withLocals] using extension
  have childPatterns : initializerState.integerPatterns ⊆ evidenceState.integerPatterns := by
    simpa [← bindingEq, State.allocateBinder, State.withLocals] using patterns
  have childLiterals : initializerState.integerLiterals ⊆ evidenceState.integerLiterals := by
    simpa [← bindingEq, State.allocateBinder, State.withLocals] using literals
  have childRequirements : initializerState.requirements ⊆ evidenceState.requirements := by
    simpa [← bindingEq, State.allocateBinder, State.withLocals] using requirements
  have childTyped := expressionSound childSuccess resources interfaces childExtension signaturesEq ownerEq parametersEq assumptionsEq
    formation functions catalog canonical (RecursiveExpressionInvariant.ofStatement invariant) actual operational expectedBelow childExpected
    ((semantic _ childMember).monoBefore childToFinal) ((raw _ childMember).monoBefore childToFinal)
    childPatterns childLiterals childRequirements childCovered (actualCovered _ childMember)
  have certificate : ActualAnnotatedInitializedForItemCertificate fuel inferenceContext name sourceType initializer initial
      (.letDecl binding.1 (some child.id), binding.2) semanticSource semanticContext finalized.substitution :=
    ⟨resolvedType, child, initializerState, locals, valueType, generalized, binding,
      resolution, childSuccess, localsEq, valueEq, generalizedEq, bindingEq, rfl, childTyped⟩
  obtain ⟨finalContext, finalInvariant, typing⟩ := inferForItemFuel_success_letAnnotatedInitialized_of_certificate
    success formation functions canonical semanticSignatures semanticParameters semanticOwner invariant sourceOwner extension certificate
  have resolvedByState : initializerState.resolve resolvedType = resolvedType := by
    simpa [State.resolve, InferState.resolve] using
      Detail.resolveSourceType_success_apply_eq_self initializerState.inference.substitution resolution
  have valueClosed : valueType.freeVariables = [] := by
    rw [annotationValueEq, resolvedByState]
    exact StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil typeWellFormed
  have schemeEq : generalized.scheme = .mono valueType := by
    rw [generalizedEq]
    exact (generalizeValue_closed_facts initializerState locals initial.nextRequirement valueType semanticContext valueClosed).1
  have requirementsEq : generalized.requirements = [] := by
    rw [generalizedEq]
    exact (generalizeValue_closed_facts initializerState locals initial.nextRequirement valueType semanticContext valueClosed).2.1
  have bindingOperational : ActualStateInvariant binding.2 (evidenceState.toTypedSource roots) := by
    rw [← bindingEq, schemeEq, requirementsEq]
    exact (((operational.ofExpression childSuccess childProperties.1.next_le).withLocals locals).allocateMonoBinder
      name.value valueType (some name.span) false)
  exact ⟨finalContext, finalInvariant, actual.of_forItem typing, bindingOperational, typing⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
