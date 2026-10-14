import Solcore.SourceSemantics.SourceInferenceSelectedMonomorphicLet
import Solcore.SourceSemantics.SourceInferenceActualRootedContracts

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000

namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferForItemFuelRootedSoundness_letUnannotatedInitialized {fuel : Nat}
    (expressionSound : ActualInferExprFuelRootedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {item : Syntax.ForItem} {name : Syntax.Identifier} {initializer : Syntax.Expr} {initial final : State}
    {inferred : ForItemForm} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    {control : ControlContext},
    item.value = .letDecl name none (some initializer) →
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
  intro wholeContext inferenceContext wholeReturn expectedReturn item name initializer initial final inferred
    evidenceState roots finalized semanticSource frames semanticContext control itemEq success resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical invariant actual operational
    _returnAdmissible extension semantic raw patterns literals requirements sourceOwner covered bindings actualCovered _actualBindings
  obtain ⟨child, initializerState, locals, valueType, generalized, binding,
    childSuccess, localsEq, valueEq, generalizedEq, bindingEq, resultEq⟩ :=
    inferForItemFuel_success_letUnannotatedInitialized_facts itemEq success
  have sameItem : inferred = .letDecl binding.1 (some child.id) := congrArg Prod.fst resultEq
  have sameState : final = binding.2 := congrArg Prod.snd resultEq
  subst inferred
  subst final
  have retained : binding.1 ∈ (evidenceState.toTypedSource roots).initializedLetBinders :=
    (bindings ⟨binding.1, .expression child.id⟩ (by simp [forItemInitializedLetBindings])).1
  have rawMono : binding.1.scheme.quantified = [] := operational.sourceMonomorphic _ retained
  have binderEq := congrArg Prod.fst bindingEq
  have generalizedMono : generalized.scheme.quantified = [] := by
    rw [← binderEq] at rawMono
    exact rawMono
  have schemeEq : generalized.scheme = .mono valueType := by
    have bodyEq : generalized.scheme.body = valueType := by rw [generalizedEq]; rfl
    cases scheme : generalized.scheme with
    | mk quantified body =>
      simp only [scheme] at generalizedMono bodyEq
      simp only [generalizedMono, bodyEq, Scheme.mono]
  have requirementsEq : generalized.requirements = [] := by
    rw [generalizedEq]
    apply Detail.generalizeValue_requirements_empty_of_quantified_eq_nil
    rwa [← generalizedEq]
  have rawScheme : binding.1.scheme = .mono valueType := by
    rw [← binderEq]
    exact schemeEq
  have rawRequirements : binding.1.schemeRequirements = [] := by
    rw [← binderEq]
    exact requirementsEq
  have initializerContextEq : localSchemeInitializerContext semanticContext
      (binding.1.applySubstitution finalized.substitution) = semanticContext := by
    rw [localSchemeInitializerContext_eq_withTypeVariables _ _ (by simp [rawRequirements])]
    rw [show (binding.1.applySubstitution finalized.substitution).scheme.quantified = [] from rawMono]
    exact Context.withTypeVariables_nil _
  have childMember : (.expression child.id : NodeId) ∈ (ForItemForm.letDecl binding.1 (some child.id)).references := by
    simp [ForItemForm.references]
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
    formation functions catalog canonical (RecursiveExpressionInvariant.ofStatement invariant) actual operational
    (by simp) (by simp) (SubtreePreserved.ofTypingSourceExtends (TypingSourceExtends.refl _))
    ((raw _ childMember).monoBefore childToFinal) childPatterns childLiterals childRequirements childCovered
    (actualCovered _ childMember)
  have semanticChild := SourceSubgraphTransport.expression
    ((semantic _ childMember).monoBefore childToFinal).subgraph childTyped (.inl rfl)
  have bodyEq : (binding.1.applySubstitution finalized.substitution).scheme.body =
      finalized.substitution.apply child.type := by
    simpa [TypedBinder.applySubstitution, rawScheme, Scheme.apply, Scheme.mono, Substitution.without,
      valueEq, State.resolve, InferState.resolve] using childExtension child.type
  have childAligned : LocalEnvironmentAligned initializerState finalized.substitution semanticContext :=
    (invariant.active.inferExprFuel childSuccess).aligned
  have childMono : ∀ binder ∈ initializerState.localBinders, binder.scheme.quantified = [] := by
    have bindersEq : initializerState.localBinders = initial.localBinders :=
      congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq childSuccess)
    simpa only [bindersEq] using operational.monomorphicBinders
  have localsMono : ∀ entry ∈ locals, entry.2.quantified = [] := by
    rw [localsEq]
    exact MonomorphicGeneralization.binderEnvironment_monomorphic childMono
  have localsPresent : ∀ entry ∈ locals, ∃ id,
      (id, entry.2.apply finalized.substitution) ∈ semanticContext.locals := by
    rw [localsEq]
    exact MonomorphicGeneralization.binderEnvironment_localPresent childAligned childMono childExtension
  have certificate : UnannotatedInitializedLetCertificate (initializerState.toTypedSource roots)
      semanticContext finalized.substitution binding.1 child.id := by
    apply unannotatedInitializedLetCertificate_of_finalMonomorphic resources generalizedEq bindingEq
      rawMono localsMono localsPresent childRequirements childExtension invariant.solvedRequirementsEq
    rw [initializerContextEq, bodyEq]
    exact childTyped
  obtain ⟨finalContext, finalActive, typingRaw⟩ :=
    unannotatedInitializedForItemHasType_afterSubstitution (control := control)
      generalizedEq bindingEq (invariant.active.inferExprFuel childSuccess)
      (Detail.inferExprFuel_preserves_localBindersBelowNextLocal invariant.bindersBelow childSuccess)
      rfl certificate
  have typing : ForItemHasType semanticSource control semanticContext
      ((ForItemForm.letDecl binding.1 (some child.id)).applySubstitution finalized.substitution)
      finalContext := by
    cases typingRaw with
    | letInitialized _ mono generalizes extension =>
      refine .letInitialized ?_ mono generalizes ?_
      · rw [bodyEq]
        exact semanticChild
      · have sameOwner : semanticSource.owner = initializerState.owner :=
          sourceOwner.trans (Detail.inferExprFuel_preserves_owner childSuccess).symm
        rw [sameOwner]
        exact extension
    | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly rawMono)
  have finalMono : ∀ binder ∈ binding.2.localBinders, binder.scheme.quantified = [] := by
    intro binder member
    rw [← bindingEq] at member
    change binder ∈ _ :: initializerState.localBinders at member
    rcases List.mem_cons.mp member with rfl | member
    · exact generalizedMono
    · exact childMono binder member
  have finalInvariant := RecursiveStatementInvariant.of_forItem_typing invariant success formation functions
    finalActive (monomorphicBinders_isolation finalMono) extension typing
  have childProperties := Detail.inferExprFuel_inferenceProperties invariant.ready formation functions (by simp) childSuccess
  have finalOperational : ActualStateInvariant binding.2 (evidenceState.toTypedSource roots) := by
    rw [← bindingEq, schemeEq, requirementsEq]
    exact (((operational.ofExpression childSuccess childProperties.1.next_le).withLocals locals).allocateMonoBinder
      name.value valueType (some name.span) false)
  exact ⟨finalContext, finalInvariant, actual.of_forItem typing, finalOperational, typing⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
