import Solcore.SourceSemantics.Internal.Selected.Loops
import Solcore.SourceSemantics.Internal.Selected.State
import Solcore.SourceSemantics.Internal.Selected.StatementReferences
import Solcore.SourceSemantics.Internal.Inference.RootedContracts
import Solcore.SourceSemantics.Internal.Selected.Children
import Solcore.SourceSemantics.Internal.Selected.Statements

/-!
# Selected lets

Annotated and unannotated lets in statements and `for` headers, with the statement dispatch.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedAnnotatedForItems
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedAnnotatedLetSoundness
/-! Actual local declarations preserve the checked semantic context and the
raw lexical quantifier invariant used by subsequent inference. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actual_letAnnotatedUninitialized
    {fuel : Nat} {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier} {sourceType : Syntax.TypeExpr}
    {expectedReturn : Ty} {initial allocated evidenceState : State} {id : StatementId}
    {result : Detail.StatementResult} {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding} {semanticContext : SourceSemantics.Context} {roots : List NodeId}
    (form : statement.value = .letDecl name (some sourceType) none)
    (allocation : initial.allocateStatementId = (id, allocated))
    (accepted : Detail.inferStatementFuel (fuel + 1) inferenceContext statement expectedReturn initial = .ok result)
    (formation : ProgramSignatureFormationValidated inferenceContext.signatures)
    (functions : ∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function (Ty.productMany candidate.parameterTypes) (Ty.productMany candidate.returnTypes))
    (parameters : SignatureParametersWellFormed inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (signaturesEq : semanticContext.signatures = inferenceContext.signatures)
    (parametersEq : semanticContext.typeParameters = inferenceContext.typeParameters)
    (declarationEq : semanticContext.currentDeclaration = some inferenceContext.scope.genericOwner)
    (invariant : RecursiveStatementInvariant wholeContext expectedReturn finalized initial semanticContext)
    (contextAt : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType ((result.state.toTypedSource roots).applySubstitution finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution result facts := by
  have isolated : ActiveSchemeQuantifierIsolation result.state ∧
      ActiveBinderCaptureOrigins result.state (evidenceState.toTypedSource roots) ∧
      ActiveQuantifiersBelowNext result.state := by
    obtain ⟨resolvedType, locals, valueType, generalized, binding,
      resolution, _localsEq, valueTypeEq, generalizedEq, bindingEq, resultEq, _contains⟩ :=
      inferStatementFuel_success_letAnnotatedUninitialized_facts form allocation accepted roots
    obtain ⟨typeWellFormed, _closedScheme, _closedRequirements, _generalizes⟩ :=
      resolvedAnnotationBinderFacts_afterSubstitution
        (target := semanticContext) (outer := finalized.substitution)
        resolution valueTypeEq generalizedEq bindingEq parameters signaturesEq parametersEq declarationEq
    have resolvedByState : allocated.resolve resolvedType = resolvedType := by
      simpa [State.resolve, InferState.resolve] using
        Detail.resolveSourceType_success_apply_eq_self allocated.inference.substitution resolution
    have valueClosed : valueType.freeVariables = [] := by
      rw [valueTypeEq, resolvedByState]
      exact StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil typeWellFormed
    have schemeEq : generalized.scheme = .mono valueType := by
      rw [generalizedEq]
      exact (generalizeValue_closed_facts allocated locals allocated.nextRequirement valueType semanticContext valueClosed).1
    have requirementsEq : generalized.requirements = [] := by
      rw [generalizedEq]
      exact (generalizeValue_closed_facts allocated locals allocated.nextRequirement valueType semanticContext valueClosed).2.1
    have allocatedIsolated := activeSchemeQuantifierIsolation_allocateStatementId invariant.schemeIsolation allocation
    have bindingIsolated : ActiveSchemeQuantifierIsolation binding.2 := by
      rw [← bindingEq, schemeEq, requirementsEq]
      exact activeSchemeQuantifierIsolation_allocateMonoBinder (allocated.withLocals locals) name.value valueType
        (some name.span) (activeSchemeQuantifierIsolation_transport allocatedIsolated rfl)
        (by intro metavariable member; simp [valueClosed] at member)
    have bindingOperational : ActualStateInvariant binding.2 (evidenceState.toTypedSource roots) := by
      rw [← bindingEq, schemeEq, requirementsEq]
      exact (((operational.allocateStatementId allocation).withLocals locals).allocateMonoBinder
        name.value valueType (some name.span) false)
    rw [resultEq]
    exact ⟨activeSchemeQuantifierIsolation_transport bindingIsolated rfl,
      bindingOperational.origins.congr_localBinders rfl,
      activeQuantifiersBelowNext_transport bindingOperational.quantifiersBelow rfl (Nat.le_refl _)⟩
  obtain ⟨finalContext, facts, finalInvariant, typed, matching⟩ :=
    invariant.close_statement_branch accepted formation functions
      (inferStatementFuel_preserves_localBindersBelowNextLocal invariant.bindersBelow accepted)
      extension isolated.1
      (inferStatementFuel_success_letAnnotatedUninitialized_sound form allocation accepted parameters
        signaturesEq parametersEq declarationEq invariant.active invariant.bindersBelow roots)
  exact ⟨finalContext, facts, finalInvariant, contextAt.of_statement typed,
    operational.ofStatementWithScope accepted isolated.2.1 isolated.2.2, typed, matching⟩

/-- Annotation resolution fixes a closed value type even when the initializer
runs the full expression checker. Binder allocation therefore introduces no
new quantified variables. -/
theorem actual_letAnnotatedInitialized
    {fuel : Nat} {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier} {sourceType : Syntax.TypeExpr}
    {initializer : Syntax.Expr} {expectedReturn : Ty}
    {initial allocated evidenceState : State} {id : StatementId}
    {result : Detail.StatementResult} {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding} {semanticContext : SourceSemantics.Context} {roots : List NodeId}
    (form : statement.value = .letDecl name (some sourceType) (some initializer))
    (allocation : initial.allocateStatementId = (id, allocated))
    (accepted : Detail.inferStatementFuel (fuel + 1) inferenceContext statement expectedReturn initial = .ok result)
    (formation : ProgramSignatureFormationValidated inferenceContext.signatures)
    (functions : ∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function (Ty.productMany candidate.parameterTypes) (Ty.productMany candidate.returnTypes))
    (parameters : SignatureParametersWellFormed inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (signaturesEq : semanticContext.signatures = inferenceContext.signatures)
    (parametersEq : semanticContext.typeParameters = inferenceContext.typeParameters)
    (declarationEq : semanticContext.currentDeclaration = some inferenceContext.scope.genericOwner)
    (invariant : RecursiveStatementInvariant wholeContext expectedReturn finalized initial semanticContext)
    (contextAt : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution)
    (initializerSound : ∀ {resolvedType : Ty} {inferred : InferredExpression} {initializerState : State},
      Detail.resolveSourceType inferenceContext sourceType = .ok resolvedType →
      Detail.inferExprFuel fuel inferenceContext initializer (some resolvedType) allocated = .ok (inferred, initializerState) →
      ExpressionHasType ((initializerState.toTypedSource roots).applySubstitution finalized.substitution)
        semanticContext inferred.id (finalized.substitution.apply inferred.type)) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType ((result.state.toTypedSource roots).applySubstitution finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution result facts := by
  have allocatedInvariant := invariant.allocateStatementId allocation
  have isolated : ActiveSchemeQuantifierIsolation result.state ∧
      ActiveBinderCaptureOrigins result.state (evidenceState.toTypedSource roots) ∧
      ActiveQuantifiersBelowNext result.state := by
    obtain ⟨resolvedType, inferred, initializerState, locals, valueType, generalized, binding,
      resolution, childSuccess, _localsEq, valueTypeEq, generalizedEq, bindingEq, resultEq, _contains⟩ :=
      inferStatementFuel_success_letAnnotatedInitialized_facts form allocation accepted roots
    have childProperties := Detail.inferExprFuel_inferenceProperties allocatedInvariant.ready formation functions
      (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        exact Detail.resolveSourceType_success_variablesBelow resolution _) childSuccess
    have rawExpected := inferExprFuel_success_expected_type_afterProgress childSuccess
      (State.InferenceProgress.refl childProperties.2.1.solved)
    have annotationValueEq : valueType = initializerState.resolve resolvedType := valueTypeEq.trans rawExpected
    obtain ⟨typeWellFormed, _closedScheme, _closedRequirements, _generalizes⟩ :=
      resolvedAnnotationBinderFacts_afterSubstitution
        (target := semanticContext) (outer := finalized.substitution)
        resolution annotationValueEq generalizedEq bindingEq parameters signaturesEq parametersEq declarationEq
    have resolvedByState : initializerState.resolve resolvedType = resolvedType := by
      simpa [State.resolve, InferState.resolve] using
        Detail.resolveSourceType_success_apply_eq_self initializerState.inference.substitution resolution
    have valueClosed : valueType.freeVariables = [] := by
      rw [annotationValueEq, resolvedByState]
      exact StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil typeWellFormed
    have schemeEq : generalized.scheme = .mono valueType := by
      rw [generalizedEq]
      exact (generalizeValue_closed_facts initializerState locals allocated.nextRequirement valueType semanticContext valueClosed).1
    have requirementsEq : generalized.requirements = [] := by
      rw [generalizedEq]
      exact (generalizeValue_closed_facts initializerState locals allocated.nextRequirement valueType semanticContext valueClosed).2.1
    have bindersEq : initializerState.localBinders = allocated.localBinders := by
      simpa [State.lexicalScope] using congrArg LexicalScope.binders
        (Detail.inferExprFuel_success_lexicalScope_eq childSuccess)
    have childIsolated := activeSchemeQuantifierIsolation_transport allocatedInvariant.schemeIsolation bindersEq
    have bindingIsolated : ActiveSchemeQuantifierIsolation binding.2 := by
      rw [← bindingEq, schemeEq, requirementsEq]
      exact activeSchemeQuantifierIsolation_allocateMonoBinder (initializerState.withLocals locals) name.value valueType
        (some name.span) (activeSchemeQuantifierIsolation_transport childIsolated rfl)
        (by intro metavariable member; simp [valueClosed] at member)
    have bindingOperational : ActualStateInvariant binding.2 (evidenceState.toTypedSource roots) := by
      rw [← bindingEq, schemeEq, requirementsEq]
      exact ((((operational.allocateStatementId allocation).ofExpression childSuccess
        childProperties.1.next_le).withLocals locals).allocateMonoBinder name.value valueType (some name.span) false)
    rw [resultEq]
    exact ⟨activeSchemeQuantifierIsolation_transport bindingIsolated rfl,
      bindingOperational.origins.congr_localBinders rfl,
      activeQuantifiersBelowNext_transport bindingOperational.quantifiersBelow rfl (Nat.le_refl _)⟩
  obtain ⟨finalContext, facts, finalInvariant, typed, matching⟩ :=
    invariant.close_statement_branch accepted formation functions
      (inferStatementFuel_preserves_localBindersBelowNextLocal invariant.bindersBelow accepted)
      extension isolated.1
      (SourceInferenceStatementsSoundness.inferStatementFuel_success_letAnnotatedInitialized_sound_local form allocation accepted formation functions parameters
        signaturesEq parametersEq declarationEq invariant.ready invariant.active invariant.bindersBelow
        invariant.nodesBelow extension roots initializerSound)
  exact ⟨finalContext, facts, finalInvariant, contextAt.of_statement typed,
    operational.ofStatementWithScope accepted isolated.2.1 isolated.2.2, typed, matching⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedLetCoverage
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem localSchemeTemplateOwner_binder_of_let
    {source : TypedSource} {id : StatementId} {node : StatementNode}
    {binder : TypedBinder} {initializer : ExpressionId} {owner : LocalSchemeTemplateOwner}
    (closed : OccurrenceGraphClosed source)
    (contains : ContainsStatement source id node)
    (form : node.form = .letDecl binder (some initializer))
    (ownerContains : ContainsLocalSchemeTemplate source owner)
    (initializerEq : owner.initializer = .expression initializer) : owner.binder = binder := by
  have edge : DirectChild source (.statement id) (.expression initializer) :=
    directChild_statement_reference contains (by simp [form, StatementForm.references])
  obtain ⟨ownerNode, ownerContains, bindingMem, ownerEdge⟩ :=
    InitializedLetBinding.owningStatement (owner.binding_mem ownerContains)
  have ownerEdge' : DirectChild source (.statement ownerNode.id) (.expression initializer) := by
    simpa only [initializerEq] using ownerEdge
  have parentEq : ownerNode.id = id := by
    have nodesEq := closed.childHasUniqueParent ownerEdge' edge
    cases nodesEq
    rfl
  have nodeEq : ownerNode = node := by
    have ownerLookup := lookupStatement?_complete closed.wellFormed.nodeOccurrencesUnique ownerContains
    have parentLookup := lookupStatement?_complete closed.wellFormed.nodeOccurrencesUnique contains
    rw [parentEq, parentLookup] at ownerLookup
    exact Option.some.inj ownerLookup.symm
  subst ownerNode
  have bindingEq : ({binder := owner.binder, initializer := owner.initializer} : InitializedLetBinding) =
      {binder, initializer := .expression initializer} := by
    simpa only [form, statementInitializedLetBindings, List.mem_singleton] using bindingMem
  exact congrArg InitializedLetBinding.binder bindingEq

theorem templateScopeCovered_letInitializer
    {source : TypedSource} {context : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {binder : TypedBinder} {initializer : ExpressionId}
    (closed : OccurrenceGraphClosed source)
    (contains : ContainsStatement source id node)
    (form : node.form = .letDecl binder (some initializer))
    (covered : TemplateScopeCovered source context (.statement id)) :
    TemplateScopeCovered source (localSchemeInitializerContext context binder) (.expression initializer) := by
  apply TemplateScopeCovered.localSchemeInitializer_of_newRoots covered closed.childHasUniqueParent
    (directChild_statement_reference contains (by simp [form, StatementForm.references]))
  intro owner ownerContains initializerEq
  have binderEq := localSchemeTemplateOwner_binder_of_let closed contains form ownerContains initializerEq
  simpa only [binderEq] using owner.requirement_mem ownerContains

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedAnnotatedLetBranches
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

theorem actualInferStatementFuelRootedSoundness_letAnnotatedUninitialized {fuel : Nat}
    :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {name : Syntax.Identifier} {sourceType : Syntax.TypeExpr}
    {initial : State}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    statement.value = .letDecl name (some sourceType) none →
    Detail.inferStatementFuel (fuel + 1) inferenceContext statement expectedReturn
      initial = .ok result →
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
    finalized.substitution.SemanticallyExtends
      result.state.inference.substitution →
    SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) semanticSource (.statement result.id) →
    RawSubtreePreserved (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id) →
    result.state.integerPatterns ⊆ evidenceState.integerPatterns →
    result.state.integerLiterals ⊆ evidenceState.integerLiterals →
    result.state.requirements ⊆ evidenceState.requirements →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.statement result.id) →
    ActualContext.Covers finalized frames (.statement result.id) →
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statement name sourceType  initial result
    evidenceState roots finalized semanticSource frames semanticContext statementEq success resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational
    returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
  generalize allocation : initial.allocateStatementId = allocatedPair
  obtain ⟨id, allocated⟩ := allocatedPair
  have semanticSignatures : semanticContext.signatures = inferenceContext.signatures :=
    (RecursiveExpressionInvariant.ofStatement invariant).signatures_eq_whole.trans signaturesEq.symm
  have semanticParameters : semanticContext.typeParameters = inferenceContext.typeParameters :=
    invariant.typeParametersEq.trans parametersEq.symm
  have semanticOwner : semanticContext.currentDeclaration = some inferenceContext.scope.genericOwner := by
    rw [ownerEq]
    exact invariant.declarationEq
  exact actual_letAnnotatedUninitialized statementEq allocation success formation functions parameters
    semanticSignatures semanticParameters semanticOwner invariant actual operational extension

theorem actualInferStatementFuelRootedSoundness_letAnnotatedInitialized {fuel : Nat}
    (expressionSound : ActualInferExprFuelRootedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {name : Syntax.Identifier} {sourceType : Syntax.TypeExpr}
    {initializer : Syntax.Expr} {initial : State}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    statement.value = .letDecl name (some sourceType) (some initializer) →
    Detail.inferStatementFuel (fuel + 1) inferenceContext statement expectedReturn
      initial = .ok result →
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
    finalized.substitution.SemanticallyExtends
      result.state.inference.substitution →
    SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) semanticSource (.statement result.id) →
    RawSubtreePreserved (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id) →
    result.state.integerPatterns ⊆ evidenceState.integerPatterns →
    result.state.integerLiterals ⊆ evidenceState.integerLiterals →
    result.state.requirements ⊆ evidenceState.requirements →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.statement result.id) →
    ActualContext.Covers finalized frames (.statement result.id) →
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statement name sourceType initializer initial result
    evidenceState roots finalized semanticSource frames semanticContext statementEq success resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational
    returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
  generalize allocation : initial.allocateStatementId = allocatedPair
  obtain ⟨id, allocated⟩ := allocatedPair
  have semanticSignatures : semanticContext.signatures = inferenceContext.signatures :=
    (RecursiveExpressionInvariant.ofStatement invariant).signatures_eq_whole.trans signaturesEq.symm
  have semanticParameters : semanticContext.typeParameters = inferenceContext.typeParameters :=
    invariant.typeParametersEq.trans parametersEq.symm
  have semanticOwner : semanticContext.currentDeclaration = some inferenceContext.scope.genericOwner := by
    rw [ownerEq]
    exact invariant.declarationEq
  apply actual_letAnnotatedInitialized statementEq allocation success formation functions parameters
    semanticSignatures semanticParameters semanticOwner invariant actual operational extension
  intro resolvedType inferred initializerState resolution childSuccess
  obtain ⟨actualType, actualInferred, actualState, locals, valueType, generalized, binding,
    actualResolution, actualChild, _localsEq, valueEq, generalizedEq, bindingEq, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_letAnnotatedInitialized_facts statementEq allocation success roots
  rw [resolution] at actualResolution
  cases Except.ok.inj actualResolution
  rw [childSuccess] at actualChild
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualChild).symm
  obtain ⟨provenanceType, provenanceInferred, provenanceState, provenanceResolution, provenanceSuccess, provenance⟩ :=
    inferStatementFuel_success_letAnnotatedInitialized_child_provenance statementEq allocation success
      invariant.nodesBelow roots
  rw [resolution] at provenanceResolution
  cases Except.ok.inj provenanceResolution
  rw [childSuccess] at provenanceSuccess
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj provenanceSuccess).symm
  have allocatedInvariant := invariant.allocateStatementId allocation
  have expectedBelow : ∀ type ∈ (some resolvedType : Option Ty), type.VariablesBelow allocated.inference.next := by
    intro type member
    cases Option.mem_def.mp member
    exact Detail.resolveSourceType_success_variablesBelow resolution _
  have childProperties := Detail.inferExprFuel_inferenceProperties allocatedInvariant.ready formation functions
    expectedBelow childSuccess
  have rawExpected := inferExprFuel_success_expected_type_afterProgress childSuccess
    (State.InferenceProgress.refl childProperties.2.1.solved)
  have annotationValueEq : valueType = initializerState.resolve resolvedType := valueEq.trans rawExpected
  obtain ⟨typeWellFormed, schemeEq, requirementsEq, _generalizes⟩ :=
    resolvedAnnotationBinderFacts_afterSubstitution (outer := finalized.substitution)
      resolution annotationValueEq generalizedEq bindingEq parameters semanticSignatures semanticParameters semanticOwner
  have childExpectedAdmissible : ∀ type ∈ (some resolvedType : Option Ty),
      TypeAdmissible semanticContext (finalized.substitution.apply type) := by
    intro type member
    cases Option.mem_def.mp member
    rw [Detail.resolveSourceType_success_apply_eq_self finalized.substitution resolution]
    exact TypeAdmissible.ofWellFormed typeWellFormed
  have finalContains := (raw.finalized resources).containsStatement containsRaw
  have initializerContextEq : localSchemeInitializerContext semanticContext
      (binding.1.applySubstitution finalized.substitution) = semanticContext := by
    rw [localSchemeInitializerContext_eq_withTypeVariables _ _ requirementsEq]
    simp only [schemeEq, Scheme.mono, Context.withTypeVariables, List.append_nil]
  have childCovered : TemplateScopeCovered finalized.typedSource semanticContext (.expression inferred.id) := by
    rw [← initializerContextEq]
    exact templateScopeCovered_letInitializer resources.graph_closed finalContains rfl covered
  have childActualCovered : ActualContext.Covers finalized frames (.expression inferred.id) :=
    actualCovered.statement_reference finalContains (by simp [StatementNode.applySubstitution,
      StatementForm.applySubstitution, StatementForm.references])
  have edge : DirectChild (result.state.toTypedSource roots) (.statement result.id) (.expression inferred.id) :=
    directChild_statement_reference containsRaw (by simp [StatementForm.references])
  have childRaw := (raw.child edge).monoBefore provenance.sourceExtension
  have childExtension : finalized.substitution.SemanticallyExtends initializerState.inference.substitution := by
    have substitutionEq : result.state.inference.substitution = initializerState.inference.substitution := by
      simp [resultEq, ← bindingEq, State.recordNode, State.allocateBinder, State.withLocals]
    rw [← substitutionEq]
    exact extension
  have childLiterals : initializerState.integerLiterals ⊆ evidenceState.integerLiterals := by
    simpa [resultEq, ← bindingEq, State.recordNode, State.allocateBinder, State.withLocals] using literals
  exact expressionSound childSuccess resources interfaces childExtension signaturesEq ownerEq parametersEq assumptionsEq
    formation functions catalog parameters (RecursiveExpressionInvariant.ofStatement allocatedInvariant) actual
    (operational.allocateStatementId allocation) expectedBelow childExpectedAdmissible
    (SubtreePreserved.ofTypingSourceExtends ⟨rfl, ⟨[], by simp⟩⟩) childRaw
    (provenance.integerPatternsSubset.trans patterns) childLiterals (provenance.requirementsSubset.trans requirements)
    childCovered childActualCovered

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedMonomorphicLet
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

theorem ActualStateInvariant.monomorphicBinders {state : State} {source : TypedSource}
    (invariant : ActualStateInvariant state source) :
    ∀ binder ∈ state.localBinders, binder.scheme.quantified = [] := by
  intro binder member
  rcases invariant.origins.origin binder member with mono | retained
  · exact mono
  · exact invariant.sourceMonomorphic binder retained

theorem monomorphicBinders_isolation {state : State}
    (monomorphic : ∀ binder ∈ state.localBinders, binder.scheme.quantified = []) :
    ActiveSchemeQuantifierIsolation state := by
  intro binder member metavariable quantified
  obtain ⟨owner, ownerMember, ownerQuantified⟩ := List.mem_flatMap.mp quantified
  rw [monomorphic owner ownerMember] at ownerQuantified
  cases ownerQuantified

theorem monomorphicBinders_bound {state : State}
    (monomorphic : ∀ binder ∈ state.localBinders, binder.scheme.quantified = []) :
    ActiveQuantifiersBelowNext state := by
  intro binder member metavariable quantified
  rw [monomorphic binder member] at quantified
  cases quantified

theorem actual_letUnannotatedInitialized
    {fuel : Nat} {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier} {initializer : Syntax.Expr}
    {expectedReturn : Ty} {initial allocated evidenceState : State} {id : StatementId}
    {result : Detail.StatementResult} {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding} {semanticContext : SourceSemantics.Context} {roots : List NodeId}
    (form : statement.value = .letDecl name none (some initializer))
    (allocation : initial.allocateStatementId = (id, allocated))
    (accepted : Detail.inferStatementFuel (fuel + 1) inferenceContext statement expectedReturn initial = .ok result)
    {wholeReturn : Ty}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (formation : ProgramSignatureFormationValidated inferenceContext.signatures)
    (functions : ∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function (Ty.productMany candidate.parameterTypes) (Ty.productMany candidate.returnTypes))
    (invariant : RecursiveStatementInvariant wholeContext expectedReturn finalized initial semanticContext)
    (contextAt : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution)
    (rawResult : RawSubtreePreserved (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id))
    (requirementsSubset : result.state.requirements ⊆ evidenceState.requirements)
    (initializerSound : ∀ {inferred : InferredExpression} {initializerState : State},
      Detail.inferExprFuel fuel inferenceContext initializer none allocated = .ok (inferred, initializerState) →
      ExpressionHasType ((initializerState.toTypedSource roots).applySubstitution finalized.substitution)
        semanticContext inferred.id (finalized.substitution.apply inferred.type)) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType ((result.state.toTypedSource roots).applySubstitution finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution result facts := by
  have initialMonomorphic := operational.monomorphicBinders
  obtain ⟨inferred, initializerState, locals, valueType, generalized, binding,
    childSuccess, localsEq, valueEq, generalizedEq, bindingEq, resultEq, contains⟩ :=
    inferStatementFuel_success_letUnannotatedInitialized_facts form allocation accepted roots
  have retained : ContainsStatement (evidenceState.toTypedSource roots) result.id {
      id := result.id, span := statement.span, type := result.type, form := .letDecl binding.1 (some inferred.id) } := by
    refine ⟨rawResult.nodes _ contains.1 (.inl ?_), contains.2⟩
    rfl
  have rawMono : binding.1.scheme.quantified = [] := operational.sourceMonomorphic _
    (retained.initializedLetBinder_mem (by simp [StatementForm.initializedLetBinders]))
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
  have bindersEq : initializerState.localBinders = initial.localBinders := by
    have childEq := congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq childSuccess)
    have allocatedEq := congrArg (fun state : State => state.localBinders) (congrArg Prod.snd allocation)
    exact childEq.trans allocatedEq.symm
  have resultMonomorphic : ∀ binder ∈ result.state.localBinders, binder.scheme.quantified = [] := by
    intro binder member
    rw [resultEq, ← bindingEq] at member
    change binder ∈ _ :: initializerState.localBinders at member
    rcases List.mem_cons.mp member with rfl | member
    · exact generalizedMono
    · exact initialMonomorphic binder (bindersEq ▸ member)
  have statementSound : ∃ finalContext facts,
      ActiveLocalContextInvariant result.state finalized.substitution finalContext ∧
      StatementHasType ((result.state.toTypedSource roots).applySubstitution finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution result facts := by
    apply inferStatementFuel_success_letUnannotatedInitialized_sound form allocation accepted invariant.active
      invariant.bindersBelow roots
    intro actualInferred actualState actualLocals actualValue actualGeneralized actualBinding actualSuccess
      actualLocalsEq actualValueEq actualGeneralizedEq actualBindingEq
    have same := Except.ok.inj (childSuccess.symm.trans actualSuccess)
    cases same
    have sameLocals : actualLocals = locals := actualLocalsEq.trans localsEq.symm
    cases sameLocals
    have sameValue : actualValue = valueType := actualValueEq.trans valueEq.symm
    cases sameValue
    have sameGeneralized : actualGeneralized = generalized := actualGeneralizedEq.trans generalizedEq.symm
    cases sameGeneralized
    have sameBinding : actualBinding = binding := actualBindingEq.symm.trans bindingEq
    cases sameBinding
    have rawScheme : binding.1.scheme = .mono valueType := by
      rw [← binderEq]
      exact schemeEq
    have rawRequirements : binding.1.schemeRequirements = [] := by
      rw [← binderEq]
      exact requirementsEq
    have contextEq : localSchemeInitializerContext semanticContext
        (binding.1.applySubstitution finalized.substitution) = semanticContext := by
      rw [localSchemeInitializerContext_eq_withTypeVariables _ _ (by simp [rawRequirements])]
      rw [show (binding.1.applySubstitution finalized.substitution).scheme.quantified = [] from rawMono]
      exact Context.withTypeVariables_nil _
    have substitutionEq : result.state.inference.substitution = initializerState.inference.substitution := by
      rw [resultEq, ← bindingEq]
      rfl
    have childExtension : finalized.substitution.SemanticallyExtends initializerState.inference.substitution := by
      rwa [substitutionEq] at extension
    have bodyEq : (binding.1.applySubstitution finalized.substitution).scheme.body =
        finalized.substitution.apply inferred.type := by
      simpa [TypedBinder.applySubstitution, rawScheme, Scheme.apply, Scheme.mono, Substitution.without,
        valueEq, State.resolve, InferState.resolve] using childExtension inferred.type
    obtain ⟨otherInferred, otherState, otherSuccess, provenance⟩ :=
      inferStatementFuel_success_letUnannotatedInitialized_child_provenance form allocation accepted invariant.nodesBelow roots
    have same := Except.ok.inj (childSuccess.symm.trans otherSuccess)
    cases same
    have localsFacts := MonomorphicGeneralization.initializer_locals allocation childSuccess localsEq
      invariant.active.aligned initialMonomorphic childExtension
    have childRequirements : initializerState.requirements ⊆ evidenceState.requirements := by
      have requirementEq : result.state.requirements = initializerState.requirements := by
        rw [resultEq, ← bindingEq]
        rfl
      rwa [requirementEq] at requirementsSubset
    apply unannotatedInitializedLetCertificate_of_finalMonomorphic resources generalizedEq bindingEq
      rawMono localsFacts.1 localsFacts.2 childRequirements childExtension invariant.solvedRequirementsEq
    rw [contextEq, bodyEq]
    exact ExpressionHasType.weakenSource (provenance.sourceExtension.applySubstitution finalized.substitution)
      (initializerSound childSuccess)
  obtain ⟨finalContext, facts, finalInvariant, typed, matching⟩ :=
    invariant.close_statement_branch accepted formation functions
      (inferStatementFuel_preserves_localBindersBelowNextLocal invariant.bindersBelow accepted)
      extension (monomorphicBinders_isolation resultMonomorphic) statementSound
  exact ⟨finalContext, facts, finalInvariant, contextAt.of_statement typed,
    operational.ofStatementWithScope accepted (ActiveBinderCaptureOrigins.of_monomorphic resultMonomorphic)
      (monomorphicBinders_bound resultMonomorphic), typed, matching⟩


end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedMonomorphicForItem
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedForItemDispatch
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferForItemFuelRootedSoundness_zero : ActualInferForItemFuelRootedSoundness 0 := by
  intro wholeContext inferenceContext wholeReturn expectedReturn item initial final inferred evidenceState roots
    finalized semanticSource frames semanticContext control success
  simp [Detail.inferForItemFuel] at success

theorem actualInferForItemFuelRootedSoundness_step {fuel : Nat}
    (expressionSound : ActualInferExprFuelRootedSoundness fuel)
    (placeSound : ActualInferPlaceFuelRootedSoundness fuel) :
    ActualInferForItemFuelRootedSoundness (fuel + 1) := by
  intro wholeContext inferenceContext wholeReturn expectedReturn item initial final inferred evidenceState roots
    finalized semanticSource frames semanticContext control success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements sourceOwner covered bindings actualCovered actualBindings
  cases form : item.value with
  | letDecl name annotation initializer =>
    cases annotation with
    | none =>
      cases initializer with
      | none => simp [Detail.inferForItemFuel, form, bind, Except.bind] at success
      | some initializer =>
        exact actualInferForItemFuelRootedSoundness_letUnannotatedInitialized expressionSound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements sourceOwner covered bindings actualCovered actualBindings
    | some annotation =>
      cases initializer with
      | none =>
        exact actualInferForItemFuelRootedSoundness_letAnnotatedUninitialized form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements sourceOwner covered bindings actualCovered actualBindings
      | some initializer =>
        exact actualInferForItemFuelRootedSoundness_letAnnotatedInitialized expressionSound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements sourceOwner covered bindings actualCovered actualBindings
  | expression expression =>
    exact actualInferForItemFuelRootedSoundness_expression expressionSound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements sourceOwner covered bindings actualCovered actualBindings
  | assignValue target operator value =>
    exact actualInferForItemFuelRootedSoundness_assignValue placeSound expressionSound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements sourceOwner covered bindings actualCovered actualBindings
  | assignBitNot target operator =>
    exact actualInferForItemFuelRootedSoundness_assignBitNot placeSound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements sourceOwner covered bindings actualCovered actualBindings

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedUnannotatedLetBranch
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

theorem actualInferStatementFuelRootedSoundness_letUnannotatedInitialized {fuel : Nat}
    (expressionSound : ActualInferExprFuelRootedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {initializer : Syntax.Expr} {initial : State}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    statement.value = .letDecl name none (some initializer) →
    Detail.inferStatementFuel (fuel + 1) inferenceContext statement expectedReturn
      initial = .ok result →
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
    finalized.substitution.SemanticallyExtends
      result.state.inference.substitution →
    SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) semanticSource (.statement result.id) →
    RawSubtreePreserved (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id) →
    result.state.integerPatterns ⊆ evidenceState.integerPatterns →
    result.state.integerLiterals ⊆ evidenceState.integerLiterals →
    result.state.requirements ⊆ evidenceState.requirements →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.statement result.id) →
    ActualContext.Covers finalized frames (.statement result.id) →
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statement name initializer initial result
    evidenceState roots finalized semanticSource frames semanticContext statementEq success resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational
    returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
  generalize allocation : initial.allocateStatementId = allocatedPair
  obtain ⟨id, allocated⟩ := allocatedPair
  apply actual_letUnannotatedInitialized statementEq allocation success resources formation functions invariant actual operational
    extension raw requirements
  intro inferred initializerState childSuccess
  obtain ⟨actualInferred, actualState, locals, valueType, generalized, binding,
    actualChild, _localsEq, _valueEq, generalizedEq, bindingEq, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_letUnannotatedInitialized_facts statementEq allocation success roots
  rw [childSuccess] at actualChild
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualChild).symm
  obtain ⟨provenanceInferred, provenanceState, provenanceSuccess, provenance⟩ :=
    inferStatementFuel_success_letUnannotatedInitialized_child_provenance statementEq allocation success
      invariant.nodesBelow roots
  rw [childSuccess] at provenanceSuccess
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj provenanceSuccess).symm
  have allocatedInvariant := invariant.allocateStatementId allocation
  have finalContains := (raw.finalized resources).containsStatement containsRaw
  have finalMonomorphic : ExecutableBinderInterfaces.SourceMonomorphic finalized.typedSource := by
    rw [resources.source_eq]
    exact operational.sourceMonomorphic.afterSubstitution
  have binderMono : (binding.1.applySubstitution finalized.substitution).scheme.quantified = [] :=
    finalMonomorphic _ (finalContains.initializedLetBinder_mem (by simp [StatementNode.applySubstitution,
      StatementForm.applySubstitution, StatementForm.initializedLetBinders]))
  have binderEq := congrArg Prod.fst bindingEq
  have rawMono : binding.1.scheme.quantified = [] := binderMono
  have generalizedMono : generalized.scheme.quantified = [] := by
    rw [← binderEq] at rawMono
    exact rawMono
  have requirementsEq : generalized.requirements = [] := by
    rw [generalizedEq]
    apply Detail.generalizeValue_requirements_empty_of_quantified_eq_nil
    rwa [← generalizedEq]
  have rawRequirements : binding.1.schemeRequirements = [] := by
    rw [← binderEq]
    exact requirementsEq
  have initializerContextEq : localSchemeInitializerContext semanticContext
      (binding.1.applySubstitution finalized.substitution) = semanticContext := by
    rw [localSchemeInitializerContext_eq_withTypeVariables _ _ (by simp [rawRequirements]), binderMono]
    exact Context.withTypeVariables_nil _
  have childCovered : TemplateScopeCovered finalized.typedSource semanticContext (.expression inferred.id) := by
    rw [← initializerContextEq]
    exact templateScopeCovered_letInitializer resources.graph_closed finalContains rfl covered
  have childActualCovered : ActualContext.Covers finalized frames (.expression inferred.id) :=
    actualCovered.statement_reference finalContains (by simp [StatementNode.applySubstitution,
      StatementForm.applySubstitution, StatementForm.references])
  have edge : DirectChild (result.state.toTypedSource roots) (.statement result.id) (.expression inferred.id) :=
    directChild_statement_reference containsRaw (by simp [StatementForm.references])
  have childRaw := (raw.child edge).monoBefore provenance.sourceExtension
  have childExtension : finalized.substitution.SemanticallyExtends initializerState.inference.substitution := by
    have substitutionEq : result.state.inference.substitution = initializerState.inference.substitution := by
      simp [resultEq, ← bindingEq, State.recordNode, State.allocateBinder, State.withLocals]
    rw [← substitutionEq]
    exact extension
  have childLiterals : initializerState.integerLiterals ⊆ evidenceState.integerLiterals := by
    simpa [resultEq, ← bindingEq, State.recordNode, State.allocateBinder, State.withLocals] using literals
  exact expressionSound childSuccess resources interfaces childExtension signaturesEq ownerEq parametersEq assumptionsEq
    formation functions catalog parameters (RecursiveExpressionInvariant.ofStatement allocatedInvariant) actual
    (operational.allocateStatementId allocation) (by simp) (by simp)
    (SubtreePreserved.ofTypingSourceExtends ⟨rfl, ⟨[], by simp⟩⟩) childRaw
    (provenance.integerPatternsSubset.trans patterns) childLiterals (provenance.requirementsSubset.trans requirements)
    childCovered childActualCovered

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedStatementDispatch
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

def ActualInferMatchStatementFuelRootedSoundness (fuel : Nat) : Prop :=
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {initial : State}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    (∃ scrutinees arms, statement.value = .matchWith scrutinees arms) →
    Detail.inferStatementFuel fuel inferenceContext statement expectedReturn
      initial = .ok result →
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
    finalized.substitution.SemanticallyExtends
      result.state.inference.substitution →
    SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) semanticSource (.statement result.id) →
    RawSubtreePreserved (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id) →
    result.state.integerPatterns ⊆ evidenceState.integerPatterns →
    result.state.integerLiterals ⊆ evidenceState.integerLiterals →
    result.state.requirements ⊆ evidenceState.requirements →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.statement result.id) →
    ActualContext.Covers finalized frames (.statement result.id) →
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts

theorem actualInferStatementFuelRootedSoundness_zero : ActualInferStatementFuelRootedSoundness 0 := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statement initial result evidenceState roots
    finalized semanticSource frames semanticContext success
  simp only [Detail.inferStatementFuel] at success
  cases success

theorem actualInferStatementFuelRootedSoundness_step {fuel : Nat}
    (expressionSound : ActualInferExprFuelRootedSoundness fuel)
    (placeSound : ActualInferPlaceFuelRootedSoundness fuel)
    (bodySound : ActualInferStatementsFuelRootedSoundness fuel)
    (itemsSound : ActualInferForItemsFuelRootedSoundness fuel)
    (matchSound : ActualInferMatchStatementFuelRootedSoundness (fuel + 1)) :
    ActualInferStatementFuelRootedSoundness (fuel + 1) := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statement initial result evidenceState roots
    finalized semanticSource frames semanticContext success resources interfaces signaturesEq ownerEq parametersEq
    assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension
    semantic raw patterns literals requirements covered actualCovered
  generalize allocation : initial.allocateStatementId = pair
  obtain ⟨id, allocated⟩ := pair
  cases form : statement.value with
  | letDecl name annotation initializer =>
    cases annotation with
    | none =>
      cases initializer with
      | none => simp [Detail.inferStatementFuel, form, bind, Except.bind] at success
      | some initializer =>
        exact actualInferStatementFuelRootedSoundness_letUnannotatedInitialized expressionSound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
    | some annotation =>
      cases initializer with
      | none => exact actualInferStatementFuelRootedSoundness_letAnnotatedUninitialized form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
      | some initializer => exact actualInferStatementFuelRootedSoundness_letAnnotatedInitialized expressionSound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
  | returnStmt value =>
    cases value with
    | none =>
      exact actualInferStatementFuel_returnUnit_atomicBranch form allocation success formation functions
        invariant actual operational extension
    | some value =>
      exact actualInferStatementFuel_returnValue_scopedBranch form allocation success resources interfaces
        signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual
        operational returnAdmissible extension raw patterns literals requirements covered actualCovered expressionSound
  | expression expression trailing =>
    exact actualInferStatementFuel_expression_scopedBranch form allocation success resources interfaces
      signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual
      operational returnAdmissible extension raw patterns literals requirements covered actualCovered expressionSound
  | assignValue target operator value =>
    exact actualInferStatementFuelRootedSoundness_assignValue placeSound expressionSound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
  | assignBitNot target operator =>
    exact actualInferStatementFuelRootedSoundness_assignBitNot placeSound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
  | matchWith scrutinees arms => exact matchSound ⟨scrutinees, arms, form⟩ success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
  | forLoop span initializer condition post body =>
    exact actualInferStatementFuelRootedSoundness_forLoop itemsSound expressionSound bodySound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
  | whileLoop condition body =>
    exact actualInferStatementFuelRootedSoundness_whileLoop expressionSound bodySound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
  | ifThen condition thenBody elseBody =>
    cases elseBody with
    | none => exact actualInferStatementFuelRootedSoundness_ifWithoutElse expressionSound bodySound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
    | some elseBody => exact actualInferStatementFuelRootedSoundness_ifWithElse expressionSound bodySound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
  | block body => exact actualInferStatementFuelRootedSoundness_block bodySound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
  | breakStmt =>
    exact actualInferStatementFuel_break_atomicBranch form allocation success formation functions
      invariant actual operational extension
  | continueStmt =>
    exact actualInferStatementFuel_continue_atomicBranch form allocation success formation functions
      invariant actual operational extension
  | assembly body => simp [Detail.inferStatementFuel, form] at success
  | error => simp [Detail.inferStatementFuel, form] at success

end Solcore.SourceSemantics.SourceInferenceSoundness
end
