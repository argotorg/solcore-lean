import Solcore.SourceSemantics.SourceInferenceSelectedStatementReferences
import Solcore.SourceSemantics.SourceInferenceSelectedLetState

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
