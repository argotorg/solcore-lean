import Solcore.SourceSemantics.SourceInferenceSelectedAnnotatedLetSoundness
import Solcore.SourceSemantics.SourceInferenceSelectedLetCoverage

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
