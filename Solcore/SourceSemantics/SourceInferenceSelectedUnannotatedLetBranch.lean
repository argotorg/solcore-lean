import Solcore.SourceSemantics.SourceInferenceSelectedMonomorphicLet
import Solcore.SourceSemantics.SourceInferenceSelectedLetCoverage

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
