import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedStatementContracts
import Solcore.SourceSemantics.SourceInferenceGeneralizedStatementRecording
import Solcore.SourceSemantics.SourceInferenceSelectedStatementReferences

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization
open SourceInferenceStatementsSoundness

theorem statement_expression
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {expression : Syntax.Expr} {trailingSemicolon : Bool} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : statement.value = .expression expression trailingSemicolon)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  have resources := selected.body.resources
  generalize allocationEq : initial.allocateStatementId = allocatedPair
  rcases allocatedPair with ⟨id, allocated⟩
  obtain ⟨inferred, childState, childSuccess, provenance⟩ :=
    inferStatementFuel_success_expression_child_provenance form allocationEq
      boundary.accepted boundary.invariant.nodesBelow (bodyRoots selected)
  obtain ⟨actualInferred, actualState, actualSuccess, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_expression_facts form allocationEq boundary.accepted (bodyRoots selected)
  rw [childSuccess] at actualSuccess
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualSuccess).symm
  have childSubstitutionEq : childState.inference.substitution = result.state.inference.substitution := by
    simp [resultEq, State.recordNode]
  have childEdge : DirectChild (result.state.toTypedSource (bodyRoots selected))
      (.statement result.id) (.expression inferred.id) :=
    directChild_statement_reference containsRaw (by simp [StatementForm.references])
  have containsFinal := (boundary.rawSubtree.finalized resources).containsStatement containsRaw
  have childCovered : TemplateScopeCovered selected.body.finalized.typedSource target
      (.expression inferred.id) := by
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      boundary.covered resources.graph_closed containsFinal
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, statementInitializedLetBindings]
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references]
  have childActualCovered : ActualContext.Covers selected.body.finalized frames (.expression inferred.id) :=
    boundary.actualCovered.statement_reference containsFinal (by
      simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references])
  have allocatedInvariant := RecursiveExpressionInvariant.ofStatement
    (boundary.invariant.allocateStatementId allocationEq)
  have allocatedOperational : GeneralizedActualStateInvariant allocated (evidenceSource selected) := by
    rw [← show initial.allocateStatementId.2 = allocated from congrArg Prod.snd allocationEq]
    exact boundary.operational.allocateStatementId
  have childExtension : selected.body.finalized.substitution.SemanticallyExtends
      childState.inference.substitution := childSubstitutionEq ▸ boundary.extension
  have childLiterals : childState.integerLiterals ⊆ selected.body.returned.integerLiterals := by
    simpa [resultEq, State.recordNode] using boundary.integerLiterals
  have typed := recursive ({
    accepted := childSuccess
    interfaces := boundary.interfaces
    extension := childExtension
    scope := boundary.scope
    invariant := allocatedInvariant
    actual := boundary.actual
    operational := allocatedOperational
    expectedBelow := by simp
    expectedAdmissible := by simp
    expectedSafe := by simp
    integerPatterns := List.Subset.trans provenance.integerPatternsSubset boundary.integerPatterns
    integerLiterals := childLiterals
    requirements := List.Subset.trans provenance.requirementsSubset boundary.requirements
    covered := childCovered
    actualCovered := childActualCovered
    rawSubtree := (boundary.rawSubtree.child childEdge).monoBefore provenance.sourceExtension } :
    RootedExpressionBoundary selected childFuel inferenceContext expression none
      allocated inferred childState frames target)
  have childActive := allocatedInvariant.active.inferExprFuel childSuccess
  have childOperational := allocatedOperational.ofExpression allocatedInvariant.ready
    (boundary.scope.catalog checked) (boundary.scope.formation checked)
    (boundary.scope.functionsCanonical checked) (by simp) (by simp) childSuccess
  have bindersEq : result.state.localBinders = initial.localBinders := by
    have childEq := congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq childSuccess)
    have allocationScope := congrArg LexicalScope.binders (Detail.allocateStatementId_success_lexicalScope allocationEq)
    simpa only [resultEq, State.recordNode, State.lexicalScope] using childEq.trans allocationScope
  have typedResult : ∃ facts,
      ActiveLocalContextInvariant result.state selected.body.finalized.substitution target ∧
      GeneralizedActualStateInvariant result.state (evidenceSource selected) ∧
      StatementHasType selected.body.finalized.typedSource
        { returnType := selected.body.finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth } target result.id target facts ∧
      StatementResultMatchesFactsAfterSubstitution selected.body.finalized.substitution result facts := by
    subst result
    cases trailingSemicolon with
    | false =>
        refine ⟨{
          type := selected.body.finalized.substitution.apply inferred.type
          hasValue := true
          sawReturn := false
          control := .ordinary (selected.body.finalized.substitution.apply inferred.type) },
          childActive.recordNode _, childOperational.recordStatement _ rfl, ?_, ?_⟩
        · exact .expressionValue containsFinal rfl typed rfl
        · constructor <;> rfl
    | true =>
        refine ⟨{ type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit },
          childActive.recordNode _, childOperational.recordStatement _ rfl, ?_, ?_⟩
        · exact .expressionDiscard containsFinal rfl typed rfl
        · constructor <;> rfl
  obtain ⟨facts, active, operational, typing, agreement⟩ := typedResult
  have finalInvariant := boundary.invariant.of_retained_statement_typing boundary.accepted
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked) active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension (activeSchemeQuantifierIsolation_transport boundary.invariant.schemeIsolation bindersEq)
    typing
  exact ⟨target, facts, finalInvariant, boundary.actual, operational, typing, agreement⟩

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
