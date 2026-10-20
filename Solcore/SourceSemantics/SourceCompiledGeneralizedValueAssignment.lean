import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedAssignedValue
import Solcore.SourceSemantics.SourceCompiledGeneralizedStatementContracts
import Solcore.SourceSemantics.SourceInferenceGeneralizedStatementRecording

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness

theorem statement_assignValue
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (placeSound : PlaceRootedSoundness selected childFuel)
    (expressionSound : ExpressionRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {targetExpression value : Syntax.Expr} {operator : Syntax.Located Syntax.ValueAssignOp}
    {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : statement.value = .assignValue targetExpression operator value)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  obtain ⟨assignment, inferred, assignmentState, assignmentAccepted, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_assignValue_facts form rfl boundary.accepted (bodyRoots selected)
  have assignedToParent : TypingSourceExtends (assignmentState.toTypedSource (bodyRoots selected))
      (result.state.toTypedSource (bodyRoots selected)) := by
    rw [resultEq]
    exact ⟨rfl, State.recordNode_nodesPrefix _ _⟩
  have assignedExtension : selected.body.finalized.substitution.SemanticallyExtends assignmentState.inference.substitution := by
    simpa only [resultEq, State.recordNode] using boundary.extension
  have finalized := boundary.rawSubtree.finalized selected.body.resources
  have reference : ∀ key, .expression key ∈ assignment.references →
      (.expression key : NodeId) ∈ (StatementForm.assignValue assignment operator.value inferred.id).references := by
    intro key member
    simp only [StatementForm.references]
    exact List.mem_append_left _ member
  have keysCovered : ∀ key, .expression key ∈ assignment.references →
      TemplateScopeCovered selected.body.finalized.typedSource target (.expression key) := by
    intro key member
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      boundary.covered selected.body.resources.graph_closed (finalized.containsStatement containsRaw)
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, statementInitializedLetBindings]
    · simpa [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references,
        AssignmentResolution.references, AssignmentResolution.applySubstitution,
        PlaceResolution.applySubstitution, PlaceResolution.references] using reference key member
  have valueCovered : TemplateScopeCovered selected.body.finalized.typedSource target (.expression inferred.id) := by
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      boundary.covered selected.body.resources.graph_closed (finalized.containsStatement containsRaw)
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, statementInitializedLetBindings]
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references]
  obtain ⟨assignmentTyped, assignmentOperational⟩ := assignedValue_of_actual_children checked placeSound expressionSound ({
    accepted := assignmentAccepted
    interfaces := boundary.interfaces
    extension := assignedExtension
    scope := boundary.scope
    invariant := RecursiveExpressionInvariant.ofStatement (boundary.invariant.allocateStatementId rfl)
    actual := boundary.actual
    operational := boundary.operational.allocateStatementId
    rawKeys := fun key member =>
      (boundary.rawSubtree.child (directChild_statement_reference containsRaw (reference key member))).monoBefore assignedToParent
    rawValue := (boundary.rawSubtree.child
      (directChild_statement_reference containsRaw (by simp [StatementForm.references]))).monoBefore assignedToParent
    integerPatterns := by simpa only [resultEq, State.recordNode] using boundary.integerPatterns
    integerLiterals := by simpa only [resultEq, State.recordNode] using boundary.integerLiterals
    requirements := by simpa only [resultEq, State.recordNode] using boundary.requirements
    keysCovered := keysCovered
    valueCovered := valueCovered
    keysActualCovered := fun key member =>
      boundary.actualCovered.preserved_statement_reference containsRaw finalized (reference key member)
    valueActualCovered := boundary.actualCovered.preserved_statement_reference containsRaw finalized
      (by simp [StatementForm.references]) } :
    AssignedValueBoundary selected childFuel inferenceContext targetExpression operator.value value
      initial.allocateStatementId.2 assignment inferred assignmentState frames target)
  have typing : StatementHasType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth }
      target result.id target {
        type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } := by
    exact .assignValue (finalized.containsStatement containsRaw) rfl assignmentTyped
      (by simp [StatementNode.applySubstitution, resultEq])
  have operational : GeneralizedActualStateInvariant result.state (evidenceSource selected) := by
    rw [resultEq]
    exact assignmentOperational.recordStatement _ rfl
  have active : ActiveLocalContextInvariant result.state selected.body.finalized.substitution target := by
    rw [resultEq]
    exact ((boundary.invariant.active.allocateStatementId rfl).inferAssignedValueFuel assignmentAccepted).recordNode _
  have bindersEq : result.state.localBinders = initial.localBinders := by
    have assignedBinders := congrArg LexicalScope.binders (Detail.inferAssignedValueFuel_success_lexicalScope_eq assignmentAccepted)
    simpa only [resultEq, State.recordNode, State.lexicalScope] using assignedBinders
  have invariant := boundary.invariant.of_retained_statement_typing boundary.accepted
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked) active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension (activeSchemeQuantifierIsolation_transport boundary.invariant.schemeIsolation bindersEq) typing
  refine ⟨target, _, invariant, boundary.actual, operational, typing, ?_⟩
  rw [resultEq]
  exact StatementResultMatchesFactsAfterSubstitution.ordinaryUnit _ _ _

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
