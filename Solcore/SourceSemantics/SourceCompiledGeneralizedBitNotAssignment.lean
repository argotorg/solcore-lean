import Solcore.SourceSemantics.SourceCompiledProvenanceStatementContracts
import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedStatementContracts
import Solcore.SourceSemantics.SourceCompiledGeneralizedPlaceContracts
import Solcore.SourceSemantics.SourceInferenceGeneralizedStatementRecording

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution SourceInferenceStatementsSoundness

theorem statement_assignBitNot_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {provenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed provenance)
    (placeSound : PlaceRootedSoundnessFor provenance selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {targetExpression : Syntax.Expr} {operatorSpan : Syntax.SourceSpan} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : provenance (.statement (childFuel + 1) inferenceContext statement expectedReturn initial result))
    (form : statement.value = .assignBitNot targetExpression operatorSpan)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  have resources := selected.body.resources
  have formation := boundary.scope.formation checked
  have canonical := boundary.scope.functionsCanonical checked
  have allocatedInvariant := boundary.invariant.allocateStatementId rfl
  obtain ⟨place, placeState, unified, placeAccepted, unifiedAccepted, resolvedWord, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_assignBitNot_facts form rfl boundary.accepted (bodyRoots selected)
  have placeToParent : TypingSourceExtends (placeState.toTypedSource (bodyRoots selected))
      (result.state.toTypedSource (bodyRoots selected)) := by
    constructor
    · change result.state.owner = placeState.owner
      rw [resultEq]
      exact congrArg State.Header.owner (Detail.unify_state_header unifiedAccepted)
    · change placeState.nodes <+: result.state.nodes
      rw [resultEq]
      change placeState.nodes <+: (unified.recordNode _).nodes
      rw [← (Detail.unify_occurrenceState_eq unifiedAccepted).1]
      exact State.recordNode_nodesPrefix _ _
  have properties := Detail.inferPlaceFuel_inferenceProperties allocatedInvariant.ready formation canonical placeAccepted
  have unifiedExtension : selected.body.finalized.substitution.SemanticallyExtends unified.inference.substitution := by
    simpa only [resultEq, State.recordNode] using boundary.extension
  have placeExtension := unifiedExtension.trans
    (Detail.unify_inferenceProgress properties.2.1.solved properties.2.2
      (Ty.variablesBelow_constructor _ _) unifiedAccepted).substitution_extends
  have finalized := boundary.rawSubtree.finalized resources
  have reference : ∀ key, .expression key ∈ place.references →
      (.expression key : NodeId) ∈ (StatementForm.assignBitNot
        { target := { place with type := unified.resolve place.type }}).references := by
    intro key member
    simpa [StatementForm.references, AssignmentResolution.references, PlaceResolution.references] using member
  have keyCoverage : ∀ key, .expression key ∈ place.references →
      TemplateScopeCovered selected.body.finalized.typedSource target (.expression key) := by
    intro key member
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      boundary.covered resources.graph_closed (finalized.containsStatement containsRaw)
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, statementInitializedLetBindings]
    · simpa [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references,
        AssignmentResolution.references, AssignmentResolution.applySubstitution, PlaceResolution.applySubstitution,
        PlaceResolution.references] using reference key member
  obtain ⟨placeTyping, placeOperational, placeSafe⟩ := placeSound (descend here (ChildStep.statement_bitnot boundary.accepted form rfl placeAccepted)) ({
    accepted := placeAccepted
    interfaces := boundary.interfaces
    extension := placeExtension
    scope := boundary.scope
    invariant := RecursiveExpressionInvariant.ofStatement allocatedInvariant
    actual := boundary.actual
    operational := boundary.operational.allocateStatementId
    rawKeys := fun key member =>
      (boundary.rawSubtree.child (directChild_statement_reference containsRaw (reference key member))).monoBefore placeToParent
    integerPatterns := by
      simpa only [resultEq, State.recordNode, Detail.unify_integerPatterns unifiedAccepted] using boundary.integerPatterns
    integerLiterals := by
      simpa only [resultEq, State.recordNode, Detail.unify_integerLiterals unifiedAccepted] using boundary.integerLiterals
    requirements := by
      simpa only [resultEq, State.recordNode, Detail.unify_requirements_eq unifiedAccepted] using boundary.requirements
    covered := keyCoverage
    actualCovered := fun key member =>
      boundary.actualCovered.preserved_statement_reference containsRaw finalized (reference key member) } :
    PlaceBoundary selected childFuel inferenceContext targetExpression initial.allocateStatementId.2
      place placeState frames target)
  have unifiedOperational := placeOperational.unify properties.2.1 properties.2.2
    (Ty.variablesBelow_constructor _ _) placeSafe
    (fun binder _ => ProtectedVariables.safe_closed binder.scheme.quantified placeState
      (Ty.variablesBelow_constructor 0 _)) unifiedAccepted
  have operational : GeneralizedActualStateInvariant result.state (evidenceSource selected) := by
    rw [resultEq]
    exact unifiedOperational.recordStatement _ rfl
  have active : ActiveLocalContextInvariant result.state selected.body.finalized.substitution target := by
    rw [resultEq]
    exact ((allocatedInvariant.active.inferPlaceFuel placeAccepted).unify unifiedAccepted).recordNode _
  have resolvedFinal : selected.body.finalized.substitution.apply (unified.resolve place.type) =
      selected.body.finalized.substitution.apply place.type := by
    simpa [State.resolve, InferState.resolve] using unifiedExtension place.type
  have placeWord : selected.body.finalized.substitution.apply place.type = .word := by
    rw [← resolvedFinal, resolvedWord]
    rfl
  have storedPlaceEq :
      ({ place with type := unified.resolve place.type } : PlaceResolution).applySubstitution
        selected.body.finalized.substitution = place.applySubstitution selected.body.finalized.substitution := by
    cases place
    simp [PlaceResolution.applySubstitution, resolvedFinal]
  have assignmentTyping : SourceBitNotAssignmentValid selected.body.finalized.typedSource target
      (({ target := { place with type := unified.resolve place.type } } : AssignmentResolution).applySubstitution
        selected.body.finalized.substitution) := by
    apply SourceBitNotAssignmentValid.intro ?_ rfl
    change SourcePlaceHasType _ _
      (({ place with type := unified.resolve place.type } : PlaceResolution).applySubstitution
        selected.body.finalized.substitution) .word
    rw [storedPlaceEq, ← placeWord]
    exact placeTyping
  have typing : StatementHasType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth }
      target result.id target {
        type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } := by
    exact .assignBitNot (finalized.containsStatement containsRaw) rfl assignmentTyping
      (by simp [StatementNode.applySubstitution, resultEq])
  have bindersEq : result.state.localBinders = initial.localBinders := by
    have placeBinders := congrArg LexicalScope.binders (Detail.inferPlaceFuel_success_lexicalScope_eq placeAccepted)
    have unifiedBinders := congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope unifiedAccepted)
    simpa only [resultEq, State.recordNode, State.lexicalScope] using unifiedBinders.trans placeBinders
  have invariant := boundary.invariant.of_retained_statement_typing boundary.accepted formation canonical active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension (activeSchemeQuantifierIsolation_transport boundary.invariant.schemeIsolation bindersEq) typing
  refine ⟨target, _, invariant, boundary.actual, operational, typing, ?_⟩
  rw [resultEq]
  exact StatementResultMatchesFactsAfterSubstitution.ordinaryUnit _ _ _

theorem statement_assignBitNot
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (placeSound : PlaceRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {targetExpression : Syntax.Expr} {operatorSpan : Syntax.SourceSpan} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : statement.value = .assignBitNot targetExpression operatorSpan)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  exact statement_assignBitNot_for (provenance := fun _ => True) checked true_childClosed
    (fun _ boundary => placeSound boundary) trivial form boundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
