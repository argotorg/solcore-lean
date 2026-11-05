import Solcore.SourceSemantics.Internal.Compiled.BodySelection
import Solcore.SourceSemantics.Internal.Compiled.Contracts
import Solcore.SourceSemantics.SourceInferenceGeneralizedStatementRecording
import Solcore.SourceSemantics.Internal.Compiled.OperationalState
import Solcore.SourceSemantics.Internal.Compiled.Expressions
import Solcore.SourceSemantics.SourceInferenceAssignedValueActualPrefix
import Solcore.SourceSemantics.SourceInferenceSelectedAssignmentChildren
import Solcore.SourceSemantics.SourceInferenceSelectedStatementReferences
import Solcore.SourceSemantics.SourceInferencePrivacyScopeRetention
import Solcore.SourceSemantics.Internal.Compiled.LifetimeSeeds

/-!
# Typing of generalized statements

Declarations, assignments, blocks, conditionals, returns and expression statements. Each passes only
its actual head and tail calls to its semantic consumers.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedAnnotatedDeclaration
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

theorem statement_annotatedUninitialized
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {name : Syntax.Identifier} {sourceType : Syntax.TypeExpr} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : statement.value = .letDecl name (some sourceType) none)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  have parameters := boundary.scope.canonical checked
  have signaturesEq := (RecursiveExpressionInvariant.ofStatement boundary.invariant).signatures_eq_whole.trans boundary.scope.signatures.symm
  have parametersEq := boundary.invariant.typeParametersEq.trans boundary.scope.parameters.symm
  have ownerEq : target.currentDeclaration = some inferenceContext.scope.genericOwner := by
    rw [boundary.scope.owner]
    exact boundary.invariant.declarationEq
  obtain ⟨resolvedType, locals, valueType, generalized, binding,
      resolution, _localsEq, valueTypeEq, generalizedEq, bindingEq, resultEq, _contains⟩ :=
    inferStatementFuel_success_letAnnotatedUninitialized_facts form rfl boundary.accepted (bodyRoots selected)
  obtain ⟨wellFormed, _closedScheme, _closedRequirements, _generalizes⟩ :=
    resolvedAnnotationBinderFacts_afterSubstitution
      (target := target) (outer := selected.body.finalized.substitution)
      resolution valueTypeEq generalizedEq bindingEq parameters signaturesEq parametersEq ownerEq
  have resolvedByState : initial.allocateStatementId.2.resolve resolvedType = resolvedType := by
    simpa [State.resolve, InferState.resolve] using
      Detail.resolveSourceType_success_apply_eq_self initial.allocateStatementId.2.inference.substitution resolution
  have valueClosed : valueType.freeVariables = [] := by
    rw [valueTypeEq]
    change (initial.allocateStatementId.2.resolve resolvedType).freeVariables = []
    rw [resolvedByState]
    exact StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil wellFormed
  have schemeEq : generalized.scheme = .mono valueType := by
    rw [generalizedEq]
    exact (generalizeValue_closed_facts initial.allocateStatementId.2 locals
      initial.allocateStatementId.2.nextRequirement valueType target valueClosed).1
  have requirementsEq : generalized.requirements = [] := by
    rw [generalizedEq]
    exact (generalizeValue_closed_facts initial.allocateStatementId.2 locals
      initial.allocateStatementId.2.nextRequirement valueType target valueClosed).2.1
  have allocatedIsolated := activeSchemeQuantifierIsolation_allocateStatementId boundary.invariant.schemeIsolation rfl
  have bindingIsolated : ActiveSchemeQuantifierIsolation binding.2 := by
    rw [← bindingEq, schemeEq, requirementsEq]
    exact activeSchemeQuantifierIsolation_allocateMonoBinder
      (initial.allocateStatementId.2.withLocals locals) name.value valueType (some name.span)
      (activeSchemeQuantifierIsolation_transport allocatedIsolated rfl)
      (by intro metavariable member; simp [valueClosed] at member)
  have bindingOperational : GeneralizedActualStateInvariant binding.2 (evidenceSource selected) := by
    rw [← bindingEq, schemeEq, requirementsEq]
    apply (boundary.operational.allocateStatementId.withLocals locals).allocateMonoBinder
    intro binder member
    exact ProtectedVariables.safe_closed _ _
      (by intro metavariable present; simp [valueClosed] at present)
  have operational : GeneralizedActualStateInvariant result.state (evidenceSource selected) := by
    rw [resultEq]
    exact bindingOperational.recordStatement _ rfl
  have isolation : ActiveSchemeQuantifierIsolation result.state := by
    rw [resultEq]
    exact activeSchemeQuantifierIsolation_transport bindingIsolated rfl
  obtain ⟨finalContext, facts, active, localTyping, agreement⟩ :=
    inferStatementFuel_success_letAnnotatedUninitialized_sound form rfl boundary.accepted parameters
      signaturesEq parametersEq ownerEq boundary.invariant.active boundary.invariant.bindersBelow
      (bodyRoots selected)
  have typing := (boundary.rawSubtree.finalized selected.body.resources).subgraph.statement localTyping (.inl rfl)
  have invariant := boundary.invariant.of_retained_statement_typing boundary.accepted
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked) active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension isolation typing
  exact ⟨finalContext, facts, invariant, boundary.actual.of_statement typing, operational, typing, agreement⟩

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedAssignedValue
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

structure AssignedValueBoundary {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel) (childFuel : Nat) (inferenceContext : SourceInference.Context)
    (targetExpression : Syntax.Expr) (operator : Syntax.ValueAssignOp) (value : Syntax.Expr)
    (initial : State) (assignment : AssignmentResolution) (inferred : InferredExpression) (final : State)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop where
  accepted : Detail.inferAssignedValueFuel childFuel inferenceContext targetExpression operator value initial =
    .ok (assignment, inferred, final)
  interfaces : ExecutableCoercionInterfaces.SourceInterfaces (checkingContext selected).signatures
    selected.body.finalized.solvedRequirements selected.body.finalized.typedSource
  extension : selected.body.finalized.substitution.SemanticallyExtends final.inference.substitution
  scope : CheckingScope selected inferenceContext
  invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target
  actual : ActualContext (checkingContext selected) selected.body.finalized frames target
  operational : GeneralizedActualStateInvariant initial (evidenceSource selected)
  rawKeys : ∀ key, .expression key ∈ assignment.references →
    RawSubtreePreserved (final.toTypedSource (bodyRoots selected)) (evidenceSource selected) (.expression key)
  rawValue : RawSubtreePreserved (final.toTypedSource (bodyRoots selected)) (evidenceSource selected) (.expression inferred.id)
  integerPatterns : final.integerPatterns ⊆ selected.body.returned.integerPatterns
  integerLiterals : final.integerLiterals ⊆ selected.body.returned.integerLiterals
  requirements : final.requirements ⊆ selected.body.returned.requirements
  keysCovered : ∀ key, .expression key ∈ assignment.references →
    TemplateScopeCovered selected.body.finalized.typedSource target (.expression key)
  valueCovered : TemplateScopeCovered selected.body.finalized.typedSource target (.expression inferred.id)
  keysActualCovered : ∀ key, .expression key ∈ assignment.references →
    ActualContext.Covers selected.body.finalized frames (.expression key)
  valueActualCovered : ActualContext.Covers selected.body.finalized frames (.expression inferred.id)

theorem assignedValue_of_actual_children_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {provenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed provenance)
    (placeSound : PlaceRootedSoundnessFor provenance selected childFuel)
    (expressionSound : ExpressionRootedSoundnessFor provenance selected childFuel)
    {inferenceContext : SourceInference.Context} {targetExpression value : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {initial final : State}
    {assignment : AssignmentResolution} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : provenance (.assignedValue childFuel inferenceContext targetExpression operator value
      initial assignment inferred final))
    (boundary : AssignedValueBoundary selected childFuel inferenceContext targetExpression operator value
      initial assignment inferred final frames target) :
    SourceAssignmentHasType selected.body.finalized.typedSource target
      (assignment.applySubstitution selected.body.finalized.substitution) operator inferred.id ∧
    GeneralizedActualStateInvariant final (evidenceSource selected) := by
  have formation := boundary.scope.formation checked
  have canonical := boundary.scope.functionsCanonical checked
  have catalog := boundary.scope.catalog checked
  obtain ⟨place, placeState, valueInitial, placeAccepted, fitting, valueAccepted, targetEq⟩ :=
    assignedValue_actual_prefix boundary.accepted
  let expected := assignmentExpected operator valueInitial place.type
  have valueOrigin :
      (valueInitial = placeState ∧ expected = placeState.resolve place.type) ∨
      (Detail.unify placeState place.type .word = .ok valueInitial ∧ expected = .word) := by
    cases operator with
    | equal =>
        have same : placeState = valueInitial := Except.ok.inj fitting
        subst valueInitial
        exact .inl ⟨rfl, rfl⟩
    | _ => exact .inr ⟨fitting, rfl⟩
  have placeProperties := Detail.inferPlaceFuel_inferenceProperties boundary.invariant.ready formation canonical placeAccepted
  have valueReady : valueInitial.InferenceReady := by
    rcases valueOrigin with ⟨rfl, _⟩ | ⟨unified, _⟩
    · exact placeProperties.2.1
    · exact Detail.unify_preserves_inferenceReady placeProperties.2.1 placeProperties.2.2
        (Ty.variablesBelow_constructor _ _) unified
  have expectedBelow : expected.VariablesBelow valueInitial.inference.next := by
    rcases valueOrigin with ⟨same, expectedEq⟩ | ⟨_, expectedEq⟩
    · rw [expectedEq, same]
      exact placeProperties.2.1.solved.variablesBelow_apply placeProperties.2.2
    · rw [expectedEq]
      exact Ty.variablesBelow_constructor _ _
  have valueProperties := Detail.inferExprFuel_inferenceProperties valueReady formation canonical
    (by intro type member; cases Option.some.inj (Option.mem_def.mp member); exact expectedBelow) valueAccepted
  have valueExtension := boundary.extension.trans valueProperties.1.substitution_extends
  have placeExtension : selected.body.finalized.substitution.SemanticallyExtends placeState.inference.substitution := by
    rcases valueOrigin with ⟨rfl, _⟩ | ⟨unified, _⟩
    · exact valueExtension
    · exact valueExtension.trans (Detail.unify_inferenceProgress placeProperties.2.1.solved
        placeProperties.2.2 (Ty.variablesBelow_constructor _ _) unified).substitution_extends
  have placeInvariant := boundary.invariant.ofPlace formation canonical placeExtension placeAccepted
  have valueInvariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized
      valueInitial target := by
    rcases valueOrigin with ⟨rfl, _⟩ | ⟨unified, _⟩
    · exact placeInvariant
    · exact placeInvariant.unify placeProperties.2.2 (Ty.variablesBelow_constructor _ _) valueExtension unified
  have referencesEq : assignment.target.references = place.references := by
    rw [targetEq]
    rfl
  obtain ⟨actualPlace, actualPlaceState, actualPlaceAccepted, _, placeToAssignment,
      placeLiterals, placePatterns, placeRequirements⟩ :=
    inferAssignedValueFuel_success_place_state_provenance boundary.accepted boundary.invariant.nodesBelow (bodyRoots selected)
  rw [placeAccepted] at actualPlaceAccepted
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualPlaceAccepted).symm
  have placeReference : ∀ key, .expression key ∈ place.references → .expression key ∈ assignment.references := by
    intro key member
    simpa [AssignmentResolution.references, referencesEq] using member
  obtain ⟨placeTyped, placeOperational, placeSafe⟩ := placeSound (descend here (ChildStep.assignedValue_place boundary.accepted placeAccepted)) ({
    accepted := placeAccepted
    interfaces := boundary.interfaces
    extension := placeInvariant.substitutionExtension
    scope := boundary.scope
    invariant := boundary.invariant
    actual := boundary.actual
    operational := boundary.operational
    rawKeys := fun key member => (boundary.rawKeys key (placeReference key member)).monoBefore placeToAssignment
    integerPatterns := List.Subset.trans placePatterns boundary.integerPatterns
    integerLiterals := List.Subset.trans placeLiterals boundary.integerLiterals
    requirements := List.Subset.trans placeRequirements boundary.requirements
    covered := fun key member => boundary.keysCovered key (placeReference key member)
    actualCovered := fun key member => boundary.keysActualCovered key (placeReference key member) } :
    PlaceBoundary selected childFuel inferenceContext targetExpression initial place placeState frames target)
  have targetTypeEq : selected.body.finalized.substitution.apply assignment.target.type =
      selected.body.finalized.substitution.apply place.type := by
    rw [targetEq]
    simpa [State.resolve, InferState.resolve] using boundary.extension place.type
  have targetSubstEq : assignment.target.applySubstitution selected.body.finalized.substitution =
      place.applySubstitution selected.body.finalized.substitution := by
    rw [targetEq]
    have storedEq : selected.body.finalized.substitution.apply (final.resolve place.type) =
        selected.body.finalized.substitution.apply place.type := by
      simpa [State.resolve, InferState.resolve] using boundary.extension place.type
    simpa [PlaceResolution.applySubstitution] using
      congrArg (fun type => ({ place with type := type } : PlaceResolution)) storedEq
  have placeProperties := Detail.inferPlaceFuel_inferenceProperties boundary.invariant.ready formation canonical placeAccepted
  have valueOperational : GeneralizedActualStateInvariant valueInitial (evidenceSource selected) := by
    rcases valueOrigin with ⟨rfl, _⟩ | ⟨unified, _⟩
    · exact placeOperational
    · exact placeOperational.unify placeProperties.2.1 placeProperties.2.2
        (Ty.variablesBelow_constructor _ _) placeSafe
        (fun binder _ => ProtectedVariables.safe_closed binder.scheme.quantified placeState
          (Ty.variablesBelow_constructor 0 _)) unified
  have expectedSafe : ∀ binder ∈ valueInitial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified valueInitial expected := by
    rcases valueOrigin with ⟨same, expectedEq⟩ | ⟨_, expectedEq⟩
    · rw [expectedEq, same]
      intro binder member
      exact ProtectedVariables.safe_resolved placeProperties.2.1 (placeSafe binder member)
    · rw [expectedEq]
      intro binder _
      exact ProtectedVariables.safe_closed _ _ (Ty.variablesBelow_constructor 0 _)
  have expectedAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expected) := by
    rcases valueOrigin with ⟨_, expectedEq⟩ | ⟨_, expectedEq⟩
    · rw [expectedEq]
      have resolved : selected.body.finalized.substitution.apply (placeState.resolve place.type) =
          selected.body.finalized.substitution.apply place.type := by
        simpa only [State.resolve, InferState.resolve] using placeInvariant.substitutionExtension place.type
      rw [resolved]
      exact sourcePlace_type_admissible placeTyped
    · rw [expectedEq]
      exact TypeAdmissible.word (boundary.invariant.typeParameterBinders (by
        simpa only [boundary.scope.owner, boundary.scope.parameters] using boundary.scope.canonical checked))
  have expectedBound : ∀ type ∈ some expected, type.VariablesBelow valueInitial.inference.next := by
    intro type member
    have same : type = expected := Option.some.inj member.symm
    simpa only [same] using expectedBelow
  have expectedPrivate : ∀ binder ∈ valueInitial.localBinders, ∀ type ∈ some expected,
      ProtectedVariables.Safe binder.scheme.quantified valueInitial type := by
    intro binder member type present
    have same : type = expected := Option.some.inj present.symm
    simpa only [same] using expectedSafe binder member
  have valueTyped := expressionSound (descend here
    (ChildStep.assignedValue_value boundary.accepted placeAccepted fitting valueAccepted)) ({
    accepted := valueAccepted
    interfaces := boundary.interfaces
    extension := boundary.extension
    scope := boundary.scope
    invariant := valueInvariant
    actual := boundary.actual
    operational := valueOperational
    expectedBelow := expectedBound
    expectedAdmissible := by
      intro type member
      have same : type = expected := Option.some.inj member.symm
      simpa only [same] using expectedAdmissible
    expectedSafe := expectedPrivate
    rawSubtree := boundary.rawValue
    integerPatterns := boundary.integerPatterns
    integerLiterals := boundary.integerLiterals
    requirements := boundary.requirements
    covered := boundary.valueCovered
    actualCovered := boundary.valueActualCovered } :
    RootedExpressionBoundary selected childFuel inferenceContext value (some expected) valueInitial inferred final frames target)
  have returned := valueOperational.ofExpression valueInvariant.ready catalog formation canonical
    expectedBound expectedPrivate valueAccepted
  refine ⟨?_, returned⟩
  have assignmentPlace : SourcePlaceHasType selected.body.finalized.typedSource target
      (assignment.target.applySubstitution selected.body.finalized.substitution)
      (selected.body.finalized.substitution.apply assignment.target.type) := by
    simpa only [targetSubstEq, targetTypeEq] using placeTyped
  rw [selected.body.resources.source_eq] at assignmentPlace valueTyped ⊢
  exact inferAssignedValueFuel_success_sound_of_typed_result boundary.invariant.ready formation canonical
    boundary.extension assignmentPlace valueTyped boundary.accepted

theorem assignedValue_of_actual_children
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (placeSound : PlaceRootedSoundness selected childFuel)
    (expressionSound : ExpressionRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {targetExpression value : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {initial final : State}
    {assignment : AssignmentResolution} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : AssignedValueBoundary selected childFuel inferenceContext targetExpression operator value
      initial assignment inferred final frames target) :
    SourceAssignmentHasType selected.body.finalized.typedSource target
      (assignment.applySubstitution selected.body.finalized.substitution) operator inferred.id ∧
    GeneralizedActualStateInvariant final (evidenceSource selected) := by
  exact assignedValue_of_actual_children_for (provenance := fun _ => True) checked true_childClosed
    (fun _ boundary => placeSound boundary) (fun _ boundary => expressionSound boundary) trivial boundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedBitNotAssignment
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedBlockStatement
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution
open SourceInferenceStatementsSoundness

theorem statement_block
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {body : List Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : statement.value = .block body)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (recursive : ∀ {bodyResult : Detail.BlockResult},
      StatementsBoundary selected childFuel inferenceContext body expectedReturn
        initial.allocateStatementId.2 bodyResult frames target →
      StatementsConclusion selected inferenceContext expectedReturn bodyResult frames target) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  have resources := selected.body.resources
  obtain ⟨bodyResult, bodySuccess, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_block_facts form rfl boundary.accepted (bodyRoots selected)
  obtain ⟨other, otherSuccess, _, bodyExtension, bodyPatterns, bodyRequirements⟩ :=
    inferStatementFuel_success_block_child_provenance form rfl boundary.accepted
      boundary.invariant.nodesBelow (bodyRoots selected)
  rw [bodySuccess] at otherSuccess
  have same := (Except.ok.inj otherSuccess).symm
  subst other
  have allocatedInvariant := boundary.invariant.allocateStatementId rfl
  have bodySubstitution : selected.body.finalized.substitution.SemanticallyExtends
      bodyResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using boundary.extension
  have containsFinal := (boundary.rawSubtree.finalized resources).containsStatement containsRaw
  have childEdge : ∀ child ∈ bodyResult.statements,
      DirectChild (result.state.toTypedSource (bodyRoots selected))
        (.statement result.id) (.statement child) := by
    intro child member
    exact directChild_statement_reference containsRaw (by simp [StatementForm.references, member])
  have finalEdge : ∀ child ∈ bodyResult.statements,
      DirectChild selected.body.finalized.typedSource (.statement result.id) (.statement child) :=
    fun child member => (boundary.rawSubtree.finalized resources).directChild (childEdge child member)
  have bodyLiterals : bodyResult.state.integerLiterals ⊆ selected.body.returned.integerLiterals := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using boundary.integerLiterals
  obtain ⟨bodyContext, bodyFacts, bodyInvariant, _, bodyOperational, bodyTyping, bodyAgreement⟩ :=
    recursive ({
      accepted := bodySuccess
      interfaces := boundary.interfaces
      extension := bodySubstitution
      scope := boundary.scope
      invariant := allocatedInvariant
      actual := boundary.actual
      operational := boundary.operational.allocateStatementId
      rawSubtrees := fun child member =>
        (boundary.rawSubtree.child (childEdge child member)).monoBefore bodyExtension
      integerPatterns := List.Subset.trans bodyPatterns boundary.integerPatterns
      integerLiterals := bodyLiterals
      requirements := List.Subset.trans bodyRequirements boundary.requirements
      covered := fun child member => TemplateScopeCovered.statementChild
        boundary.covered resources.graph_closed (finalEdge child member) (fun _ present => present)
      actualCovered := fun child member => boundary.actualCovered.statement_reference
        containsFinal (by simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
          StatementForm.references, member]) } :
      StatementsBoundary selected childFuel inferenceContext body expectedReturn
        initial.allocateStatementId.2 bodyResult frames target)
  let facts : StatementFacts := {
    type := bodyFacts.type
    hasValue := bodyFacts.sawReturn
    sawReturn := bodyFacts.sawReturn
    control := bodyFacts.control.eraseValue }
  have active : ActiveLocalContextInvariant result.state selected.body.finalized.substitution target := by
    rw [resultEq]
    exact allocatedInvariant.active.restoreLexicalScope_recordNode _
  have operational : GeneralizedActualStateInvariant result.state (evidenceSource selected) := by
    rw [resultEq]
    exact (bodyOperational.restoreSaved boundary.operational.allocateStatementId.origins
      (ProtectedVariables.inferStatementsFuel_binders_subset bodySuccess)).recordStatement _ rfl
  have typing : StatementHasType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth } target result.id target facts := by
    apply StatementHasType.block containsFinal rfl bodyTyping
    change selected.body.finalized.substitution.apply result.type = bodyFacts.type
    rw [resultEq]
    exact bodyAgreement.type_eq.symm
  have agreement : StatementResultMatchesFactsAfterSubstitution
      selected.body.finalized.substitution result facts := by
    rw [resultEq]
    exact StatementResultMatchesFactsAfterSubstitution.block bodyAgreement _ _
  have bindersEq : result.state.localBinders = initial.localBinders := by
    simp [resultEq, State.restoreLexicalScope, State.recordNode, State.lexicalScope]
  have finalInvariant := boundary.invariant.of_retained_statement_typing boundary.accepted
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked) active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension (activeSchemeQuantifierIsolation_transport boundary.invariant.schemeIsolation bindersEq)
    typing
  exact ⟨target, facts, finalInvariant, boundary.actual, operational, typing, agreement⟩


/-- Reuse the block typing proof with its actual, fixed child call. -/
theorem statement_block_for {callProvenance : CallIndex → Prop}
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursive : StatementsRootedSoundnessFor callProvenance selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {body : List Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.statement (childFuel + 1) inferenceContext statement expectedReturn initial result))
    (form : statement.value = .block body)
    (returnSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  apply statement_block checked form boundary
  intro bodyResult childBoundary
  apply recursive (descend here (.statement_block boundary.accepted form rfl childBoundary.accepted))
    (fun binder member => returnSafe binder member) returnAdmissible childBoundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionStatement
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution
open SourceInferenceStatementsSoundness

theorem statement_expression_for {callProvenance : CallIndex → Prop}
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursive : ExpressionRootedSoundnessFor callProvenance selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {expression : Syntax.Expr} {trailingSemicolon : Bool} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.statement (childFuel + 1) inferenceContext statement expectedReturn initial result))
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
  have childHere := descend here (.statement_expression boundary.accepted form allocationEq childSuccess)
  have typed := recursive childHere ({
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
  exact statement_expression_for (callProvenance := fun _ => True) checked true_childClosed
    (fun _ boundary => recursive boundary) True.intro form boundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedIfElseStatement
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness SourceInferenceExecution

theorem statement_if_with_else_for {callProvenance : CallIndex → Prop}
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursiveExpression : ExpressionRootedSoundnessFor callProvenance selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {condition : Syntax.Expr} {body elseBody : Syntax.Block} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.statement (childFuel + 1) inferenceContext statement expectedReturn initial result))
    (form : statement.value = .ifThen condition body (some elseBody))
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (recursiveBody : ∀ {bodySource : List Syntax.Statement} {bodyInitial : State} {bodyResult : Detail.BlockResult},
      callProvenance (.statements childFuel inferenceContext bodySource expectedReturn bodyInitial bodyResult) →
      (∀ binder ∈ bodyInitial.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified bodyInitial expectedReturn) →
      TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn) →
      StatementsBoundary selected childFuel inferenceContext bodySource expectedReturn
        bodyInitial bodyResult frames target →
      StatementsConclusion selected inferenceContext expectedReturn bodyResult frames target) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  have resources := selected.body.resources
  have formation := boundary.scope.formation checked
  have canonical := boundary.scope.functionsCanonical checked
  have catalog := boundary.scope.catalog checked
  have allocatedInvariant := boundary.invariant.allocateStatementId rfl
  have allocatedOperational := boundary.operational.allocateStatementId
  obtain ⟨conditionValue, conditionState, bodyResult, elseResult, conditionAccepted, bodyAccepted,
      elseAccepted, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_ifWithElse_facts form rfl boundary.accepted (bodyRoots selected)
  obtain ⟨otherState, otherBody, otherElse, ⟨otherCondition, otherAccepted⟩, otherBodyAccepted,
      otherElseAccepted, _, _, bodyExtension, elseExtension, bodyPatterns, elsePatterns,
      bodyRequirements, elseRequirements⟩ :=
    inferStatementFuel_success_ifWithElse_child_provenance form rfl boundary.accepted
      boundary.invariant.nodesBelow (bodyRoots selected)
  rw [conditionAccepted] at otherAccepted
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj otherAccepted).symm
  rw [bodyAccepted] at otherBodyAccepted
  have same := (Except.ok.inj otherBodyAccepted).symm
  subst otherBody
  rw [elseAccepted] at otherElseAccepted
  have sameElse := (Except.ok.inj otherElseAccepted).symm
  subst otherElse
  have conditionExpected : ∀ type ∈ some Ty.bool,
      type.VariablesBelow initial.allocateStatementId.2.inference.next := by
    intro type member
    have same : type = .bool := (Option.some.inj member).symm
    subst type
    exact Ty.variablesBelow_constructor _ _
  have conditionSafe : ∀ binder ∈ initial.allocateStatementId.2.localBinders, ∀ type ∈ some Ty.bool,
      ProtectedVariables.Safe binder.scheme.quantified initial.allocateStatementId.2 type := by
    intro binder _ type member
    have same : type = .bool := (Option.some.inj member).symm
    subst type
    exact ProtectedVariables.safe_closed _ _ (Ty.variablesBelow_constructor _ _)
  have conditionProperties := Detail.inferExprFuel_inferenceProperties allocatedInvariant.ready
    formation canonical conditionExpected conditionAccepted
  have bodyProperties := Detail.inferStatementsFuel_inferenceProperties conditionProperties.2.1
    formation canonical (allocatedInvariant.returnBelow.weaken conditionProperties.1.next_le) bodyAccepted
  have restoredProperties := State.restoreLexicalScope_inferenceProperties conditionProperties.2.1 bodyProperties.1
  have elseProperties := Detail.inferStatementsFuel_inferenceProperties restoredProperties.2 formation canonical
    ((allocatedInvariant.returnBelow.weaken conditionProperties.1.next_le).weaken restoredProperties.1.next_le)
    elseAccepted
  have elseSubstitution : selected.body.finalized.substitution.SemanticallyExtends
      elseResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using boundary.extension
  have bodySubstitution : selected.body.finalized.substitution.SemanticallyExtends
      bodyResult.state.inference.substitution := elseSubstitution.trans elseProperties.1.substitution_extends
  have conditionSubstitution := bodySubstitution.trans bodyProperties.1.substitution_extends
  have conditionInvariant := allocatedInvariant.inferExprFuel conditionAccepted formation canonical
    conditionExpected conditionSubstitution
  have conditionOperational := allocatedOperational.ofExpression allocatedInvariant.ready
    catalog formation canonical conditionExpected conditionSafe conditionAccepted
  have containsFinal := (boundary.rawSubtree.finalized resources).containsStatement containsRaw
  have conditionEdge : DirectChild (result.state.toTypedSource (bodyRoots selected))
      (.statement result.id) (.expression conditionValue.id) :=
    directChild_statement_reference containsRaw (by simp [StatementForm.references])
  have bodyEdge : ∀ child ∈ bodyResult.statements,
      DirectChild (result.state.toTypedSource (bodyRoots selected))
        (.statement result.id) (.statement child) := by
    intro child member
    exact directChild_statement_reference containsRaw (by simp [StatementForm.references, member])
  have elseEdge : ∀ child ∈ elseResult.statements,
      DirectChild (result.state.toTypedSource (bodyRoots selected))
        (.statement result.id) (.statement child) := by
    intro child member
    exact directChild_statement_reference containsRaw (by simp [StatementForm.references, member])
  have elseLiterals : elseResult.state.integerLiterals ⊆ selected.body.returned.integerLiterals := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using boundary.integerLiterals
  have bodyLiterals : bodyResult.state.integerLiterals ⊆ selected.body.returned.integerLiterals := by
    have subset := Detail.inferStatementsFuel_integerLiterals_subset elseAccepted
    exact List.Subset.trans subset elseLiterals
  have conditionSource := (inferStatementsFuel_success_typingSourceExtends bodyAccepted
    conditionInvariant.nodesBelow (bodyRoots selected)).trans bodyExtension
  have conditionHere := descend here (.statement_if_condition boundary.accepted form rfl conditionAccepted)
  have conditionTyping := recursiveExpression conditionHere ({
    accepted := conditionAccepted
    interfaces := boundary.interfaces
    extension := conditionSubstitution
    scope := boundary.scope
    invariant := RecursiveExpressionInvariant.ofStatement allocatedInvariant
    actual := boundary.actual
    operational := allocatedOperational
    expectedBelow := conditionExpected
    expectedAdmissible := by
      intro type member
      have same : type = .bool := (Option.some.inj member).symm
      subst type
      exact TypeAdmissible.bool ((RecursiveExpressionInvariant.ofStatement allocatedInvariant).typeParameterBinders (by
        simpa [boundary.scope.owner, boundary.scope.parameters] using boundary.scope.canonical checked))
    expectedSafe := conditionSafe
    integerPatterns := List.Subset.trans (Detail.inferStatementsFuel_integerPatterns_subset bodyAccepted)
      (List.Subset.trans bodyPatterns boundary.integerPatterns)
    integerLiterals := List.Subset.trans (Detail.inferStatementsFuel_integerLiterals_subset bodyAccepted) bodyLiterals
    requirements := List.Subset.trans (Detail.inferStatementsFuel_requirements_subset bodyAccepted)
      (List.Subset.trans bodyRequirements boundary.requirements)
    covered := TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      boundary.covered resources.graph_closed containsFinal
      (by simp [StatementNode.applySubstitution, StatementForm.applySubstitution, statementInitializedLetBindings])
      (by simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references])
    actualCovered := boundary.actualCovered.statement_reference containsFinal (by
      simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references])
    rawSubtree := (boundary.rawSubtree.child conditionEdge).monoBefore conditionSource } :
    RootedExpressionBoundary selected childFuel inferenceContext condition (some .bool)
      initial.allocateStatementId.2 conditionValue conditionState frames target)
  have bodyReturnSafe : ∀ binder ∈ conditionState.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified conditionState expectedReturn := by
    intro binder member
    have binders : conditionState.localBinders = initial.localBinders :=
      congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq conditionAccepted)
    have entering : binder ∈ initial.localBinders := binders ▸ member
    have privacy := ProtectedVariables.inferExprFuel_private binder.scheme.quantified childFuel
      inferenceContext condition (some .bool) initial.allocateStatementId.2
      allocatedInvariant.ready allocatedOperational.requirements
      (allocatedOperational.quantifiersBelow binder entering)
      (allocatedOperational.privacy binder entering) catalog formation canonical conditionExpected
      (conditionSafe binder entering) _ conditionAccepted
    exact privacy.1 expectedReturn (returnSafe binder entering)
  obtain ⟨bodyContext, bodyFacts, bodyInvariant, _, bodyOperational, bodyTyping, bodyAgreement⟩ :=
    recursiveBody (descend here (.statement_if_then boundary.accepted form rfl conditionAccepted bodyAccepted))
      bodyReturnSafe returnAdmissible ({
    accepted := bodyAccepted
    interfaces := boundary.interfaces
    extension := bodySubstitution
    scope := boundary.scope
    invariant := conditionInvariant
    actual := boundary.actual
    operational := conditionOperational
    rawSubtrees := fun child member => (boundary.rawSubtree.child (bodyEdge child member)).monoBefore bodyExtension
    integerPatterns := List.Subset.trans bodyPatterns boundary.integerPatterns
    integerLiterals := bodyLiterals
    requirements := List.Subset.trans bodyRequirements boundary.requirements
    covered := fun child member => TemplateScopeCovered.statementChild boundary.covered
      resources.graph_closed ((boundary.rawSubtree.finalized resources).directChild (bodyEdge child member))
      (fun _ present => present)
    actualCovered := fun child member => boundary.actualCovered.statement_reference containsFinal (by
      simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references, member]) } :
    StatementsBoundary selected childFuel inferenceContext body.value expectedReturn
      conditionState bodyResult frames target)
  have elseInvariant := conditionInvariant.restoreLexicalScope bodyProperties.1 bodyInvariant.nodesBelow
    (Detail.inferStatementsFuel_nextLocal_le bodyAccepted) bodySubstitution
  have elseOperational := bodyOperational.restoreSaved conditionOperational.origins
    (ProtectedVariables.inferStatementsFuel_binders_subset bodyAccepted)
  have elseReturnSafe : ∀ binder ∈ conditionState.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified
        (bodyResult.state.restoreLexicalScope conditionState.lexicalScope) expectedReturn := by
    intro binder member
    have privacy := ProtectedVariables.inferStatementsFuel_private binder.scheme.quantified childFuel
      inferenceContext body.value expectedReturn conditionState conditionInvariant.ready
      conditionOperational.requirements (conditionOperational.quantifiersBelow binder member)
      (conditionOperational.privacy binder member) catalog formation canonical conditionInvariant.returnBelow
      (bodyReturnSafe binder member) _ bodyAccepted
    exact privacy.1 expectedReturn (bodyReturnSafe binder member)
  obtain ⟨elseContext, elseFacts, _, _, elseFinishedOperational, elseTyping, elseAgreement⟩ :=
    recursiveBody (descend here (.statement_if_else boundary.accepted form rfl conditionAccepted rfl bodyAccepted elseAccepted))
      elseReturnSafe returnAdmissible ({
      accepted := elseAccepted
      interfaces := boundary.interfaces
      extension := elseSubstitution
      scope := boundary.scope
      invariant := elseInvariant
      actual := boundary.actual
      operational := elseOperational
      rawSubtrees := fun child member => (boundary.rawSubtree.child (elseEdge child member)).monoBefore elseExtension
      integerPatterns := List.Subset.trans elsePatterns boundary.integerPatterns
      integerLiterals := elseLiterals
      requirements := List.Subset.trans elseRequirements boundary.requirements
      covered := fun child member => TemplateScopeCovered.statementChild boundary.covered
        resources.graph_closed ((boundary.rawSubtree.finalized resources).directChild (elseEdge child member))
        (fun _ present => present)
      actualCovered := fun child member => boundary.actualCovered.statement_reference containsFinal (by
        simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references, member]) } :
      StatementsBoundary selected childFuel inferenceContext elseBody.value expectedReturn
        (bodyResult.state.restoreLexicalScope conditionState.lexicalScope) elseResult frames target)
  let facts : StatementFacts := {
    type := if bodyFacts.sawReturn && elseFacts.sawReturn then
      selected.body.finalized.substitution.apply expectedReturn else .unit
    hasValue := bodyFacts.sawReturn && elseFacts.sawReturn
    sawReturn := bodyFacts.sawReturn && elseFacts.sawReturn
    control := bodyFacts.control.branches elseFacts.control }
  have active : ActiveLocalContextInvariant result.state selected.body.finalized.substitution target := by
    rw [resultEq]
    exact conditionInvariant.active.restoreLexicalScope_recordNode _
  have operational : GeneralizedActualStateInvariant result.state (evidenceSource selected) := by
    rw [resultEq]
    have saved := ProtectedVariables.inferStatementsFuel_binders_subset elseAccepted
    exact (elseFinishedOperational.restoreSaved conditionOperational.origins saved).recordStatement _ rfl
  have conditionBool : ExpressionHasType selected.body.finalized.typedSource target conditionValue.id .bool := by
    have typeEq : selected.body.finalized.substitution.apply conditionValue.type = .bool := by
      simpa using Detail.inferExprFuel_expected_type_apply_eq conditionAccepted conditionSubstitution
    rw [typeEq] at conditionTyping
    exact conditionTyping
  have agreement : StatementResultMatchesFactsAfterSubstitution
      selected.body.finalized.substitution result facts := by
    rw [resultEq]
    exact StatementResultMatchesFactsAfterSubstitution.ifWithElse bodyAgreement elseAgreement elseSubstitution _ _
  have typing : StatementHasType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn,
        loopDepth := inferenceContext.loopDepth } target result.id target facts := by
    exact .ifWithElse containsFinal rfl conditionBool bodyTyping elseTyping agreement.type_eq.symm
  have conditionBinders := congrArg LexicalScope.binders
    (Detail.inferExprFuel_success_lexicalScope_eq conditionAccepted)
  have bindersEq : result.state.localBinders = initial.localBinders := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode, State.lexicalScope] using conditionBinders
  have finalInvariant := boundary.invariant.of_retained_statement_typing boundary.accepted formation canonical active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension (activeSchemeQuantifierIsolation_transport boundary.invariant.schemeIsolation bindersEq) typing
  exact ⟨target, facts, finalInvariant, boundary.actual, operational, typing, agreement⟩

theorem statement_if_with_else
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursiveExpression : ExpressionRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {condition : Syntax.Expr} {body elseBody : Syntax.Block} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : statement.value = .ifThen condition body (some elseBody))
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (recursiveBody : ∀ {bodySource : List Syntax.Statement} {bodyInitial : State} {bodyResult : Detail.BlockResult},
      (∀ binder ∈ bodyInitial.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified bodyInitial expectedReturn) →
      TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn) →
      StatementsBoundary selected childFuel inferenceContext bodySource expectedReturn
        bodyInitial bodyResult frames target →
      StatementsConclusion selected inferenceContext expectedReturn bodyResult frames target) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  exact statement_if_with_else_for (callProvenance := fun _ => True) checked true_childClosed
    (fun _ boundary => recursiveExpression boundary) True.intro form boundary returnSafe returnAdmissible
    (fun _ safe admissible boundary => recursiveBody safe admissible boundary)

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedIfStatement
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness SourceInferenceExecution

theorem statement_if_without_else_for {callProvenance : CallIndex → Prop}
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursiveExpression : ExpressionRootedSoundnessFor callProvenance selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {condition : Syntax.Expr} {body : Syntax.Block} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.statement (childFuel + 1) inferenceContext statement expectedReturn initial result))
    (form : statement.value = .ifThen condition body none)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (recursiveBody : ∀ {bodyInitial : State} {bodyResult : Detail.BlockResult},
      callProvenance (.statements childFuel inferenceContext body.value expectedReturn bodyInitial bodyResult) →
      (∀ binder ∈ bodyInitial.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified bodyInitial expectedReturn) →
      TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn) →
      StatementsBoundary selected childFuel inferenceContext body.value expectedReturn
        bodyInitial bodyResult frames target →
      StatementsConclusion selected inferenceContext expectedReturn bodyResult frames target) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  have resources := selected.body.resources
  have formation := boundary.scope.formation checked
  have canonical := boundary.scope.functionsCanonical checked
  have catalog := boundary.scope.catalog checked
  have allocatedInvariant := boundary.invariant.allocateStatementId rfl
  have allocatedOperational := boundary.operational.allocateStatementId
  obtain ⟨conditionValue, conditionState, bodyResult, conditionAccepted, bodyAccepted,
      resultEq, containsRaw⟩ :=
    inferStatementFuel_success_ifWithoutElse_facts form rfl boundary.accepted (bodyRoots selected)
  obtain ⟨otherState, otherBody, ⟨otherCondition, otherAccepted⟩, otherBodyAccepted,
      _, bodyExtension, bodyPatterns, bodyRequirements⟩ :=
    inferStatementFuel_success_ifWithoutElse_child_provenance form rfl boundary.accepted
      boundary.invariant.nodesBelow (bodyRoots selected)
  rw [conditionAccepted] at otherAccepted
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj otherAccepted).symm
  rw [bodyAccepted] at otherBodyAccepted
  have same := (Except.ok.inj otherBodyAccepted).symm
  subst otherBody
  have conditionExpected : ∀ type ∈ some Ty.bool,
      type.VariablesBelow initial.allocateStatementId.2.inference.next := by
    intro type member
    have same : type = .bool := (Option.some.inj member).symm
    subst type
    exact Ty.variablesBelow_constructor _ _
  have conditionSafe : ∀ binder ∈ initial.allocateStatementId.2.localBinders, ∀ type ∈ some Ty.bool,
      ProtectedVariables.Safe binder.scheme.quantified initial.allocateStatementId.2 type := by
    intro binder _ type member
    have same : type = .bool := (Option.some.inj member).symm
    subst type
    exact ProtectedVariables.safe_closed _ _ (Ty.variablesBelow_constructor _ _)
  have conditionProperties := Detail.inferExprFuel_inferenceProperties allocatedInvariant.ready
    formation canonical conditionExpected conditionAccepted
  have bodyProperties := Detail.inferStatementsFuel_inferenceProperties conditionProperties.2.1
    formation canonical (allocatedInvariant.returnBelow.weaken conditionProperties.1.next_le) bodyAccepted
  have bodySubstitution : selected.body.finalized.substitution.SemanticallyExtends
      bodyResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using boundary.extension
  have conditionSubstitution := bodySubstitution.trans bodyProperties.1.substitution_extends
  have conditionInvariant := allocatedInvariant.inferExprFuel conditionAccepted formation canonical
    conditionExpected conditionSubstitution
  have conditionOperational := allocatedOperational.ofExpression allocatedInvariant.ready
    catalog formation canonical conditionExpected conditionSafe conditionAccepted
  have containsFinal := (boundary.rawSubtree.finalized resources).containsStatement containsRaw
  have conditionEdge : DirectChild (result.state.toTypedSource (bodyRoots selected))
      (.statement result.id) (.expression conditionValue.id) :=
    directChild_statement_reference containsRaw (by simp [StatementForm.references])
  have bodyEdge : ∀ child ∈ bodyResult.statements,
      DirectChild (result.state.toTypedSource (bodyRoots selected))
        (.statement result.id) (.statement child) := by
    intro child member
    exact directChild_statement_reference containsRaw (by simp [StatementForm.references, member])
  have bodyLiterals : bodyResult.state.integerLiterals ⊆ selected.body.returned.integerLiterals := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using boundary.integerLiterals
  have conditionSource := (inferStatementsFuel_success_typingSourceExtends bodyAccepted
    conditionInvariant.nodesBelow (bodyRoots selected)).trans bodyExtension
  have conditionHere := descend here (.statement_if_condition boundary.accepted form rfl conditionAccepted)
  have conditionTyping := recursiveExpression conditionHere ({
    accepted := conditionAccepted
    interfaces := boundary.interfaces
    extension := conditionSubstitution
    scope := boundary.scope
    invariant := RecursiveExpressionInvariant.ofStatement allocatedInvariant
    actual := boundary.actual
    operational := allocatedOperational
    expectedBelow := conditionExpected
    expectedAdmissible := by
      intro type member
      have same : type = .bool := (Option.some.inj member).symm
      subst type
      exact TypeAdmissible.bool ((RecursiveExpressionInvariant.ofStatement allocatedInvariant).typeParameterBinders (by
        simpa [boundary.scope.owner, boundary.scope.parameters] using boundary.scope.canonical checked))
    expectedSafe := conditionSafe
    integerPatterns := List.Subset.trans (Detail.inferStatementsFuel_integerPatterns_subset bodyAccepted)
      (List.Subset.trans bodyPatterns boundary.integerPatterns)
    integerLiterals := List.Subset.trans (Detail.inferStatementsFuel_integerLiterals_subset bodyAccepted) bodyLiterals
    requirements := List.Subset.trans (Detail.inferStatementsFuel_requirements_subset bodyAccepted)
      (List.Subset.trans bodyRequirements boundary.requirements)
    covered := TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      boundary.covered resources.graph_closed containsFinal
      (by simp [StatementNode.applySubstitution, StatementForm.applySubstitution, statementInitializedLetBindings])
      (by simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references])
    actualCovered := boundary.actualCovered.statement_reference containsFinal (by
      simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references])
    rawSubtree := (boundary.rawSubtree.child conditionEdge).monoBefore conditionSource } :
    RootedExpressionBoundary selected childFuel inferenceContext condition (some .bool)
      initial.allocateStatementId.2 conditionValue conditionState frames target)
  have bodyReturnSafe : ∀ binder ∈ conditionState.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified conditionState expectedReturn := by
    intro binder member
    have binders : conditionState.localBinders = initial.localBinders :=
      congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq conditionAccepted)
    have entering : binder ∈ initial.localBinders := binders ▸ member
    have privacy := ProtectedVariables.inferExprFuel_private binder.scheme.quantified childFuel
      inferenceContext condition (some .bool) initial.allocateStatementId.2
      allocatedInvariant.ready allocatedOperational.requirements
      (allocatedOperational.quantifiersBelow binder entering)
      (allocatedOperational.privacy binder entering) catalog formation canonical conditionExpected
      (conditionSafe binder entering) _ conditionAccepted
    exact privacy.1 expectedReturn (returnSafe binder entering)
  obtain ⟨bodyContext, bodyFacts, _, _, bodyOperational, bodyTyping, bodyAgreement⟩ :=
    recursiveBody (descend here (.statement_if_then boundary.accepted form rfl conditionAccepted bodyAccepted))
      bodyReturnSafe returnAdmissible ({
    accepted := bodyAccepted
    interfaces := boundary.interfaces
    extension := bodySubstitution
    scope := boundary.scope
    invariant := conditionInvariant
    actual := boundary.actual
    operational := conditionOperational
    rawSubtrees := fun child member => (boundary.rawSubtree.child (bodyEdge child member)).monoBefore bodyExtension
    integerPatterns := List.Subset.trans bodyPatterns boundary.integerPatterns
    integerLiterals := bodyLiterals
    requirements := List.Subset.trans bodyRequirements boundary.requirements
    covered := fun child member => TemplateScopeCovered.statementChild boundary.covered
      resources.graph_closed ((boundary.rawSubtree.finalized resources).directChild (bodyEdge child member))
      (fun _ present => present)
    actualCovered := fun child member => boundary.actualCovered.statement_reference containsFinal (by
      simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references, member]) } :
    StatementsBoundary selected childFuel inferenceContext body.value expectedReturn
      conditionState bodyResult frames target)
  let facts : StatementFacts := {
    type := .unit, hasValue := false, sawReturn := false,
    control := bodyFacts.control.branches (.ordinary .unit) }
  have active : ActiveLocalContextInvariant result.state selected.body.finalized.substitution target := by
    rw [resultEq]
    exact conditionInvariant.active.restoreLexicalScope_recordNode _
  have operational : GeneralizedActualStateInvariant result.state (evidenceSource selected) := by
    rw [resultEq]
    exact (bodyOperational.restoreSaved conditionOperational.origins
      (ProtectedVariables.inferStatementsFuel_binders_subset bodyAccepted)).recordStatement _ rfl
  have conditionBool : ExpressionHasType selected.body.finalized.typedSource target conditionValue.id .bool := by
    have typeEq : selected.body.finalized.substitution.apply conditionValue.type = .bool := by
      simpa using Detail.inferExprFuel_expected_type_apply_eq conditionAccepted conditionSubstitution
    rw [typeEq] at conditionTyping
    exact conditionTyping
  have typing : StatementHasType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn,
        loopDepth := inferenceContext.loopDepth } target result.id target facts := by
    exact .ifWithoutElse containsFinal rfl conditionBool bodyTyping
      (by simp [StatementNode.applySubstitution, resultEq])
  have agreement : StatementResultMatchesFactsAfterSubstitution
      selected.body.finalized.substitution result facts := by
    rw [resultEq]
    exact StatementResultMatchesFactsAfterSubstitution.ifWithoutElse _ bodyFacts _ _
  have conditionBinders := congrArg LexicalScope.binders
    (Detail.inferExprFuel_success_lexicalScope_eq conditionAccepted)
  have bindersEq : result.state.localBinders = initial.localBinders := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode, State.lexicalScope] using conditionBinders
  have finalInvariant := boundary.invariant.of_retained_statement_typing boundary.accepted formation canonical active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension (activeSchemeQuantifierIsolation_transport boundary.invariant.schemeIsolation bindersEq) typing
  exact ⟨target, facts, finalInvariant, boundary.actual, operational, typing, agreement⟩

theorem statement_if_without_else
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursiveExpression : ExpressionRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {condition : Syntax.Expr} {body : Syntax.Block} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : statement.value = .ifThen condition body none)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (recursiveBody : ∀ {bodyInitial : State} {bodyResult : Detail.BlockResult},
      (∀ binder ∈ bodyInitial.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified bodyInitial expectedReturn) →
      TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn) →
      StatementsBoundary selected childFuel inferenceContext body.value expectedReturn
        bodyInitial bodyResult frames target →
      StatementsConclusion selected inferenceContext expectedReturn bodyResult frames target) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  exact statement_if_without_else_for (callProvenance := fun _ => True) checked true_childClosed
    (fun _ boundary => recursiveExpression boundary) True.intro form boundary returnSafe returnAdmissible
    (fun _ safe admissible boundary => recursiveBody safe admissible boundary)

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedReturnStatement
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution
open SourceInferenceStatementsSoundness

theorem statement_returnValue_for {callProvenance : CallIndex → Prop}
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursive : ExpressionRootedSoundnessFor callProvenance selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {expression : Syntax.Expr} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.statement (childFuel + 1) inferenceContext statement expectedReturn initial result))
    (form : statement.value = .returnStmt (some expression))
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target
      (selected.body.finalized.substitution.apply expectedReturn)) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  have resources := selected.body.resources
  generalize allocationEq : initial.allocateStatementId = allocatedPair
  rcases allocatedPair with ⟨id, allocated⟩
  obtain ⟨inferred, childState, childSuccess, provenance⟩ :=
    inferStatementFuel_success_returnValue_child_provenance form allocationEq
      boundary.accepted boundary.invariant.nodesBelow (bodyRoots selected)
  obtain ⟨actualInferred, actualState, actualSuccess, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_returnValue_facts form allocationEq boundary.accepted (bodyRoots selected)
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
  have expectedBelow : ∀ type ∈ (some expectedReturn : Option Ty),
      type.VariablesBelow allocated.inference.next := by
    intro type member
    cases Option.mem_def.mp member
    exact (boundary.invariant.allocateStatementId allocationEq).returnBelow
  have expectedSafe : ∀ binder ∈ allocated.localBinders, ∀ type ∈ (some expectedReturn : Option Ty),
      ProtectedVariables.Safe binder.scheme.quantified allocated type := by
    intro binder present type member
    cases Option.mem_def.mp member
    have stateEq : initial.allocateStatementId.2 = allocated := congrArg Prod.snd allocationEq
    rw [← stateEq] at present ⊢
    exact returnSafe binder present
  have childHere := descend here (.statement_return boundary.accepted form allocationEq childSuccess)
  have typed := recursive childHere ({
    accepted := childSuccess
    interfaces := boundary.interfaces
    extension := childExtension
    scope := boundary.scope
    invariant := allocatedInvariant
    actual := boundary.actual
    operational := allocatedOperational
    expectedBelow := expectedBelow
    expectedAdmissible := by
      intro type member
      cases Option.mem_def.mp member
      exact returnAdmissible
    expectedSafe := expectedSafe
    integerPatterns := List.Subset.trans provenance.integerPatternsSubset boundary.integerPatterns
    integerLiterals := childLiterals
    requirements := List.Subset.trans provenance.requirementsSubset boundary.requirements
    covered := childCovered
    actualCovered := childActualCovered
    rawSubtree := (boundary.rawSubtree.child childEdge).monoBefore provenance.sourceExtension } :
    RootedExpressionBoundary selected childFuel inferenceContext expression (some expectedReturn)
      allocated inferred childState frames target)
  have childActive := allocatedInvariant.active.inferExprFuel childSuccess
  have childOperational := allocatedOperational.ofExpression allocatedInvariant.ready
    (boundary.scope.catalog checked) (boundary.scope.formation checked)
    (boundary.scope.functionsCanonical checked) expectedBelow expectedSafe childSuccess
  have bindersEq : result.state.localBinders = initial.localBinders := by
    have childEq := congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq childSuccess)
    have allocationScope := congrArg LexicalScope.binders (Detail.allocateStatementId_success_lexicalScope allocationEq)
    simpa only [resultEq, State.recordNode, State.lexicalScope] using childEq.trans allocationScope
  have expectedEq := Detail.inferExprFuel_expected_type_apply_eq childSuccess childExtension
  have valueTyping : ExpressionHasType selected.body.finalized.typedSource target inferred.id
      (selected.body.finalized.substitution.apply expectedReturn) := expectedEq ▸ typed
  have active : ActiveLocalContextInvariant result.state selected.body.finalized.substitution target := by
    rw [resultEq]
    exact childActive.recordNode _
  have operational : GeneralizedActualStateInvariant result.state (evidenceSource selected) := by
    rw [resultEq]
    exact childOperational.recordStatement _ rfl
  have typing : StatementHasType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth } target result.id target {
        type := selected.body.finalized.substitution.apply expectedReturn
        hasValue := true, sawReturn := true, control := .returned } := by
    apply StatementHasType.returnValue containsFinal rfl valueTyping
    change selected.body.finalized.substitution.apply result.type = _
    rw [resultEq]
    exact childExtension expectedReturn
  have agreement : StatementResultMatchesFactsAfterSubstitution selected.body.finalized.substitution result {
      type := selected.body.finalized.substitution.apply expectedReturn
      hasValue := true, sawReturn := true, control := .returned } := by
    rw [resultEq]
    exact StatementResultMatchesFactsAfterSubstitution.returned childExtension
  have finalInvariant := boundary.invariant.of_retained_statement_typing boundary.accepted
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked) active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension (activeSchemeQuantifierIsolation_transport boundary.invariant.schemeIsolation bindersEq)
    typing
  exact ⟨target, _, finalInvariant, boundary.actual, operational, typing, agreement⟩

theorem statement_returnValue
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {expression : Syntax.Expr} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : statement.value = .returnStmt (some expression))
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target
      (selected.body.finalized.substitution.apply expectedReturn)) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  exact statement_returnValue_for (callProvenance := fun _ => True) checked true_childClosed
    (fun _ boundary => recursive boundary) True.intro form boundary returnSafe returnAdmissible

/-- The selected function signature supplies both return-input conditions
from actual checking. Lambda return inputs use their own fresh prefix. -/
theorem statement_function_returnValue
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {expression : Syntax.Expr} {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : statement.value = .returnStmt (some expression))
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      (Ty.productMany selected.signature.returnTypes) initial result frames target) :
    StatementConclusion selected inferenceContext (Ty.productMany selected.signature.returnTypes) result frames target := by
  let expectedReturn := Ty.productMany selected.signature.returnTypes
  have signatureParameters := selected.canonical checked
  have returnClosed : expectedReturn.VariablesBelow 0 := selected.returns_closed checked
  have declarationEq := (ProgramEnvironment.declaration?_sound selected.body.declared).2
  have baseFormed := (selected.header checked).return_types
  have resultTypes : TypesWellFormed target selected.signature.returnTypes :=
    StructuralSubstitution.TypesWellFormed.transportContext (RecursiveExpressionInvariant.ofStatement boundary.invariant).signatures_eq_whole
      boundary.invariant.typeParametersEq (by
        change target.currentDeclaration = some selected.signature.id
        simpa only [checkingContext, context, ProgramTypeScope.ofDeclaration, declarationEq, checkedBodyContext, declarationContext, Context.withResidualTypeVariables, Context.withSolvedRequirements, Context.withAssumptions, Context.forDeclaration]
          using boundary.invariant.declarationEq) baseFormed
  have returnFormed : TypeWellFormed target expectedReturn := {
    binders := (RecursiveExpressionInvariant.ofStatement boundary.invariant).typeParameterBinders
      (by simpa only [checkingContext, context, ProgramTypeScope.ofDeclaration, declarationEq] using signatureParameters)
    typeWellScoped := StructuralSubstitution.TypesWellScoped.productMany
      (StructuralSubstitution.TypesWellFormed.toTypesWellScoped resultTypes) }
  have returnFixed : selected.body.finalized.substitution.apply expectedReturn = expectedReturn :=
    Ty.apply_eq_self_of_domain_disjoint_freeVariables _ _
      (fun metavariable _ occurs => False.elim (Nat.not_lt_zero _ (returnClosed metavariable occurs)))
  have returnAdmissible : TypeAdmissible target
      (selected.body.finalized.substitution.apply expectedReturn) :=
    returnFixed.symm ▸ TypeAdmissible.ofWellFormed returnFormed
  exact statement_returnValue checked recursive form boundary
    (fun binder _ => ProtectedVariables.safe_closed _ _ returnClosed) returnAdmissible

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedSequenceReturnConnection
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness SourceInferenceExecution

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}

/-- The actual head statement derives the return privacy required by the tail. -/
theorem statements_cons_with_return_for
    {provenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed provenance)
    (headSound : StatementRootedSoundnessFor provenance selected childFuel)
    (tailSound : StatementsRootedSoundnessFor provenance selected childFuel)
    {inferenceContext : SourceInference.Context} {expectedReturn : Ty}
    {initial : State} {result : Detail.BlockResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    {statement next : Syntax.Statement} {rest : List Syntax.Statement}
    (here : provenance (.statements (childFuel + 1) inferenceContext
      (statement :: next :: rest) expectedReturn initial result))
    (returnSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (boundary : StatementsBoundary selected (childFuel + 1) inferenceContext
      (statement :: next :: rest) expectedReturn initial result frames target) :
    StatementsConclusion selected inferenceContext expectedReturn result frames target := by
  obtain ⟨head, tail, headAccepted, tailAccepted, resultEq⟩ :=
    inferStatementsFuel_success_cons_facts boundary.accepted
  subst result
  have headProperties := Detail.inferStatementFuel_inferenceProperties boundary.invariant.ready
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked)
    boundary.invariant.returnBelow headAccepted
  have tailProperties := Detail.inferStatementsFuel_inferenceProperties headProperties.2.1
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked)
    (boundary.invariant.returnBelow.weaken headProperties.1.next_le) tailAccepted
  have headBelow := (Detail.inferStatementFuel_occurrenceBoundExtends headAccepted
    ).nodesBelowNextOccurrence boundary.invariant.nodesBelow
  have headToTail := inferStatementsFuel_success_typingSourceExtends tailAccepted
    headBelow (bodyRoots selected)
  let headBoundary := ({
      accepted := headAccepted
      interfaces := boundary.interfaces
      extension := boundary.extension.trans tailProperties.1.substitution_extends
      scope := boundary.scope
      invariant := boundary.invariant
      actual := boundary.actual
      operational := boundary.operational
      rawSubtree := (boundary.rawSubtrees head.id (by simp)).monoBefore headToTail
      integerPatterns := (Detail.inferStatementsFuel_integerPatterns_subset tailAccepted).trans boundary.integerPatterns
      integerLiterals := (Detail.inferStatementsFuel_integerLiterals_subset tailAccepted).trans boundary.integerLiterals
      requirements := (Detail.inferStatementsFuel_requirements_subset tailAccepted).trans boundary.requirements
      covered := boundary.covered head.id (by simp)
      actualCovered := boundary.actualCovered head.id (by simp) } :
      StatementBoundary selected childFuel inferenceContext statement expectedReturn initial head frames target)
  obtain ⟨middle, headFacts, middleInvariant, middleActual, middleOperational, headTyping, headAgreement⟩ :=
    headSound (descend here (.statements_head boundary.accepted headAccepted))
      returnSafe returnAdmissible headBoundary
  have middleSafe := headBoundary.return_safe checked returnSafe
  have middleAdmissible : TypeAdmissible middle (selected.body.finalized.substitution.apply expectedReturn) :=
    StructuralSubstitution.TypeAdmissible.transportContext
      (middleInvariant.signaturesEq.trans boundary.invariant.signaturesEq.symm)
      (middleInvariant.typeParametersEq.trans boundary.invariant.typeParametersEq.symm)
      (middleInvariant.declarationEq.trans boundary.invariant.declarationEq.symm)
      (middleActual.variables_eq.trans boundary.actual.variables_eq.symm)
      (middleInvariant.residual.trans boundary.invariant.residual.symm) returnAdmissible
  have assumptionsEq := statementHasType_assumptions_eq headTyping
  have covered : ∀ id ∈ tail.statements,
      TemplateScopeCovered selected.body.finalized.typedSource middle (.statement id) := by
    intro id member owner scopes
    change owner.requirement.predicate ∈ middle.assumptions
    rw [assumptionsEq]
    exact boundary.covered id (by simp [member]) owner scopes
  obtain ⟨finalContext, tailFacts, invariant, actual, operational, tailTyping, tailAgreement⟩ :=
    tailSound (descend here (.statements_tail boundary.accepted (by simp) headAccepted tailAccepted))
      middleSafe middleAdmissible ({
      accepted := tailAccepted
      interfaces := boundary.interfaces
      extension := boundary.extension
      scope := boundary.scope
      invariant := middleInvariant
      actual := middleActual
      operational := middleOperational
      rawSubtrees := fun id member => boundary.rawSubtrees id (by simp [member])
      integerPatterns := boundary.integerPatterns
      integerLiterals := boundary.integerLiterals
      requirements := boundary.requirements
      covered
      actualCovered := fun id member => boundary.actualCovered id (by simp [member]) } :
      StatementsBoundary selected childFuel inferenceContext (next :: rest) expectedReturn
        head.state tail frames middle)
  obtain ⟨tailHead, tailRest, tailEq⟩ := inferStatementsFuel_success_statements_eq_cons tailAccepted
  have typing : StatementsHaveType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth }
      target (head.id :: tail.statements) finalContext (.cons headFacts tailFacts) := by
    rw [tailEq]
    exact .cons headTyping (by simpa [tailEq] using tailTyping)
  exact ⟨finalContext, .cons headFacts tailFacts, invariant, actual, operational, typing,
    BlockResultMatchesFactsAfterSubstitution.cons headAgreement tailAgreement⟩

theorem statementsRooted_zero : StatementsRootedSoundness selected 0 := by
  intro inferenceContext statements expectedReturn initial result frames target returnSafe returnAdmissible boundary
  have success := boundary.accepted
  simp only [Detail.inferStatementsFuel] at success
  cases success

/-- Source-order recursion consumes the smaller actual statement and block proofs. -/
theorem statementsRooted_step_for
    {provenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed provenance)
    (headSound : StatementRootedSoundnessFor provenance selected childFuel)
    (tailSound : StatementsRootedSoundnessFor provenance selected childFuel) :
    StatementsRootedSoundnessFor provenance selected (childFuel + 1) := by
  intro inferenceContext statements expectedReturn initial result frames target here returnSafe returnAdmissible boundary
  cases statements with
  | nil => exact statements_nil boundary
  | cons statement rest =>
    cases rest with
    | nil =>
        apply statements_singleton boundary
        intro head childBoundary
        exact headSound (descend here (.statements_head boundary.accepted childBoundary.accepted))
          returnSafe returnAdmissible childBoundary
    | cons next rest =>
        exact statements_cons_with_return_for checked descend headSound tailSound
          here returnSafe returnAdmissible boundary

theorem statementsRooted_zero_for {provenance : CallIndex → Prop} :
    StatementsRootedSoundnessFor provenance selected 0 := by
  intro context source expected initial result frames target _ safe admissible boundary
  exact statementsRooted_zero safe admissible boundary

theorem statements_cons_with_return
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (headSound : StatementRootedSoundness selected childFuel)
    (tailSound : StatementsRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {expectedReturn : Ty}
    {initial : State} {result : Detail.BlockResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    {statement next : Syntax.Statement} {rest : List Syntax.Statement}
    (returnSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (boundary : StatementsBoundary selected (childFuel + 1) inferenceContext
      (statement :: next :: rest) expectedReturn initial result frames target) :
    StatementsConclusion selected inferenceContext expectedReturn result frames target := by
  exact statements_cons_with_return_for (provenance := fun _ => True) checked true_childClosed
    (by
      intro context source expected initial result frames target _ safe admissible boundary
      exact headSound safe admissible boundary)
    (by
      intro context source expected initial result frames target _ safe admissible boundary
      exact tailSound safe admissible boundary) trivial returnSafe returnAdmissible boundary

theorem statementsRooted_step
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (headSound : StatementRootedSoundness selected childFuel)
    (tailSound : StatementsRootedSoundness selected childFuel) :
    StatementsRootedSoundness selected (childFuel + 1) := by
  intro context source expected initial result frames target safe admissible boundary
  exact statementsRooted_step_for (provenance := fun _ => True) checked true_childClosed
    (by
      intro context source expected initial result frames target _ safe admissible boundary
      exact headSound safe admissible boundary)
    (by
      intro context source expected initial result frames target _ safe admissible boundary
      exact tailSound safe admissible boundary) trivial safe admissible boundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedValueAssignment
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution SourceInferenceStatementsSoundness

theorem statement_assignValue_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {provenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed provenance)
    (placeSound : PlaceRootedSoundnessFor provenance selected childFuel)
    (expressionSound : ExpressionRootedSoundnessFor provenance selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {targetExpression value : Syntax.Expr} {operator : Syntax.Located Syntax.ValueAssignOp}
    {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : provenance (.statement (childFuel + 1) inferenceContext statement expectedReturn initial result))
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
  obtain ⟨assignmentTyped, assignmentOperational⟩ := assignedValue_of_actual_children_for checked descend placeSound expressionSound
    (descend here (ChildStep.statement_assignment boundary.accepted form rfl assignmentAccepted)) ({
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
  exact statement_assignValue_for (provenance := fun _ => True) checked true_childClosed
    (fun _ boundary => placeSound boundary) (fun _ boundary => expressionSound boundary) trivial form boundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end
