import Solcore.SourceSemantics.SourceInferenceSelectedAssignmentChildren
import Solcore.SourceSemantics.SourceInferenceSelectedStatementReferences

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

theorem actualInferStatementFuelRootedSoundness_assignValue {fuel : Nat}
    (placeSound : ActualInferPlaceFuelRootedSoundness fuel)
    (expressionSound : ActualInferExprFuelRootedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {targetExpression value : Syntax.Expr}
    {operator : Syntax.Located Syntax.ValueAssignOp} {initial : State}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    statement.value = .assignValue targetExpression operator value →
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
  intro wholeContext inferenceContext wholeReturn expectedReturn statement targetExpression value operator initial result
    evidenceState roots finalized semanticSource frames semanticContext statementEq success resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical invariant actual operational
    _returnAdmissible extension _semantic raw patterns literals requirements covered actualCovered
  generalize allocationEq : initial.allocateStatementId = pair
  obtain ⟨id, allocated⟩ := pair
  have allocatedInvariant := invariant.allocateStatementId allocationEq
  have allocatedOperational := operational.allocateStatementId allocationEq
  obtain ⟨assignment, inferred, assignmentState, assignmentSuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_assignValue_facts statementEq allocationEq success roots
  have assignedToParent : TypingSourceExtends (assignmentState.toTypedSource roots) (result.state.toTypedSource roots) := by
    rw [resultEq]
    exact ⟨rfl, State.recordNode_nodesPrefix _ _⟩
  have assignedExtension : finalized.substitution.SemanticallyExtends assignmentState.inference.substitution := by
    simpa only [resultEq, State.recordNode] using extension
  have final := raw.finalized resources
  have reference : ∀ key, .expression key ∈ assignment.references →
      (.expression key : NodeId) ∈ (StatementForm.assignValue assignment operator.value inferred.id).references := by
    intro key member
    simp only [StatementForm.references]
    exact List.mem_append_left _ member
  have keysCovered : ∀ key, .expression key ∈ assignment.references →
      TemplateScopeCovered finalized.typedSource semanticContext (.expression key) := by
    intro key member
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference covered resources.graph_closed
      (final.containsStatement contains)
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, statementInitializedLetBindings]
    · simpa [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references,
        AssignmentResolution.references, AssignmentResolution.applySubstitution, PlaceResolution.applySubstitution,
        PlaceResolution.references] using reference key member
  have rhsCovered : TemplateScopeCovered finalized.typedSource semanticContext (.expression inferred.id) := by
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference covered resources.graph_closed
      (final.containsStatement contains)
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, statementInitializedLetBindings]
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references]
  obtain ⟨placeTyped, valueTyped⟩ := actualInferAssignedValueFuel_children_rootedSound assignmentSuccess resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical
    (RecursiveExpressionInvariant.ofStatement allocatedInvariant) actual allocatedOperational assignedExtension assignedToParent
    (fun key member => raw.child (directChild_statement_reference contains (reference key member)))
    (raw.child (directChild_statement_reference contains (by simp [StatementForm.references])))
    (by simpa only [resultEq, State.recordNode] using patterns)
    (by simpa only [resultEq, State.recordNode] using literals)
    (by simpa only [resultEq, State.recordNode] using requirements)
    keysCovered rhsCovered
    (fun key member => actualCovered.preserved_statement_reference contains final (reference key member))
    (actualCovered.preserved_statement_reference contains final (by simp [StatementForm.references])) placeSound expressionSound
  obtain ⟨active, typing, agreement⟩ := inferStatementFuel_success_assignValue_sound_of_typed_children
    statementEq allocationEq success assignmentSuccess invariant.ready formation functions invariant.active extension roots
    placeTyped valueTyped
  have bindersEq : result.state.localBinders = initial.localBinders := by
    have assignedBinders := congrArg LexicalScope.binders (Detail.inferAssignedValueFuel_success_lexicalScope_eq assignmentSuccess)
    have allocatedBinders := congrArg LexicalScope.binders (Detail.allocateStatementId_success_lexicalScope allocationEq)
    simpa only [resultEq, State.recordNode, State.lexicalScope] using assignedBinders.trans allocatedBinders
  have properties := Detail.inferStatementFuel_inferenceProperties invariant.ready formation functions invariant.returnBelow success
  have finalInvariant := invariant.of_statement_typing success formation functions active
    (inferStatementFuel_preserves_localBindersBelowNextLocal invariant.bindersBelow success) extension
    (activeSchemeQuantifierIsolation_transport invariant.schemeIsolation bindersEq) typing
  exact ⟨semanticContext, _, finalInvariant, actual, operational.ofStatementPreservingBinders success bindersEq
    properties.1.next_le, typing, agreement⟩

theorem actualInferStatementFuelRootedSoundness_assignBitNot {fuel : Nat}
    (placeSound : ActualInferPlaceFuelRootedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {targetExpression : Syntax.Expr} {operatorSpan : Syntax.SourceSpan} {initial : State}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    statement.value = .assignBitNot targetExpression operatorSpan →
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
  intro wholeContext inferenceContext wholeReturn expectedReturn statement targetExpression operatorSpan initial result
    evidenceState roots finalized semanticSource frames semanticContext statementEq success resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical invariant actual operational
    _returnAdmissible extension _semantic raw patterns literals requirements covered actualCovered
  generalize allocationEq : initial.allocateStatementId = pair
  obtain ⟨id, allocated⟩ := pair
  have allocatedInvariant := invariant.allocateStatementId allocationEq
  have allocatedOperational := operational.allocateStatementId allocationEq
  obtain ⟨place, placeState, unified, placeSuccess, unifySuccess, _, resultEq, contains⟩ :=
    inferStatementFuel_success_assignBitNot_facts statementEq allocationEq success roots
  have placeToParent : TypingSourceExtends (placeState.toTypedSource roots) (result.state.toTypedSource roots) := by
    constructor
    · change result.state.owner = placeState.owner
      rw [resultEq]
      exact congrArg State.Header.owner (Detail.unify_state_header unifySuccess)
    · change placeState.nodes <+: result.state.nodes
      rw [resultEq]
      change placeState.nodes <+: (unified.recordNode _).nodes
      rw [← (Detail.unify_occurrenceState_eq unifySuccess).1]
      exact State.recordNode_nodesPrefix _ _
  have placeProperties := Detail.inferPlaceFuel_inferenceProperties allocatedInvariant.ready formation functions placeSuccess
  have unifiedExtension : finalized.substitution.SemanticallyExtends unified.inference.substitution := by
    simpa only [resultEq, State.recordNode] using extension
  have placeExtension := unifiedExtension.trans
    (Detail.unify_inferenceProgress placeProperties.2.1.solved placeProperties.2.2
      (Ty.variablesBelow_constructor _ _) unifySuccess).substitution_extends
  have final := raw.finalized resources
  have reference : ∀ key, .expression key ∈ place.references →
      (.expression key : NodeId) ∈ (StatementForm.assignBitNot
        { target := { place with type := unified.resolve place.type }}).references := by
    intro key member
    simpa [StatementForm.references, AssignmentResolution.references, PlaceResolution.references] using member
  have keysCovered : ∀ key, .expression key ∈ place.references →
      TemplateScopeCovered finalized.typedSource semanticContext (.expression key) := by
    intro key member
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference covered resources.graph_closed
      (final.containsStatement contains)
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, statementInitializedLetBindings]
    · simpa [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references,
        AssignmentResolution.references, AssignmentResolution.applySubstitution, PlaceResolution.applySubstitution,
        PlaceResolution.references] using reference key member
  have placePatterns : placeState.integerPatterns ⊆ evidenceState.integerPatterns := by
    simpa only [resultEq, State.recordNode, Detail.unify_integerPatterns unifySuccess] using patterns
  have placeLiterals : placeState.integerLiterals ⊆ evidenceState.integerLiterals := by
    simpa only [resultEq, State.recordNode, Detail.unify_integerLiterals unifySuccess] using literals
  have placeRequirements : placeState.requirements ⊆ evidenceState.requirements := by
    simpa only [resultEq, State.recordNode, Detail.unify_requirements_eq unifySuccess] using requirements
  have placeTyped := placeSound placeSuccess resources interfaces signaturesEq ownerEq parametersEq assumptionsEq
    formation functions catalog canonical (RecursiveExpressionInvariant.ofStatement allocatedInvariant) actual allocatedOperational
    placeExtension placeToParent
    (fun key member => raw.child (directChild_statement_reference contains (reference key member)))
    placePatterns placeLiterals placeRequirements keysCovered
    (fun key member => actualCovered.preserved_statement_reference contains final (reference key member))
  obtain ⟨active, typing, agreement⟩ := inferStatementFuel_success_assignBitNot_sound_of_actual_child
    statementEq allocationEq success invariant.active extension roots placeSuccess placeTyped
  have bindersEq : result.state.localBinders = initial.localBinders := by
    have placeBinders := congrArg LexicalScope.binders (Detail.inferPlaceFuel_success_lexicalScope_eq placeSuccess)
    have unifiedBinders := congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope unifySuccess)
    have allocatedBinders := congrArg LexicalScope.binders (Detail.allocateStatementId_success_lexicalScope allocationEq)
    simpa only [resultEq, State.recordNode, State.lexicalScope] using unifiedBinders.trans (placeBinders.trans allocatedBinders)
  have properties := Detail.inferStatementFuel_inferenceProperties invariant.ready formation functions invariant.returnBelow success
  have finalInvariant := invariant.of_statement_typing success formation functions active
    (inferStatementFuel_preserves_localBindersBelowNextLocal invariant.bindersBelow success) extension
    (activeSchemeQuantifierIsolation_transport invariant.schemeIsolation bindersEq) typing
  exact ⟨semanticContext, _, finalInvariant, actual, operational.ofStatementPreservingBinders success bindersEq
    properties.1.next_le, typing, agreement⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
