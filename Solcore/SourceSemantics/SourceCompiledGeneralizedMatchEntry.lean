import Solcore.SourceSemantics.SourceCompiledGeneralizedScrutineeTyping
import Solcore.SourceSemantics.SourceCompiledGeneralizedMatchCases
import Solcore.SourceSemantics.SourceInferenceGeneralizedScrutineeState
import Solcore.SourceSemantics.SourceInferenceSelectedMatchScrutineeScope

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness ProtectedVariables

theorem matchEntry
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}
    (checkedProgram : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundness selected smaller)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders, Safe binder.scheme.quantified initial expectedReturn)
    {scrutinee : InferredExpression} {scrutineeState hiddenState : State}
    {hiddenScrutinee : Resolved.LocalId} {checked : Detail.MatchCasesResult}
    {defaultBody : Option (List StatementId)}
    (scrutineeAccepted : inferMatchScrutineesFuel childFuel inferenceContext statement.span
      scrutinees.elements.toList initial.allocateStatementId.2 = .ok (scrutinee, scrutineeState))
    (hiddenAllocation : scrutineeState.allocateHiddenLocal = (hiddenScrutinee, hiddenState))
    (casesAccepted : Detail.inferMatchCasesFuel childFuel inferenceContext scrutinee.type expectedReturn
      hiddenState.lexicalScope arms.value.cases hiddenState = .ok checked)
    (casesExtension : selected.body.finalized.substitution.SemanticallyExtends checked.state.inference.substitution)
    (casesSource : TypingSourceExtends (checked.state.toTypedSource (bodyRoots selected))
      (result.state.toTypedSource (bodyRoots selected)))
    (patterns : checked.state.integerPatterns ⊆ selected.body.returned.integerPatterns)
    (literals : checked.state.integerLiterals ⊆ selected.body.returned.integerLiterals)
    (requirements : checked.state.requirements ⊆ selected.body.returned.requirements)
    (contains : ContainsStatement (result.state.toTypedSource (bodyRoots selected)) result.id {
      id := result.id, span := statement.span, type := result.type, form := .matchWith {
        scrutinee := scrutinee.id, hiddenScrutinee, cases := checked.cases, defaultBody,
        requirements := checked.cases.flatMap (·.pattern.requirements) } }) :
    MatchCasesBoundary selected childFuel inferenceContext arms.value.cases scrutinee.type expectedReturn
      hiddenState hiddenState.lexicalScope checked frames target (.statement result.id) ∧
    ExpressionHasType selected.body.finalized.typedSource target scrutinee.id
      (selected.body.finalized.substitution.apply scrutinee.type) ∧
    Safe (activeSchemeQuantifiers hiddenState) hiddenState expectedReturn := by
  have resources := selected.body.resources
  have formation := boundary.scope.formation checkedProgram
  have canonical := boundary.scope.functionsCanonical checkedProgram
  have catalog := boundary.scope.catalog checkedProgram
  have allocatedInvariant := boundary.invariant.allocateStatementId rfl
  have allocatedOperational := boundary.operational.allocateStatementId
  have properties := inferMatchScrutineesFuel_inferenceProperties allocatedInvariant.ready
    formation canonical scrutineeAccepted
  have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState := congrArg Prod.snd hiddenAllocation
  have hiddenReady : hiddenState.InferenceReady := by
    rw [← hiddenEq]
    exact properties.2.1.allocateHiddenLocal
  have scrutineeBelow : scrutinee.type.VariablesBelow hiddenState.inference.next := by
    rw [← hiddenEq]
    exact properties.2.2
  have returnBelow : expectedReturn.VariablesBelow hiddenState.inference.next := by
    rw [← hiddenEq]
    exact allocatedInvariant.returnBelow.weaken properties.1.next_le
  have casesProperties := Detail.inferMatchCasesFuel_inferenceProperties hiddenReady formation canonical
    scrutineeBelow returnBelow rfl casesAccepted
  have hiddenExtension := casesExtension.trans casesProperties.1.substitution_extends
  have scrutineeExtension : selected.body.finalized.substitution.SemanticallyExtends
      scrutineeState.inference.substitution := by
    rw [← hiddenEq] at hiddenExtension
    exact hiddenExtension
  have scrutineeNodes := inferMatchScrutineesFuel_success_nodesBelow scrutineeAccepted allocatedInvariant.nodesBelow
  have hiddenNodes : hiddenState.NodesBelowNextOccurrence := by
    rw [← hiddenEq]
    exact State.allocateHiddenLocal_preserves_nodesBelowNextOccurrence _ scrutineeNodes
  have hiddenBinders : hiddenState.localBinders = initial.localBinders := by
    rw [← hiddenEq]
    exact congrArg LexicalScope.binders (inferMatchScrutineesFuel_success_lexicalScope_eq scrutineeAccepted)
  have hiddenInvariant : RecursiveStatementInvariant (checkingContext selected) expectedReturn
      selected.body.finalized hiddenState target := {
    boundary.invariant with
    active := allocatedInvariant.active.inferMatchScrutineesFuel scrutineeAccepted |>.allocateHiddenLocal hiddenAllocation
    ready := hiddenReady
    returnBelow := returnBelow
    bindersBelow := by
      rw [← hiddenEq]
      exact State.allocateHiddenLocal_preserves_localBindersBelowNextLocal _
        (inferMatchScrutineesFuel_preserves_localBindersBelowNextLocal allocatedInvariant.bindersBelow scrutineeAccepted)
    nodesBelow := hiddenNodes
    schemeIsolation := activeSchemeQuantifierIsolation_transport boundary.invariant.schemeIsolation hiddenBinders
    substitutionExtension := hiddenExtension }
  have scrutineeOperational := allocatedOperational.ofMatchScrutinees allocatedInvariant.ready catalog formation canonical
    scrutineeAccepted
  have hiddenOperational : GeneralizedActualStateInvariant hiddenState (evidenceSource selected) := by
    rw [← hiddenEq]
    exact scrutineeOperational.1.allocateHiddenLocal
  have scrutineeSafe : Safe (activeSchemeQuantifiers hiddenState) hiddenState scrutinee.type := by
    rw [← hiddenEq]
    exact scrutineeOperational.2
  have hiddenReturnSafe : Safe (activeSchemeQuantifiers hiddenState) hiddenState expectedReturn := by
    have privacy := allocatedOperational.scrutinees_safe_transport allocatedInvariant.ready catalog formation canonical
      scrutineeAccepted
    have beforeSafe : Safe (activeSchemeQuantifiers initial.allocateStatementId.2)
        initial.allocateStatementId.2 expectedReturn := safe_active_iff.mpr returnSafe
    have afterSafe := privacy expectedReturn beforeSafe
    change Safe (activeSchemeQuantifiers hiddenState) hiddenState expectedReturn
    simp only [activeSchemeQuantifiers, hiddenBinders]
    rw [← hiddenEq]
    exact afterSafe
  have scrutineeToHidden : TypingSourceExtends (scrutineeState.toTypedSource (bodyRoots selected))
      (hiddenState.toTypedSource (bodyRoots selected)) := by
    rw [← hiddenEq]
    exact ⟨rfl, List.prefix_rfl⟩
  have scrutineeSource := scrutineeToHidden.trans
    ((inferMatchCasesFuel_success_typingSourceExtends casesAccepted hiddenNodes (bodyRoots selected)).trans casesSource)
  have scrutineeReference : (.expression scrutinee.id : NodeId) ∈ (StatementForm.matchWith {
        scrutinee := scrutinee.id, hiddenScrutinee, cases := checked.cases, defaultBody,
        requirements := checked.cases.flatMap (·.pattern.requirements) }).references := by
    simp [StatementForm.references, MatchResolution.references]
  have scrutineePatterns : scrutineeState.integerPatterns ⊆ checked.state.integerPatterns := by
    have rows := Detail.inferMatchCasesFuel_integerPatterns_subset casesAccepted
    simpa [← hiddenEq] using rows
  have scrutineeLiterals : scrutineeState.integerLiterals ⊆ checked.state.integerLiterals := by
    have rows := Detail.inferMatchCasesFuel_integerLiterals_subset casesAccepted
    simpa [← hiddenEq] using rows
  have scrutineeRequirements : scrutineeState.requirements ⊆ checked.state.requirements := by
    have rows := Detail.inferMatchCasesFuel_requirements_subset casesAccepted
    simpa [← hiddenEq] using rows
  have finalContains := (boundary.rawSubtree.finalized resources).containsStatement contains
  have typed := scrutineeRooted checkedProgram recursive ({
    accepted := scrutineeAccepted
    interfaces := boundary.interfaces, extension := scrutineeExtension, scope := boundary.scope
    invariant := RecursiveExpressionInvariant.ofStatement allocatedInvariant
    actual := boundary.actual, operational := allocatedOperational
    rawSubtree := (boundary.rawSubtree.child (directChild_statement_reference contains scrutineeReference)).monoBefore scrutineeSource
    integerPatterns := scrutineePatterns.trans patterns, integerLiterals := scrutineeLiterals.trans literals
    requirements := scrutineeRequirements.trans requirements
    covered := by
      apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference boundary.covered resources.graph_closed finalContains
      · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, statementInitializedLetBindings]
      · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, MatchResolution.applySubstitution,
          StatementForm.references, MatchResolution.references]
    actualCovered := boundary.actualCovered.preserved_statement_reference contains
      (boundary.rawSubtree.finalized resources) scrutineeReference } : ScrutineeBoundary selected childFuel
        inferenceContext statement.span scrutinees.elements.toList initial.allocateStatementId.2 scrutinee scrutineeState frames target)
  have reference : ∀ arm ∈ checked.cases, ∀ child ∈ arm.body,
      (.statement child : NodeId) ∈ (StatementForm.matchWith {
        scrutinee := scrutinee.id, hiddenScrutinee, cases := checked.cases, defaultBody,
        requirements := checked.cases.flatMap (·.pattern.requirements) }).references := by
    intro arm present child member
    simp only [StatementForm.references, MatchResolution.references]
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨arm, present, by simpa [TypedMatchCase.references] using
      (List.mem_map.mpr ⟨child, member, rfl⟩ : NodeId.statement child ∈ arm.body.map NodeId.statement)⟩
  have owner : hiddenState.owner = (checkingContext selected).scope.genericOwner := by
    have evidenceOwner : (evidenceSource selected).owner = (checkingContext selected).scope.genericOwner := by
      exact (congrArg State.Header.owner (Detail.unify_state_header selected.body.unified)).trans
        (Detail.inferStatementsFuel_preserves_owner selected.body.inferred)
    exact (Detail.inferMatchCasesFuel_preserves_owner casesAccepted).symm.trans
      (casesSource.owner_eq.symm.trans (boundary.rawSubtree.owner_eq.symm.trans evidenceOwner))
  refine ⟨{
    accepted := casesAccepted, interfaces := boundary.interfaces, extension := casesExtension
    scope := boundary.scope, invariant := hiddenInvariant, actual := boundary.actual, operational := hiddenOperational
    owner := owner, lexicalScope := rfl, scrutineeBelow := scrutineeBelow
    scrutineeAdmissible := typed.type_admissible, scrutineeSafe := scrutineeSafe
    integerPatterns := patterns, integerLiterals := literals, requirements := requirements
    patternCovered := boundary.covered
    patternOccurs := ?_
    rawSubtrees := fun arm present child member =>
      (boundary.rawSubtree.child (directChild_statement_reference contains (reference arm present child member))).monoBefore casesSource
    covered := ?_
    actualCovered := fun arm present child member => boundary.actualCovered.preserved_statement_reference contains
      (boundary.rawSubtree.finalized resources) (reference arm present child member) }, typed, hiddenReturnSafe⟩
  · intro arm present requirement member
    exact finalContains.matchCasePatternRequirementOccursAt rfl
      (List.mem_map.mpr ⟨arm, present, rfl⟩) (by
        simpa [TypedMatchCase.applySubstitution, TypedMatchPattern.applySubstitution] using member)
  · intro arm present child member
    exact TemplateScopeCovered.statementChild boundary.covered resources.graph_closed
      ((boundary.rawSubtree.finalized resources).directChild
        (directChild_statement_reference contains (reference arm present child member))) (fun _ member => member)

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
