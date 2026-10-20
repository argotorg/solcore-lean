import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedBlockStatement

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness

theorem statement_while
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursiveExpression : ExpressionRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {condition : Syntax.Expr} {body : Syntax.Block} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : statement.value = .whileLoop condition body)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (recursiveBody : ∀ {bodyInitial : State} {bodyResult : Detail.BlockResult},
      (∀ binder ∈ bodyInitial.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified bodyInitial expectedReturn) →
      TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn) →
      StatementsBoundary selected childFuel {inferenceContext with loopDepth := inferenceContext.loopDepth + 1} body.value expectedReturn
        bodyInitial bodyResult frames target →
      StatementsConclusion selected {inferenceContext with loopDepth := inferenceContext.loopDepth + 1} expectedReturn bodyResult frames target) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  have resources := selected.body.resources
  have formation := boundary.scope.formation checked
  have canonical := boundary.scope.functionsCanonical checked
  have catalog := boundary.scope.catalog checked
  have allocatedInvariant := boundary.invariant.allocateStatementId rfl
  have allocatedOperational := boundary.operational.allocateStatementId
  obtain ⟨conditionValue, conditionState, bodyResult, conditionAccepted, bodyAccepted,
      resultEq, containsRaw⟩ :=
    inferStatementFuel_success_whileLoop_facts form rfl boundary.accepted (bodyRoots selected)
  obtain ⟨otherState, otherBody, ⟨otherCondition, otherAccepted⟩, otherBodyAccepted,
      _, bodyExtension, bodyPatterns, bodyRequirements⟩ :=
    inferStatementFuel_success_whileLoop_child_provenance form rfl boundary.accepted
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
  have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
    (context := {inferenceContext with loopDepth := inferenceContext.loopDepth + 1}) conditionProperties.2.1
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
  have conditionTyping := recursiveExpression ({
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
    recursiveBody bodyReturnSafe returnAdmissible ({
    accepted := bodyAccepted
    interfaces := boundary.interfaces
    extension := bodySubstitution
    scope := boundary.scope.withLoopDepth (inferenceContext.loopDepth + 1)
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
    StatementsBoundary selected childFuel {inferenceContext with loopDepth := inferenceContext.loopDepth + 1} body.value expectedReturn
      conditionState bodyResult frames target)
  let facts : StatementFacts := {
    type := .unit, hasValue := false, sawReturn := false,
    control := .loop bodyFacts.control }
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
    exact .whileLoop containsFinal rfl conditionBool bodyTyping
      (by simp [StatementNode.applySubstitution, resultEq])
  have agreement : StatementResultMatchesFactsAfterSubstitution
      selected.body.finalized.substitution result facts := by
    rw [resultEq]
    exact StatementResultMatchesFactsAfterSubstitution.whileLoop _ bodyFacts _ _
  have conditionBinders := congrArg LexicalScope.binders
    (Detail.inferExprFuel_success_lexicalScope_eq conditionAccepted)
  have bindersEq : result.state.localBinders = initial.localBinders := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode, State.lexicalScope] using conditionBinders
  have finalInvariant := boundary.invariant.of_retained_statement_typing boundary.accepted formation canonical active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension (activeSchemeQuantifierIsolation_transport boundary.invariant.schemeIsolation bindersEq) typing
  exact ⟨target, facts, finalInvariant, boundary.actual, operational, typing, agreement⟩

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
