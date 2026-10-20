import Solcore.SourceSemantics.SourceCompiledGeneralizedBlockStatement

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness

theorem statement_if_with_else
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}
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
  obtain ⟨bodyContext, bodyFacts, bodyInvariant, _, bodyOperational, bodyTyping, bodyAgreement⟩ :=
    recursiveBody bodyReturnSafe returnAdmissible ({
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
    recursiveBody elseReturnSafe returnAdmissible ({
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

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
