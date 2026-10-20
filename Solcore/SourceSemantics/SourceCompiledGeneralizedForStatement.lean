import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedForSequence
import Solcore.SourceSemantics.SourceCompiledGeneralizedStatementsContracts
import Solcore.SourceSemantics.SourceInferenceGeneralizedStatementState
import Solcore.SourceSemantics.SourceInferenceGeneralizedStatementRecording
import Solcore.SourceSemantics.SourceInferenceStatementForLoopChildProgress
import Solcore.SourceSemantics.SourceInferenceSelectedForLoopCoverage

/-! The complete for-loop consumer follows the actual initializer, condition,
body and post calls. The initializer's return-type privacy is kept explicit
until its producer for newly generalized declarations is assembled. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness SourceInferenceExecution

theorem statement_for_of_initializer_privacy_for {callProvenance : CallIndex → Prop}
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursiveItems : ForItemsRootedSoundnessFor callProvenance selected childFuel)
    (recursiveExpression : ExpressionRootedSoundnessFor callProvenance selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {headerSpan : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
    {condition : Syntax.Expr} {body : Syntax.Block} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.statement (childFuel + 1) inferenceContext statement expectedReturn initial result))
    (form : statement.value = .forLoop headerSpan initializer condition post body)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (initializerPrivacy : ∀ {actualInitializer : Detail.InferredForItems},
      Detail.inferForItemsFuel childFuel inferenceContext initializer initial.allocateStatementId.2 = .ok actualInitializer →
      ∀ binder ∈ actualInitializer.state.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified actualInitializer.state expectedReturn)
    (recursiveBody : ∀ {bodyInitial : State} {bodyResult : Detail.BlockResult}
      {loopContext : SourceSemantics.Context},
      callProvenance (.statements childFuel {inferenceContext with loopDepth := inferenceContext.loopDepth + 1}
        body.value expectedReturn bodyInitial bodyResult) →
      (∀ binder ∈ bodyInitial.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified bodyInitial expectedReturn) →
      TypeAdmissible loopContext (selected.body.finalized.substitution.apply expectedReturn) →
      StatementsBoundary selected childFuel {inferenceContext with loopDepth := inferenceContext.loopDepth + 1} body.value expectedReturn
        bodyInitial bodyResult frames loopContext →
      StatementsConclusion selected {inferenceContext with loopDepth := inferenceContext.loopDepth + 1} expectedReturn bodyResult frames loopContext) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  have resources := selected.body.resources
  have formation := boundary.scope.formation checked
  have canonical := boundary.scope.functionsCanonical checked
  have catalog := boundary.scope.catalog checked
  have allocatedInvariant := boundary.invariant.allocateStatementId rfl
  have allocatedOperational := boundary.operational.allocateStatementId
  have resultExtension := boundary.rawSubtree.finalized resources
  obtain ⟨initializerResult, inferredCondition, conditionState, bodyResult,
    postResult, initializerSuccess, conditionSuccess, bodySuccess,
    postSuccess, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_forLoop_facts form rfl boundary.accepted
      (bodyRoots selected)
  obtain ⟨progressInitializer, progressCondition, progressConditionState,
    progressBody, progressPost, progressInitializerSuccess,
    progressConditionSuccess, progressBodySuccess, progressPostSuccess,
    initializerSubstitutionExtension, conditionSubstitutionExtension,
    bodySubstitutionExtension, postSubstitutionExtension,
    initializerLiteralsParent, conditionLiteralsParent,
    bodyLiteralsParent, postLiteralsParent⟩ :=
    inferStatementFuel_success_forLoop_child_progress form
      rfl boundary.accepted formation canonical
      boundary.invariant boundary.extension
  rw [initializerSuccess] at progressInitializerSuccess
  have progressInitializerEq :=
    (Except.ok.inj progressInitializerSuccess).symm
  subst progressInitializer
  rw [conditionSuccess] at progressConditionSuccess
  obtain ⟨rfl, rfl⟩ :=
    (Except.ok.inj progressConditionSuccess).symm
  rw [bodySuccess] at progressBodySuccess
  have progressBodyEq := (Except.ok.inj progressBodySuccess).symm
  subst progressBody
  rw [postSuccess] at progressPostSuccess
  have progressPostEq := (Except.ok.inj progressPostSuccess).symm
  subst progressPost
  obtain ⟨provenanceInitializer, provenanceCondition,
    provenanceConditionState, provenanceBody, provenancePost,
    provenanceInitializerSuccess, provenanceConditionSuccess,
    provenanceBodySuccess, provenancePostSuccess,
    initializerProvenance, bodyProvenance, postProvenance⟩ :=
    inferStatementFuel_success_forLoop_child_provenance form
      rfl boundary.accepted boundary.invariant.nodesBelow (bodyRoots selected)
  rw [initializerSuccess] at provenanceInitializerSuccess
  have provenanceInitializerEq :=
    (Except.ok.inj provenanceInitializerSuccess).symm
  subst provenanceInitializer
  rw [conditionSuccess] at provenanceConditionSuccess
  obtain ⟨rfl, rfl⟩ :=
    (Except.ok.inj provenanceConditionSuccess).symm
  rw [bodySuccess] at provenanceBodySuccess
  have provenanceBodyEq := (Except.ok.inj provenanceBodySuccess).symm
  subst provenanceBody
  rw [postSuccess] at provenancePostSuccess
  have provenancePostEq := (Except.ok.inj provenancePostSuccess).symm
  subst provenancePost
  have containsFinal := resultExtension.containsStatement containsRaw
  have headerCovered := forItemsReferencesCovered_of_rootedForLoop
    containsRaw rfl resultExtension resources.graph_closed boundary.covered
  have headerBindings := forItemsBindingsRetained_of_containedForLoop
    (boundary.rawSubtree.containsStatement containsRaw) ⟨rfl, ⟨[], by simp⟩⟩
  have headerActualBindings := actualForItemsBindings_of_rootedForLoop
    containsRaw resultExtension boundary.actualCovered
  have initializerReference : ∀ item ∈ initializerResult.items, ∀ reference ∈ item.references,
      reference ∈ (StatementForm.forLoop initializerResult.items inferredCondition.id postResult.items bodyResult.statements).references := by
    intro item member reference present
    simp only [StatementForm.references, List.mem_append, List.mem_cons]
    exact .inl (.inl (.inl (List.mem_flatMap.mpr ⟨item, member, present⟩)))
  have postReference : ∀ item ∈ postResult.items, ∀ reference ∈ item.references,
      reference ∈ (StatementForm.forLoop initializerResult.items inferredCondition.id postResult.items bodyResult.statements).references := by
    intro item member reference present
    simp only [StatementForm.references, List.mem_append, List.mem_cons]
    exact .inl (.inr (List.mem_flatMap.mpr ⟨item, member, present⟩))
  have initializerOwner : selected.body.finalized.typedSource.owner = initial.allocateStatementId.2.owner := by
    have retained := resultExtension.owner_eq
    have parentOwner := Detail.inferStatementFuel_preserves_owner boundary.accepted
    have allocatedOwner := congrArg (fun header : State.Header => header.owner)
      (State.allocateStatementId_header initial)
    exact retained.trans (parentOwner.trans allocatedOwner.symm)
  obtain ⟨loopContext, initializerInvariant, initializerActual, initializerOperational, initializerTyping⟩ :=
    recursiveItems (descend here (.statement_for_initializer boundary.accepted form rfl initializerSuccess)) ({
      accepted := initializerSuccess
      interfaces := boundary.interfaces
      extension := initializerSubstitutionExtension
      scope := boundary.scope
      invariant := allocatedInvariant
      actual := boundary.actual
      operational := allocatedOperational
      rawReferences := fun item member reference present =>
        (boundary.rawSubtree.child (directChild_statement_reference containsRaw
          (initializerReference item member reference present))).monoBefore initializerProvenance.sourceExtension
      integerPatterns := List.Subset.trans initializerProvenance.integerPatternsSubset boundary.integerPatterns
      integerLiterals := List.Subset.trans initializerLiteralsParent boundary.integerLiterals
      requirements := List.Subset.trans initializerProvenance.requirementsSubset boundary.requirements
      owner := initializerOwner
      covered := headerCovered.1
      bindingsRetained := headerBindings.1
      actualCovered := fun item member reference present =>
        boundary.actualCovered.preserved_statement_reference containsRaw resultExtension
          (initializerReference item member reference present)
      actualBindings := headerActualBindings.1 } :
      ForItemsBoundary selected childFuel inferenceContext initializer expectedReturn
        initial.allocateStatementId.2 initializerResult frames target)
  have loopAssumptions : loopContext.assumptions = target.assumptions :=
    forItemsHaveType_assumptions_eq initializerTyping
  have conditionExpected : ∀ type ∈ some Ty.bool,
      type.VariablesBelow initializerResult.state.inference.next := by
    intro type member
    cases member
    exact Ty.variablesBelow_constructor _ _
  have conditionSafe : ∀ binder ∈ initializerResult.state.localBinders, ∀ type ∈ some Ty.bool,
      ProtectedVariables.Safe binder.scheme.quantified initializerResult.state type := by
    intro binder _ type member
    cases member
    exact ProtectedVariables.safe_closed _ _ (Ty.variablesBelow_constructor _ _)
  have conditionProperties := Detail.inferExprFuel_inferenceProperties initializerInvariant.ready
    formation canonical conditionExpected conditionSuccess
  have conditionInvariant := initializerInvariant.inferExprFuel conditionSuccess formation canonical
    conditionExpected conditionSubstitutionExtension
  have conditionOperational := initializerOperational.ofExpression initializerInvariant.ready
    catalog formation canonical conditionExpected conditionSafe conditionSuccess
  have conditionSource := (inferStatementsFuel_success_typingSourceExtends bodySuccess
    conditionInvariant.nodesBelow (bodyRoots selected)).trans bodyProvenance.sourceExtension
  have conditionCovered : TemplateScopeCovered selected.body.finalized.typedSource
      loopContext (.expression inferredCondition.id) := by
    apply TemplateScopeCovered.forLoopCondition boundary.covered resources.graph_closed
    · simpa [StatementNode.applySubstitution, StatementForm.applySubstitution] using containsFinal
    · exact loopAssumptions
  have conditionTyping := recursiveExpression
    (descend here (.statement_for_condition boundary.accepted form rfl initializerSuccess conditionSuccess)) ({
    accepted := conditionSuccess
    interfaces := boundary.interfaces
    extension := conditionSubstitutionExtension
    scope := boundary.scope
    invariant := RecursiveExpressionInvariant.ofStatement initializerInvariant
    actual := initializerActual
    operational := initializerOperational
    expectedBelow := conditionExpected
    expectedAdmissible := by
      intro type member
      cases member
      exact TypeAdmissible.bool ((RecursiveExpressionInvariant.ofStatement initializerInvariant).typeParameterBinders
        (by simpa [boundary.scope.owner, boundary.scope.parameters] using boundary.scope.canonical checked))
    expectedSafe := conditionSafe
    rawSubtree := (boundary.rawSubtree.child (directChild_statement_reference containsRaw
      (by simp [StatementForm.references]))).monoBefore conditionSource
    integerPatterns := List.Subset.trans (Detail.inferStatementsFuel_integerPatterns_subset bodySuccess)
      (List.Subset.trans bodyProvenance.integerPatternsSubset boundary.integerPatterns)
    integerLiterals := List.Subset.trans (Detail.inferStatementsFuel_integerLiterals_subset bodySuccess)
      (List.Subset.trans bodyLiteralsParent boundary.integerLiterals)
    requirements := List.Subset.trans (Detail.inferStatementsFuel_requirements_subset bodySuccess)
      (List.Subset.trans bodyProvenance.requirementsSubset boundary.requirements)
    covered := conditionCovered
    actualCovered := boundary.actualCovered.preserved_statement_reference containsRaw resultExtension
      (by simp [StatementForm.references]) } :
    RootedExpressionBoundary selected childFuel inferenceContext condition (some .bool)
      initializerResult.state inferredCondition conditionState frames loopContext)
  have conditionBool : ExpressionHasType selected.body.finalized.typedSource
      loopContext inferredCondition.id .bool := by
    have same : selected.body.finalized.substitution.apply inferredCondition.type = .bool := by
      simpa using Detail.inferExprFuel_expected_type_apply_eq conditionSuccess conditionSubstitutionExtension
    simpa [same] using conditionTyping
  have loopReturn : TypeAdmissible loopContext (selected.body.finalized.substitution.apply expectedReturn) :=
    StructuralSubstitution.TypeAdmissible.transportContext
      (initializerInvariant.signaturesEq.trans boundary.invariant.signaturesEq.symm)
      (initializerInvariant.typeParametersEq.trans boundary.invariant.typeParametersEq.symm)
      (initializerInvariant.declarationEq.trans boundary.invariant.declarationEq.symm)
      (initializerActual.variables_eq.trans boundary.actual.variables_eq.symm)
      (initializerInvariant.residual.trans boundary.invariant.residual.symm) returnAdmissible
  have conditionBinders := congrArg LexicalScope.binders
    (Detail.inferExprFuel_success_lexicalScope_eq conditionSuccess)
  change conditionState.localBinders = initializerResult.state.localBinders at conditionBinders
  have bodyReturnSafe : ∀ binder ∈ conditionState.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified conditionState expectedReturn := by
    intro binder member
    have old : binder ∈ initializerResult.state.localBinders := conditionBinders ▸ member
    have privacy := ProtectedVariables.inferExprFuel_private binder.scheme.quantified childFuel
      inferenceContext condition (some .bool) initializerResult.state initializerInvariant.ready
      initializerOperational.requirements (initializerOperational.quantifiersBelow binder old)
      (initializerOperational.privacy binder old) catalog formation canonical conditionExpected
      (conditionSafe binder old) _ conditionSuccess
    exact privacy.1 expectedReturn (initializerPrivacy initializerSuccess binder old)
  have bodyCovered : ∀ child ∈ bodyResult.statements,
      TemplateScopeCovered selected.body.finalized.typedSource loopContext (.statement child) := by
    intro child member
    apply rooted_statement_child_covered containsRaw
      (by simp [StatementForm.references, member]) resultExtension boundary.covered resources.graph_closed
    intro predicate present
    simpa [loopAssumptions] using present
  obtain ⟨bodyFinal, bodyFacts, _, _, bodyOperational, bodyTyping, bodyAgreement⟩ :=
    recursiveBody (descend here (.statement_for_body boundary.accepted form rfl initializerSuccess conditionSuccess bodySuccess))
      bodyReturnSafe loopReturn ({
      accepted := bodySuccess
      interfaces := boundary.interfaces
      extension := bodySubstitutionExtension
      scope := boundary.scope.withLoopDepth (inferenceContext.loopDepth + 1)
      invariant := conditionInvariant
      actual := initializerActual
      operational := conditionOperational
      rawSubtrees := fun child member => (boundary.rawSubtree.child
        (directChild_statement_reference containsRaw (by simp [StatementForm.references, member]))).monoBefore
          bodyProvenance.sourceExtension
      integerPatterns := List.Subset.trans bodyProvenance.integerPatternsSubset boundary.integerPatterns
      integerLiterals := List.Subset.trans bodyLiteralsParent boundary.integerLiterals
      requirements := List.Subset.trans bodyProvenance.requirementsSubset boundary.requirements
      covered := bodyCovered
      actualCovered := fun child member => boundary.actualCovered.preserved_statement_reference
        containsRaw resultExtension (by simp [StatementForm.references, member]) } :
      StatementsBoundary selected childFuel {inferenceContext with loopDepth := inferenceContext.loopDepth + 1}
        body.value expectedReturn conditionState bodyResult frames loopContext)
  have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
    (context := {inferenceContext with loopDepth := inferenceContext.loopDepth + 1})
    conditionProperties.2.1 formation canonical conditionInvariant.returnBelow bodySuccess
  have bodyBelow := (Detail.inferStatementsFuel_occurrenceBoundExtends bodySuccess).nodesBelowNextOccurrence
    bodyProvenance.initialBelow
  have nextLocalLe := Nat.le_trans (Detail.inferExprFuel_nextLocal_le conditionSuccess)
    (Detail.inferStatementsFuel_nextLocal_le bodySuccess)
  have postInvariant := initializerInvariant.restoreLexicalScope
    (conditionProperties.1.trans bodyProperties.1) bodyBelow nextLocalLe bodySubstitutionExtension
  have savedBinders : initializerResult.state.localBinders ⊆ bodyResult.state.localBinders := by
    rw [← conditionBinders]
    exact ProtectedVariables.inferStatementsFuel_binders_subset bodySuccess
  have postOperational := bodyOperational.restoreSaved initializerOperational.origins savedBinders
  have postOwner : selected.body.finalized.typedSource.owner =
      (bodyResult.state.restoreLexicalScope initializerResult.state.lexicalScope).owner := by
    have ownerToPost := postProvenance.sourceExtension.owner_eq
    have postOwner := Detail.inferForItemsFuel_preserves_owner postSuccess
    have retained := resultExtension.owner_eq
    simpa [State.toTypedSource] using retained.trans (ownerToPost.trans postOwner)
  obtain ⟨postContext, _, _, _, postTyping⟩ :=
    recursiveItems (descend here (.statement_for_post boundary.accepted form rfl initializerSuccess conditionSuccess bodySuccess postSuccess)) ({
      accepted := postSuccess
      interfaces := boundary.interfaces
      extension := postSubstitutionExtension
      scope := boundary.scope.withLoopDepth (inferenceContext.loopDepth + 1)
      invariant := postInvariant
      actual := initializerActual
      operational := postOperational
      rawReferences := fun item member reference present => (boundary.rawSubtree.child
        (directChild_statement_reference containsRaw (postReference item member reference present))).monoBefore
          postProvenance.sourceExtension
      integerPatterns := List.Subset.trans postProvenance.integerPatternsSubset boundary.integerPatterns
      integerLiterals := List.Subset.trans postLiteralsParent boundary.integerLiterals
      requirements := List.Subset.trans postProvenance.requirementsSubset boundary.requirements
      owner := postOwner
      covered := fun item member => (headerCovered.2 item member).transportAssumptions loopAssumptions
      bindingsRetained := headerBindings.2
      actualCovered := fun item member reference present =>
        boundary.actualCovered.preserved_statement_reference containsRaw resultExtension
          (postReference item member reference present)
      actualBindings := headerActualBindings.2 } :
      ForItemsBoundary selected childFuel {inferenceContext with loopDepth := inferenceContext.loopDepth + 1}
        post expectedReturn (bodyResult.state.restoreLexicalScope initializerResult.state.lexicalScope)
        postResult frames loopContext)
  let facts : StatementFacts := {
    type := .unit, hasValue := false, sawReturn := false,
    control := .loop bodyFacts.control }
  have typing : StatementHasType selected.body.finalized.typedSource
      {returnType := selected.body.finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth}
      target result.id target facts :=
    .forLoop containsFinal rfl initializerTyping conditionBool bodyTyping postTyping
      (by simp [StatementNode.applySubstitution, resultEq])
  have agreement : StatementResultMatchesFactsAfterSubstitution
      selected.body.finalized.substitution result facts := by
    rw [resultEq]
    exact StatementResultMatchesFactsAfterSubstitution.forLoop _ bodyFacts _ _
  have bindersEq : result.state.localBinders = initial.localBinders := by
    simp [resultEq, State.restoreLexicalScope, State.recordNode, State.lexicalScope]
  have active : ActiveLocalContextInvariant result.state selected.body.finalized.substitution target := by
    rw [resultEq]
    exact allocatedInvariant.active.restoreLexicalScope_recordNode _
  have finalInvariant := boundary.invariant.of_retained_statement_typing boundary.accepted formation canonical active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension (activeSchemeQuantifierIsolation_transport boundary.invariant.schemeIsolation bindersEq) typing
  have finalOperational := boundary.operational.ofStatementPreservingBinders boundary.invariant.ready
    catalog formation canonical boundary.invariant.returnBelow returnSafe boundary.accepted bindersEq
  exact ⟨target, facts, finalInvariant, boundary.actual, finalOperational, typing, agreement⟩

theorem statement_for_of_initializer_privacy
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursiveItems : ForItemsRootedSoundness selected childFuel)
    (recursiveExpression : ExpressionRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {headerSpan : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
    {condition : Syntax.Expr} {body : Syntax.Block} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : statement.value = .forLoop headerSpan initializer condition post body)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (initializerPrivacy : ∀ {actualInitializer : Detail.InferredForItems},
      Detail.inferForItemsFuel childFuel inferenceContext initializer initial.allocateStatementId.2 = .ok actualInitializer →
      ∀ binder ∈ actualInitializer.state.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified actualInitializer.state expectedReturn)
    (recursiveBody : ∀ {bodyInitial : State} {bodyResult : Detail.BlockResult}
      {loopContext : SourceSemantics.Context},
      (∀ binder ∈ bodyInitial.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified bodyInitial expectedReturn) →
      TypeAdmissible loopContext (selected.body.finalized.substitution.apply expectedReturn) →
      StatementsBoundary selected childFuel {inferenceContext with loopDepth := inferenceContext.loopDepth + 1} body.value expectedReturn
        bodyInitial bodyResult frames loopContext →
      StatementsConclusion selected {inferenceContext with loopDepth := inferenceContext.loopDepth + 1} expectedReturn bodyResult frames loopContext) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  exact statement_for_of_initializer_privacy_for (callProvenance := fun _ => True) checked true_childClosed
    (fun _ boundary => recursiveItems boundary) (fun _ boundary => recursiveExpression boundary)
    True.intro form boundary returnSafe returnAdmissible initializerPrivacy
    (fun _ safe admissible boundary => recursiveBody safe admissible boundary)

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
