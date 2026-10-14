import Solcore.SourceSemantics.SourceInferenceSelectedStatementReferences
import Solcore.SourceSemantics.SourceInferenceSelectedStatementState

/-! Blocks and branches retain only their own actual occurrence subtrees.
Their local typing still uses the completed parent statement source. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

theorem actualInferStatementFuel_success_block_of_scoped_body
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {body : List Syntax.Statement}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .block body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions =
      wholeContext.assumptions)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (actual : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (returnAdmissible : TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn))
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultExtension : SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) finalized.typedSource (.statement result.id))
    (rawResultExtension : RawSubtreePreserved
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentActualCovered : ActualContext.Covers finalized frames (.statement result.id))
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (bodySound : ActualInferStatementsFuelRootedSoundness fuel) :
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
  obtain ⟨bodyResult, bodySuccess, resultEq, parentNode⟩ :=
    inferStatementFuel_success_block_facts statementEq allocationEq success
      roots
  obtain ⟨bodyResult', bodySuccess', _allocatedBelow, bodyExtension,
      bodyIntegerPatternsSubset, bodyRequirementsSubset⟩ :=
    inferStatementFuel_success_block_child_provenance statementEq allocationEq
      success initialInvariant.nodesBelow roots
  have bodyResultEq : bodyResult' = bodyResult := by
    rw [bodySuccess] at bodySuccess'
    exact (Except.ok.inj bodySuccess').symm
  subst bodyResult'
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have bodySubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        bodyResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      resultSubstitutionExtension
  have bodyIntegerLiteralsSubset :
      bodyResult.state.integerLiterals ⊆ result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    simpa [State.restoreLexicalScope, State.recordNode] using member
  have bodyCovered : ∀ child, child ∈ bodyResult.statements →
      TemplateScopeCovered finalized.typedSource semanticContext
        (.statement child) := by
    intro child member
    have childEdge : DirectChild (result.state.toTypedSource roots)
        (.statement result.id) (.statement child) := by
      refine ⟨.statement {
        id := result.id
        span := statement.span
        type := result.type
        form := .block bodyResult.statements
      }, ?_, ?_⟩
      · refine ⟨parentNode.1, ?_⟩
        exact congrArg NodeId.statement parentNode.2
      · simpa [nodeChildIds, Node.references, StatementForm.references] using
          (List.mem_map.mpr ⟨child, member, rfl⟩ :
            NodeId.statement child ∈
              bodyResult.statements.map NodeId.statement)
    have coveredEdge : DirectChild finalized.typedSource
        (.statement result.id) (.statement child) :=
      resultExtension.directChild childEdge
    exact TemplateScopeCovered.statementChild parentCovered
      resources.graph_closed coveredEdge (fun _ membership => membership)
  have branch : ∃ finalContext facts,
      ActiveLocalContextInvariant result.state finalized.substitution
        finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
    have blockSound := inferStatementFuel_success_block_sound
      statementEq allocationEq success initialInvariant.active roots
      (by
        intro actualBody actualSuccess
        have actualEq : actualBody = bodyResult := by
          rw [bodySuccess] at actualSuccess
          exact (Except.ok.inj actualSuccess).symm
        subst actualBody
        obtain ⟨bodyContext, bodyFacts, bodyInvariant, _bodyActual, _bodyOperational, bodyTyping,
            bodyAgreement⟩ :=
          bodySound bodySuccess resources interfaces signaturesEq ownerEq parametersEq
            assumptionsEq signatureFormation functionsCanonical catalog
            signatureParameters allocatedInvariant actual (operational.allocateStatementId allocationEq) returnAdmissible bodySubstitutionExtension
            (fun child _ => SubtreePreserved.ofTypingSourceExtends
              (bodyExtension.applySubstitution finalized.substitution))
            (fun child member => (rawResultExtension.child
              (directChild_statement_reference parentNode (by simp [StatementForm.references, member]))).monoBefore bodyExtension)
            (List.Subset.trans bodyIntegerPatternsSubset integerPatternsSubset)
            (List.Subset.trans bodyIntegerLiteralsSubset integerLiteralsSubset)
            (List.Subset.trans bodyRequirementsSubset requirementsSubset)
            bodyCovered (fun child member => parentActualCovered.preserved_statement_reference
              parentNode resultExtension (by simp [StatementForm.references, member]))
        exact ⟨bodyContext, bodyFacts, bodyInvariant.active, bodyTyping,
          bodyAgreement⟩)
    obtain ⟨facts, active, typing, agreement⟩ := blockSound
    exact ⟨semanticContext, facts, active, typing, agreement⟩
  have resultSchemeIsolation : ActiveSchemeQuantifierIsolation
      result.state := by
    apply activeSchemeQuantifierIsolation_transport
      allocatedInvariant.schemeIsolation
    simp [resultEq, State.restoreLexicalScope, State.recordNode,
      State.lexicalScope]
  obtain ⟨finalContext, facts, finalInvariant, typing, agreement⟩ :=
    RecursiveStatementInvariant.close_statement_branch initialInvariant
      success signatureFormation functionsCanonical
      (inferStatementFuel_preserves_localBindersBelowNextLocal initialInvariant.bindersBelow success)
      resultSubstitutionExtension resultSchemeIsolation branch
  have bindersEq : result.state.localBinders = initial.localBinders := by
    have allocationBinders := congrArg LexicalScope.binders (Detail.allocateStatementId_success_lexicalScope allocationEq)
    simpa only [resultEq, State.restoreLexicalScope, State.recordNode, State.lexicalScope] using allocationBinders
  have properties := Detail.inferStatementFuel_inferenceProperties initialInvariant.ready signatureFormation
    functionsCanonical initialInvariant.returnBelow success
  exact ⟨finalContext, facts, finalInvariant, actual.of_statement typing,
    operational.ofStatementPreservingBinders success bindersEq properties.1.next_le, typing, agreement⟩

/-- The while-loop body is checked at the actual condition-result state and
typed under the loop-depth increment.  Its semantic source is the completed
while statement, while coverage and requirements remain anchored to the
whole finalized body. -/
theorem actualInferStatementFuel_success_whileLoop_of_scoped_body
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {body : Syntax.Block}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .whileLoop condition body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions =
      wholeContext.assumptions)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (actual : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (returnAdmissible : TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn))
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultExtension : SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) finalized.typedSource (.statement result.id))
    (rawResultExtension : RawSubtreePreserved
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentActualCovered : ActualContext.Covers finalized frames (.statement result.id))
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (conditionSound : ∀ {inferredCondition : InferredExpression}
      {conditionState : State},
      Detail.inferExprFuel fuel inferenceContext condition (some .bool)
        allocated = .ok (inferredCondition, conditionState) →
      ExpressionHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        semanticContext inferredCondition.id
        (finalized.substitution.apply inferredCondition.type))
    (bodySound : ActualInferStatementsFuelRootedSoundness fuel) :
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
  let loopContext : Frontend.SourceInference.Context := {
    inferenceContext with loopDepth := inferenceContext.loopDepth + 1 }
  obtain ⟨inferredCondition, conditionState, bodyResult, conditionSuccess,
      actualBodySuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_whileLoop_facts statementEq allocationEq
      success roots
  obtain ⟨actualConditionState, actualBodyResult,
      ⟨actualCondition, actualConditionSuccess⟩, actualBodySuccess',
      conditionBelow, bodySourceExtension, bodyIntegerPatternsSubset,
      bodyRequirementsSubset⟩ :=
    inferStatementFuel_success_whileLoop_child_provenance statementEq
      allocationEq success initialInvariant.nodesBelow roots
  have conditionStateEq : actualConditionState = conditionState := by
    rw [conditionSuccess] at actualConditionSuccess
    exact (congrArg Prod.snd
      (Except.ok.inj actualConditionSuccess)).symm
  subst actualConditionState
  have bodyResultEq : actualBodyResult = bodyResult := by
    rw [actualBodySuccess] at actualBodySuccess'
    exact (Except.ok.inj actualBodySuccess').symm
  subst actualBodyResult
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical (by
      intro expected member
      simp only [Option.mem_def] at member
      injection member with expectedEq
      subst expected
      simp [Ty.bool]) conditionSuccess
  have conditionReturnBelow :
      expectedReturn.VariablesBelow conditionState.inference.next :=
    allocatedInvariant.returnBelow.weaken conditionProperties.1.next_le
  have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
    (context := loopContext) conditionProperties.2.1 signatureFormation
    functionsCanonical conditionReturnBelow actualBodySuccess
  have bodySubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        bodyResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      resultSubstitutionExtension
  have conditionSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        conditionState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans
      bodySubstitutionExtension bodyProperties.1.substitution_extends
  have conditionInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized conditionState semanticContext :=
    allocatedInvariant.inferExprFuel conditionSuccess signatureFormation
      functionsCanonical (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [Ty.bool]) conditionSubstitutionExtension
  have conditionOperational := (operational.allocateStatementId allocationEq).ofExpression conditionSuccess conditionProperties.1.next_le
  have bodyIntegerLiteralsSubset :
      bodyResult.state.integerLiterals ⊆ result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    simpa [State.restoreLexicalScope, State.recordNode] using member
  have bodyCovered : ∀ child, child ∈ bodyResult.statements →
      TemplateScopeCovered finalized.typedSource semanticContext
        (.statement child) := by
    intro child member
    have childReference : (.statement child : NodeId) ∈
        (StatementForm.whileLoop inferredCondition.id
          bodyResult.statements).references := by
      simp [StatementForm.references, member]
    exact rooted_statement_child_covered
      contains childReference resultExtension parentCovered
      resources.graph_closed (fun _ membership => membership)
  obtain ⟨bodyFinal, bodyFacts, bodyInvariant, _bodyActual, _bodyOperational, bodyTyping,
      bodyAgreement⟩ :=
    bodySound actualBodySuccess resources interfaces (by simpa [loopContext] using signaturesEq)
      (by simpa [loopContext] using ownerEq)
      (by simpa [loopContext] using parametersEq)
      (by simpa [loopContext] using assumptionsEq)
      signatureFormation functionsCanonical catalog signatureParameters
      conditionInvariant actual conditionOperational returnAdmissible bodySubstitutionExtension
      (fun child _ => SubtreePreserved.ofTypingSourceExtends
        (bodySourceExtension.applySubstitution finalized.substitution))
      (fun child member => (rawResultExtension.child
        (directChild_statement_reference contains (by simp [StatementForm.references, member]))).monoBefore bodySourceExtension)
      (List.Subset.trans bodyIntegerPatternsSubset integerPatternsSubset)
      (List.Subset.trans bodyIntegerLiteralsSubset integerLiteralsSubset)
      (List.Subset.trans bodyRequirementsSubset requirementsSubset)
      bodyCovered (fun child member => parentActualCovered.preserved_statement_reference
        contains resultExtension (by simp [StatementForm.references, member]))
  have branch : ∃ finalContext facts,
      ActiveLocalContextInvariant result.state finalized.substitution
        finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
    have conditionTyping := conditionSound conditionSuccess
    have conditionEq : finalized.substitution.apply inferredCondition.type =
        .bool := by
      simpa using Detail.inferExprFuel_expected_type_apply_eq
        conditionSuccess conditionSubstitutionExtension
    subst result
    refine ⟨semanticContext, {
        type := .unit
        hasValue := false
        sawReturn := false
        control := .loop bodyFacts.control
      }, conditionInvariant.active.restoreLexicalScope_recordNode _, ?_, ?_⟩
    · exact whileLoopStatementHasType_afterSubstitution contains
        conditionTyping conditionEq bodyTyping
    · exact StatementResultMatchesFactsAfterSubstitution.whileLoop
        finalized.substitution bodyFacts id _
  have resultSchemeIsolation : ActiveSchemeQuantifierIsolation
      result.state := by
    apply activeSchemeQuantifierIsolation_transport
      conditionInvariant.schemeIsolation
    simp [resultEq, State.restoreLexicalScope, State.recordNode,
      State.lexicalScope]
  obtain ⟨finalContext, facts, finalInvariant, typing, agreement⟩ :=
    RecursiveStatementInvariant.close_statement_branch initialInvariant
      success signatureFormation functionsCanonical
      (inferStatementFuel_preserves_localBindersBelowNextLocal initialInvariant.bindersBelow success)
      resultSubstitutionExtension resultSchemeIsolation branch
  have bindersEq : result.state.localBinders = initial.localBinders := by
    have conditionBinders := congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq conditionSuccess)
    have allocationBinders := congrArg LexicalScope.binders (Detail.allocateStatementId_success_lexicalScope allocationEq)
    simpa only [resultEq, State.restoreLexicalScope, State.recordNode, State.lexicalScope] using conditionBinders.trans allocationBinders
  have properties := Detail.inferStatementFuel_inferenceProperties initialInvariant.ready signatureFormation
    functionsCanonical initialInvariant.returnBelow success
  exact ⟨finalContext, facts, finalInvariant, actual.of_statement typing,
    operational.ofStatementPreservingBinders success bindersEq properties.1.next_le, typing, agreement⟩

/-- The no-else conditional consumes only its actual then-body traversal;
the missing else branch contributes the ordinary unit control fact. -/
theorem actualInferStatementFuel_success_ifWithoutElse_of_scoped_body
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody : Syntax.Block}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .ifThen condition thenBody none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions =
      wholeContext.assumptions)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (actual : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (returnAdmissible : TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn))
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultExtension : SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) finalized.typedSource (.statement result.id))
    (rawResultExtension : RawSubtreePreserved
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentActualCovered : ActualContext.Covers finalized frames (.statement result.id))
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (conditionSound : ∀ {inferredCondition : InferredExpression}
      {conditionState : State},
      Detail.inferExprFuel fuel inferenceContext condition (some .bool)
        allocated = .ok (inferredCondition, conditionState) →
      ExpressionHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        semanticContext inferredCondition.id
        (finalized.substitution.apply inferredCondition.type))
    (thenSound : ActualInferStatementsFuelRootedSoundness fuel) :
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
  obtain ⟨inferredCondition, conditionState, thenResult, conditionSuccess,
      thenSuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_ifWithoutElse_facts statementEq allocationEq
      success roots
  obtain ⟨actualConditionState, actualThenResult,
      ⟨actualCondition, actualConditionSuccess⟩, actualThenSuccess,
      _conditionBelow, thenSourceExtension, thenIntegerPatternsSubset,
      thenRequirementsSubset⟩ :=
    inferStatementFuel_success_ifWithoutElse_child_provenance statementEq
      allocationEq success initialInvariant.nodesBelow roots
  have conditionStateEq : actualConditionState = conditionState := by
    rw [conditionSuccess] at actualConditionSuccess
    exact (congrArg Prod.snd
      (Except.ok.inj actualConditionSuccess)).symm
  subst actualConditionState
  have thenResultEq : actualThenResult = thenResult := by
    rw [thenSuccess] at actualThenSuccess
    exact (Except.ok.inj actualThenSuccess).symm
  subst actualThenResult
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical (by
      intro expected member
      simp only [Option.mem_def] at member
      injection member with expectedEq
      subst expected
      simp [Ty.bool]) conditionSuccess
  have conditionReturnBelow :
      expectedReturn.VariablesBelow conditionState.inference.next :=
    allocatedInvariant.returnBelow.weaken conditionProperties.1.next_le
  have thenProperties := Detail.inferStatementsFuel_inferenceProperties
    conditionProperties.2.1 signatureFormation functionsCanonical
    conditionReturnBelow thenSuccess
  have thenSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        thenResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      resultSubstitutionExtension
  have conditionSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        conditionState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans
      thenSubstitutionExtension thenProperties.1.substitution_extends
  have conditionInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized conditionState semanticContext :=
    allocatedInvariant.inferExprFuel conditionSuccess signatureFormation
      functionsCanonical (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [Ty.bool]) conditionSubstitutionExtension
  have conditionOperational := (operational.allocateStatementId allocationEq).ofExpression conditionSuccess conditionProperties.1.next_le
  have thenIntegerLiteralsSubset :
      thenResult.state.integerLiterals ⊆ result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    simpa [State.restoreLexicalScope, State.recordNode] using member
  have thenCovered : ∀ child, child ∈ thenResult.statements →
      TemplateScopeCovered finalized.typedSource semanticContext
        (.statement child) := by
    intro child member
    have childReference : (.statement child : NodeId) ∈
        (StatementForm.ifThen inferredCondition.id thenResult.statements
          none).references := by
      simp [StatementForm.references, member]
    exact rooted_statement_child_covered
      contains childReference resultExtension parentCovered
      resources.graph_closed (fun _ membership => membership)
  obtain ⟨thenFinal, thenFacts, thenInvariant, _thenActual, _thenOperational, thenTyping,
      thenAgreement⟩ :=
    thenSound thenSuccess resources interfaces signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters conditionInvariant actual conditionOperational returnAdmissible thenSubstitutionExtension
      (fun child _ => SubtreePreserved.ofTypingSourceExtends
        (thenSourceExtension.applySubstitution finalized.substitution))
      (fun child member => (rawResultExtension.child
        (directChild_statement_reference contains (by simp [StatementForm.references, member]))).monoBefore thenSourceExtension)
      (List.Subset.trans thenIntegerPatternsSubset integerPatternsSubset)
      (List.Subset.trans thenIntegerLiteralsSubset integerLiteralsSubset)
      (List.Subset.trans thenRequirementsSubset requirementsSubset)
      thenCovered (fun child member => parentActualCovered.preserved_statement_reference
        contains resultExtension (by simp [StatementForm.references, member]))
  have branch : ∃ finalContext facts,
      ActiveLocalContextInvariant result.state finalized.substitution
        finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
    have conditionTyping := conditionSound conditionSuccess
    have conditionEq : finalized.substitution.apply inferredCondition.type =
        .bool := by
      simpa using Detail.inferExprFuel_expected_type_apply_eq
        conditionSuccess conditionSubstitutionExtension
    subst result
    refine ⟨semanticContext, {
        type := .unit
        hasValue := false
        sawReturn := false
        control := thenFacts.control.branches (.ordinary .unit)
      }, conditionInvariant.active.restoreLexicalScope_recordNode _, ?_, ?_⟩
    · exact ifWithoutElseStatementHasType_afterSubstitution contains
        conditionTyping conditionEq thenTyping
    · exact StatementResultMatchesFactsAfterSubstitution.ifWithoutElse
        finalized.substitution thenFacts id _
  have resultSchemeIsolation : ActiveSchemeQuantifierIsolation
      result.state := by
    apply activeSchemeQuantifierIsolation_transport
      conditionInvariant.schemeIsolation
    simp [resultEq, State.restoreLexicalScope, State.recordNode,
      State.lexicalScope]
  obtain ⟨finalContext, facts, finalInvariant, typing, agreement⟩ :=
    RecursiveStatementInvariant.close_statement_branch initialInvariant
      success signatureFormation functionsCanonical
      (inferStatementFuel_preserves_localBindersBelowNextLocal initialInvariant.bindersBelow success)
      resultSubstitutionExtension resultSchemeIsolation branch
  have bindersEq : result.state.localBinders = initial.localBinders := by
    have conditionBinders := congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq conditionSuccess)
    have allocationBinders := congrArg LexicalScope.binders (Detail.allocateStatementId_success_lexicalScope allocationEq)
    simpa only [resultEq, State.restoreLexicalScope, State.recordNode, State.lexicalScope] using conditionBinders.trans allocationBinders
  have properties := Detail.inferStatementFuel_inferenceProperties initialInvariant.ready signatureFormation
    functionsCanonical initialInvariant.returnBelow success
  exact ⟨finalContext, facts, finalInvariant, actual.of_statement typing,
    operational.ofStatementPreservingBinders success bindersEq properties.1.next_le, typing, agreement⟩

/-- Both branches of a successful conditional are typed from their concrete
traces.  The second branch starts from the restored condition scope, while
both branches' roots remain direct children of the completed parent node. -/
theorem actualInferStatementFuel_success_ifWithElse_of_scoped_bodies
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody elseBody : Syntax.Block}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .ifThen condition thenBody
      (some elseBody))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions =
      wholeContext.assumptions)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (actual : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (returnAdmissible : TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn))
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultExtension : SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) finalized.typedSource (.statement result.id))
    (rawResultExtension : RawSubtreePreserved
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentActualCovered : ActualContext.Covers finalized frames (.statement result.id))
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (conditionSound : ∀ {inferredCondition : InferredExpression}
      {conditionState : State},
      Detail.inferExprFuel fuel inferenceContext condition (some .bool)
        allocated = .ok (inferredCondition, conditionState) →
      ExpressionHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        semanticContext inferredCondition.id
        (finalized.substitution.apply inferredCondition.type))
    (branchSound : ActualInferStatementsFuelRootedSoundness fuel) :
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
  obtain ⟨inferredCondition, conditionState, thenResult, elseResult,
      conditionSuccess, thenSuccess, elseSuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_ifWithElse_facts statementEq allocationEq
      success roots
  obtain ⟨actualConditionState, actualThenResult, actualElseResult,
      ⟨actualCondition, actualConditionSuccess⟩, actualThenSuccess,
      actualElseSuccess, _conditionBelow, _elseInputBelow,
      thenSourceExtension, elseSourceExtension,
      thenIntegerPatternsSubset, elseIntegerPatternsSubset,
      thenRequirementsSubset, elseRequirementsSubset⟩ :=
    inferStatementFuel_success_ifWithElse_child_provenance statementEq
      allocationEq success initialInvariant.nodesBelow roots
  have conditionStateEq : actualConditionState = conditionState := by
    rw [conditionSuccess] at actualConditionSuccess
    exact (congrArg Prod.snd
      (Except.ok.inj actualConditionSuccess)).symm
  subst actualConditionState
  have thenResultEq : actualThenResult = thenResult := by
    rw [thenSuccess] at actualThenSuccess
    exact (Except.ok.inj actualThenSuccess).symm
  subst actualThenResult
  have elseResultEq : actualElseResult = elseResult := by
    rw [elseSuccess] at actualElseSuccess
    exact (Except.ok.inj actualElseSuccess).symm
  subst actualElseResult
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical (by
      intro expected member
      simp only [Option.mem_def] at member
      injection member with expectedEq
      subst expected
      simp [Ty.bool]) conditionSuccess
  have conditionReturnBelow :
      expectedReturn.VariablesBelow conditionState.inference.next :=
    allocatedInvariant.returnBelow.weaken conditionProperties.1.next_le
  have thenProperties := Detail.inferStatementsFuel_inferenceProperties
    conditionProperties.2.1 signatureFormation functionsCanonical
    conditionReturnBelow thenSuccess
  have thenBelow : thenResult.state.NodesBelowNextOccurrence :=
    (Detail.inferStatementsFuel_occurrenceBoundExtends thenSuccess
      ).nodesBelowNextOccurrence
        ((Detail.inferExprFuel_occurrenceBoundExtends conditionSuccess
          ).nodesBelowNextOccurrence allocatedInvariant.nodesBelow)
  have restoredProperties := State.restoreLexicalScope_inferenceProperties
    conditionProperties.2.1 thenProperties.1
  have elseReturnBelow : expectedReturn.VariablesBelow
      (thenResult.state.restoreLexicalScope
        conditionState.lexicalScope).inference.next :=
    conditionReturnBelow.weaken restoredProperties.1.next_le
  have elseProperties := Detail.inferStatementsFuel_inferenceProperties
    restoredProperties.2 signatureFormation functionsCanonical
    elseReturnBelow elseSuccess
  have elseSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        elseResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      resultSubstitutionExtension
  have elseInputSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        (thenResult.state.restoreLexicalScope
          conditionState.lexicalScope).inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans
      elseSubstitutionExtension elseProperties.1.substitution_extends
  have conditionSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        conditionState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans
      elseInputSubstitutionExtension restoredProperties.1.substitution_extends
  have conditionInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized conditionState semanticContext :=
    allocatedInvariant.inferExprFuel conditionSuccess signatureFormation
      functionsCanonical (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [Ty.bool]) conditionSubstitutionExtension
  have conditionOperational := (operational.allocateStatementId allocationEq).ofExpression conditionSuccess conditionProperties.1.next_le
  have elseInputInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized
      (thenResult.state.restoreLexicalScope conditionState.lexicalScope)
      semanticContext :=
    conditionInvariant.restoreLexicalScope thenProperties.1 thenBelow
      (Detail.inferStatementsFuel_nextLocal_le thenSuccess)
      elseInputSubstitutionExtension
  have thenSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        thenResult.state.inference.substitution := by
    simpa [State.restoreLexicalScope] using
      elseInputSubstitutionExtension
  have elseIntegerLiteralsSubset :
      elseResult.state.integerLiterals ⊆ result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    simpa [State.restoreLexicalScope, State.recordNode] using member
  have thenIntegerLiteralsSubset :
      thenResult.state.integerLiterals ⊆ result.state.integerLiterals := by
    have throughElse : thenResult.state.integerLiterals ⊆
        elseResult.state.integerLiterals := by
      simpa [State.restoreLexicalScope] using
        (Detail.inferStatementsFuel_integerLiterals_subset elseSuccess)
    exact List.Subset.trans throughElse elseIntegerLiteralsSubset
  have thenCovered : ∀ child, child ∈ thenResult.statements →
      TemplateScopeCovered finalized.typedSource semanticContext
        (.statement child) := by
    intro child member
    have childReference : (.statement child : NodeId) ∈
        (StatementForm.ifThen inferredCondition.id thenResult.statements
          (some elseResult.statements)).references := by
      simp [StatementForm.references, member]
    exact rooted_statement_child_covered
      contains childReference resultExtension parentCovered
      resources.graph_closed (fun _ membership => membership)
  obtain ⟨thenFinal, thenFacts, thenInvariant, _thenActual, _thenOperational, thenTyping,
      thenAgreement⟩ :=
    branchSound thenSuccess resources interfaces signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters conditionInvariant actual conditionOperational returnAdmissible thenSubstitutionExtension
      (fun child _ => SubtreePreserved.ofTypingSourceExtends
        (thenSourceExtension.applySubstitution finalized.substitution))
      (fun child member => (rawResultExtension.child
        (directChild_statement_reference contains (by simp [StatementForm.references, member]))).monoBefore thenSourceExtension)
      (List.Subset.trans thenIntegerPatternsSubset integerPatternsSubset)
      (List.Subset.trans thenIntegerLiteralsSubset integerLiteralsSubset)
      (List.Subset.trans thenRequirementsSubset requirementsSubset)
      thenCovered (fun child member => parentActualCovered.preserved_statement_reference
        contains resultExtension (by simp [StatementForm.references, member]))
  have elseIntegerPatternsSubset' :=
    List.Subset.trans elseIntegerPatternsSubset integerPatternsSubset
  have elseIntegerLiteralsSubset' :=
    List.Subset.trans elseIntegerLiteralsSubset integerLiteralsSubset
  have elseRequirementsSubset' :=
    List.Subset.trans elseRequirementsSubset requirementsSubset
  have elseCovered : ∀ child, child ∈ elseResult.statements →
      TemplateScopeCovered finalized.typedSource semanticContext
        (.statement child) := by
    intro child member
    have childReference : (.statement child : NodeId) ∈
        (StatementForm.ifThen inferredCondition.id thenResult.statements
          (some elseResult.statements)).references := by
      simp [StatementForm.references, member]
    exact rooted_statement_child_covered
      contains childReference resultExtension parentCovered
      resources.graph_closed (fun _ membership => membership)
  have elseOperational : ActualStateInvariant
      (thenResult.state.restoreLexicalScope conditionState.lexicalScope) (evidenceState.toTypedSource roots) := by
    obtain ⟨pending, ledger⟩ := conditionOperational.ledger
    refine ⟨⟨pending, ((actualLedgerFamily fuel).statements.statements thenSuccess ledger).restoreLexicalScope _⟩,
      conditionOperational.origins.congr_localBinders rfl, ?_, conditionOperational.sourceMonomorphic⟩
    exact activeQuantifiersBelowNext_transport conditionOperational.quantifiersBelow rfl thenProperties.1.next_le
  obtain ⟨elseFinal, elseFacts, elseInvariant, _elseActual, _elseOperational, elseTyping,
      elseAgreement⟩ :=
    branchSound elseSuccess resources interfaces signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters elseInputInvariant actual elseOperational returnAdmissible elseSubstitutionExtension
      (fun child _ => SubtreePreserved.ofTypingSourceExtends
        (elseSourceExtension.applySubstitution finalized.substitution))
      (fun child member => (rawResultExtension.child
        (directChild_statement_reference contains (by simp [StatementForm.references, member]))).monoBefore elseSourceExtension)
      elseIntegerPatternsSubset' elseIntegerLiteralsSubset'
      elseRequirementsSubset' elseCovered (fun child member => parentActualCovered.preserved_statement_reference
        contains resultExtension (by simp [StatementForm.references, member]))
  have branch : ∃ finalContext facts,
      ActiveLocalContextInvariant result.state finalized.substitution
        finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
    have conditionTyping := conditionSound conditionSuccess
    have conditionEq : finalized.substitution.apply inferredCondition.type =
        .bool := by
      simpa using Detail.inferExprFuel_expected_type_apply_eq
        conditionSuccess conditionSubstitutionExtension
    subst result
    refine ⟨semanticContext, {
        type := if thenFacts.sawReturn && elseFacts.sawReturn then
          finalized.substitution.apply expectedReturn
        else
          .unit
        hasValue := thenFacts.sawReturn && elseFacts.sawReturn
        sawReturn := thenFacts.sawReturn && elseFacts.sawReturn
        control := thenFacts.control.branches elseFacts.control
      }, conditionInvariant.active.restoreLexicalScope_recordNode _, ?_, ?_⟩
    · exact ifWithElseStatementHasType_afterSubstitution contains
        conditionTyping conditionEq thenTyping elseTyping thenAgreement
        elseAgreement elseSubstitutionExtension
    · exact StatementResultMatchesFactsAfterSubstitution.ifWithElse
        thenAgreement elseAgreement elseSubstitutionExtension id _
  have resultSchemeIsolation : ActiveSchemeQuantifierIsolation
      result.state := by
    apply activeSchemeQuantifierIsolation_transport
      conditionInvariant.schemeIsolation
    simp [resultEq, State.restoreLexicalScope, State.recordNode,
      State.lexicalScope]
  obtain ⟨finalContext, facts, finalInvariant, typing, agreement⟩ :=
    RecursiveStatementInvariant.close_statement_branch initialInvariant
      success signatureFormation functionsCanonical
      (inferStatementFuel_preserves_localBindersBelowNextLocal initialInvariant.bindersBelow success)
      resultSubstitutionExtension resultSchemeIsolation branch
  have bindersEq : result.state.localBinders = initial.localBinders := by
    have conditionBinders := congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq conditionSuccess)
    have allocationBinders := congrArg LexicalScope.binders (Detail.allocateStatementId_success_lexicalScope allocationEq)
    simpa only [resultEq, State.restoreLexicalScope, State.recordNode, State.lexicalScope] using conditionBinders.trans allocationBinders
  have properties := Detail.inferStatementFuel_inferenceProperties initialInvariant.ready signatureFormation
    functionsCanonical initialInvariant.returnBelow success
  exact ⟨finalContext, facts, finalInvariant, actual.of_statement typing,
    operational.ofStatementPreservingBinders success bindersEq properties.1.next_le, typing, agreement⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
