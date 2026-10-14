import Solcore.SourceSemantics.SourceInferenceStatementForLoopAssembly
import Solcore.SourceSemantics.SourceInferenceSelectedForLoopCondition
import Solcore.SourceSemantics.SourceInferenceSelectedForItemsSequencing
import Solcore.SourceSemantics.SourceInferenceStatementForLoopChildProgress
import Solcore.SourceSemantics.SourceInferenceForItemsCoverage

/-!
The recursive `for` statement step.  Each induction hypothesis is invoked
only on the actual initializer, condition, body, or post-header trace exposed
by the successful parent computation.  The completed local statement source
is separate from the whole-body finalization and coverage evidence.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

/-- Scoped soundness of one successful `for` statement, conditional only on
the four smaller-fuel recursive soundness propositions. -/
theorem actualInferStatementFuel_success_forLoop_rooted
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {headerSpan : Syntax.SourceSpan}
    {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Block}
    {initial allocated evidenceState : State} {id : StatementId}
    {result : Detail.StatementResult} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    {frames : List InitializedLetBinding}
    (statementEq : statement.value =
      .forLoop headerSpan initializer condition post body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures finalized.solvedRequirements finalized.typedSource)
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
    (parentActualCovered : ActualContext.Covers finalized frames (.statement result.id))
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultExtension : SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) finalized.typedSource (.statement result.id))
    (rawResultExtension : RawSubtreePreserved (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (initializerSound : ActualInferForItemsFuelRootedSoundness fuel)
    (expressionSound : ActualInferExprFuelRootedSoundness fuel)
    (bodySound : ActualInferStatementsFuelRootedSoundness fuel)
    (postSound : ActualInferForItemsFuelRootedSoundness fuel) :
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
  obtain ⟨initializerResult, inferredCondition, conditionState, bodyResult,
    postResult, initializerSuccess, conditionSuccess, bodySuccess,
    postSuccess, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_forLoop_facts statementEq allocationEq success
      roots
  obtain ⟨progressInitializer, progressCondition, progressConditionState,
    progressBody, progressPost, progressInitializerSuccess,
    progressConditionSuccess, progressBodySuccess, progressPostSuccess,
    initializerSubstitutionExtension, conditionSubstitutionExtension,
    bodySubstitutionExtension, postSubstitutionExtension,
    initializerLiteralsParent, conditionLiteralsParent,
    bodyLiteralsParent, postLiteralsParent⟩ :=
    inferStatementFuel_success_forLoop_child_progress statementEq
      allocationEq success signatureFormation functionsCanonical
      initialInvariant resultSubstitutionExtension
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
    inferStatementFuel_success_forLoop_child_provenance statementEq
      allocationEq success initialInvariant.nodesBelow roots
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
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have headerCovered := forItemsReferencesCovered_of_rootedForLoop
    containsRaw rfl resultExtension resources.graph_closed parentCovered
  have headerBindings := forItemsBindingsRetained_of_containedForLoop
    (rawResultExtension.containsStatement containsRaw) ⟨rfl, ⟨[], by simp⟩⟩
  have headerActualBindings := actualForItemsBindings_of_rootedForLoop containsRaw resultExtension parentActualCovered
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
  have initializerSourceOwner :
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution).owner = allocated.owner := by
    have ownerToInitializer := initializerProvenance.sourceExtension.owner_eq
    have initializerOwner :=
      Detail.inferForItemsFuel_preserves_owner initializerSuccess
    simpa [State.toTypedSource] using ownerToInitializer.trans initializerOwner
  obtain ⟨loopContext, initializerInvariant, initializerActual, initializerOperational, initializerTyping⟩ :=
    (initializerSound (control := {
        returnType := finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth })
      initializerSuccess resources interfaces signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters allocatedInvariant actual (operational.allocateStatementId allocationEq) returnAdmissible initializerSubstitutionExtension
      (fun _ _ _ _ => SubtreePreserved.ofTypingSourceExtends
        (initializerProvenance.sourceExtension.applySubstitution finalized.substitution))
      (fun item member reference present => (rawResultExtension.child (directChild_statement_reference
        containsRaw (initializerReference item member reference present))).monoBefore initializerProvenance.sourceExtension)
      (List.Subset.trans initializerProvenance.integerPatternsSubset
        integerPatternsSubset)
      (List.Subset.trans initializerLiteralsParent integerLiteralsSubset)
      (List.Subset.trans initializerProvenance.requirementsSubset
        requirementsSubset)
      initializerSourceOwner headerCovered.1 headerBindings.1
      (fun item member reference present => parentActualCovered.preserved_statement_reference containsRaw
        resultExtension (initializerReference item member reference present)) headerActualBindings.1)
  have loopAssumptionsEq : loopContext.assumptions =
      semanticContext.assumptions :=
    forItemsHaveType_assumptions_eq initializerTyping
  have conditionTyping :=
    actualInferStatementFuel_success_forLoop_condition_rooted statementEq
      allocationEq success initializerSuccess conditionSuccess resources interfaces
      signaturesEq ownerEq parametersEq assumptionsEq signatureFormation
      functionsCanonical catalog signatureParameters initialInvariant
      initializerInvariant initializerActual initializerOperational parentActualCovered resultSubstitutionExtension resultExtension
      rawResultExtension integerPatternsSubset integerLiteralsSubset
      requirementsSubset parentCovered loopAssumptionsEq expressionSound
  have conditionInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized conditionState loopContext :=
    initializerInvariant.inferExprFuel conditionSuccess signatureFormation
      functionsCanonical (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [Ty.bool]) conditionSubstitutionExtension
  have loopReturn : TypeAdmissible loopContext (finalized.substitution.apply expectedReturn) :=
    StructuralSubstitution.TypeAdmissible.transportContext
      (initializerInvariant.signaturesEq.trans initialInvariant.signaturesEq.symm)
      (initializerInvariant.typeParametersEq.trans initialInvariant.typeParametersEq.symm)
      (initializerInvariant.declarationEq.trans initialInvariant.declarationEq.symm)
      (initializerActual.variables_eq.trans actual.variables_eq.symm)
      (initializerInvariant.residual.trans initialInvariant.residual.symm) returnAdmissible
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    initializerInvariant.ready signatureFormation functionsCanonical
    (by intro expected member; cases member; simp [Ty.bool]) conditionSuccess
  have conditionOperational := initializerOperational.ofExpression conditionSuccess conditionProperties.1.next_le
  have bodyCovered : ∀ child, child ∈ bodyResult.statements →
      TemplateScopeCovered finalized.typedSource loopContext
        (.statement child) := by
    intro child member
    have childReference : (.statement child : NodeId) ∈
        (StatementForm.forLoop initializerResult.items inferredCondition.id
          postResult.items bodyResult.statements).references := by
      simp [StatementForm.references, member]
    apply rooted_statement_child_covered
      containsRaw childReference resultExtension parentCovered
      resources.graph_closed
    intro predicate predicateMember
    simpa [loopAssumptionsEq] using predicateMember
  obtain ⟨bodyFinal, bodyFacts, bodyInvariant, bodyActual, bodyOperational, bodyTyping,
    bodyAgreement⟩ :=
    bodySound bodySuccess resources interfaces
      (by simpa using signaturesEq)
      (by simpa using ownerEq)
      (by simpa using parametersEq)
      (by simpa using assumptionsEq)
      signatureFormation functionsCanonical catalog signatureParameters
      conditionInvariant initializerActual conditionOperational loopReturn bodySubstitutionExtension
      (fun _ _ => SubtreePreserved.ofTypingSourceExtends
        (bodyProvenance.sourceExtension.applySubstitution finalized.substitution))
      (fun child member => (rawResultExtension.child (directChild_statement_reference containsRaw
        (by simp [StatementForm.references, member]))).monoBefore bodyProvenance.sourceExtension)
      (List.Subset.trans bodyProvenance.integerPatternsSubset
        integerPatternsSubset)
      (List.Subset.trans bodyLiteralsParent integerLiteralsSubset)
      (List.Subset.trans bodyProvenance.requirementsSubset
        requirementsSubset)
      bodyCovered (fun child member => parentActualCovered.preserved_statement_reference containsRaw resultExtension
        (by simp [StatementForm.references, member]))
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    initializerInvariant.ready signatureFormation functionsCanonical
    (by
      intro expected member
      simp only [Option.mem_def] at member
      injection member with expectedEq
      subst expected
      simp [Ty.bool]) conditionSuccess
  have conditionReturnBelow : expectedReturn.VariablesBelow
      conditionState.inference.next :=
    initializerInvariant.returnBelow.weaken conditionProperties.1.next_le
  have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
    (context := { inferenceContext with
      loopDepth := inferenceContext.loopDepth + 1 })
    conditionProperties.2.1 signatureFormation functionsCanonical
    conditionReturnBelow bodySuccess
  have bodyBelow : bodyResult.state.NodesBelowNextOccurrence :=
    (Detail.inferStatementsFuel_occurrenceBoundExtends bodySuccess
      ).nodesBelowNextOccurrence bodyProvenance.initialBelow
  have nextLocalLe : initializerResult.state.nextLocal ≤
      bodyResult.state.nextLocal :=
    Nat.le_trans (Detail.inferExprFuel_nextLocal_le conditionSuccess)
      (Detail.inferStatementsFuel_nextLocal_le bodySuccess)
  have postInputInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized
      (bodyResult.state.restoreLexicalScope
        initializerResult.state.lexicalScope) loopContext :=
    initializerInvariant.restoreLexicalScope
      (conditionProperties.1.trans bodyProperties.1) bodyBelow nextLocalLe
      bodySubstitutionExtension
  have postOperational : ActualStateInvariant
      (bodyResult.state.restoreLexicalScope initializerResult.state.lexicalScope) (evidenceState.toTypedSource roots) := by
    obtain ⟨pending, ledger⟩ := bodyOperational.ledger
    refine ⟨⟨pending, ledger.restoreLexicalScope _⟩, initializerOperational.origins.congr_localBinders rfl, ?_, initializerOperational.sourceMonomorphic⟩
    exact activeQuantifiersBelowNext_transport initializerOperational.quantifiersBelow rfl
      (Nat.le_trans conditionProperties.1.next_le bodyProperties.1.next_le)
  have postCovered : ForItemsReferencesCovered finalized.typedSource
      finalized.substitution loopContext postResult.items := by
    intro item itemMember
    exact (headerCovered.2 item itemMember).transportAssumptions
      loopAssumptionsEq
  have postSourceOwner :
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution).owner =
        (bodyResult.state.restoreLexicalScope
          initializerResult.state.lexicalScope).owner := by
    have ownerToPost := postProvenance.sourceExtension.owner_eq
    have postOwner := Detail.inferForItemsFuel_preserves_owner postSuccess
    simpa [State.toTypedSource] using ownerToPost.trans postOwner
  obtain ⟨postContext, postInvariant, postActual, postFinalOperational, postTyping⟩ :=
    (postSound (control := ({
        returnType := finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth } : ControlContext).enterLoop)
      postSuccess resources interfaces
      (by simpa using signaturesEq)
      (by simpa using ownerEq)
      (by simpa using parametersEq)
      (by simpa using assumptionsEq)
      signatureFormation functionsCanonical catalog signatureParameters
      postInputInvariant initializerActual postOperational loopReturn postSubstitutionExtension
      (fun _ _ _ _ => SubtreePreserved.ofTypingSourceExtends
        (postProvenance.sourceExtension.applySubstitution finalized.substitution))
      (fun item member reference present => (rawResultExtension.child (directChild_statement_reference
        containsRaw (postReference item member reference present))).monoBefore postProvenance.sourceExtension)
      (List.Subset.trans postProvenance.integerPatternsSubset
        integerPatternsSubset)
      (List.Subset.trans postLiteralsParent integerLiteralsSubset)
      (List.Subset.trans postProvenance.requirementsSubset
        requirementsSubset)
      postSourceOwner postCovered headerBindings.2
      (fun item member reference present => parentActualCovered.preserved_statement_reference containsRaw
        resultExtension (postReference item member reference present)) headerActualBindings.2)
  have assembled : ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized result.state finalContext ∧
      StatementHasType ((result.state.toTypedSource roots).applySubstitution finalized.substitution)
        {returnType := finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth}
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution result facts := by
    apply inferStatementFuel_success_forLoop_of_actual_typed_children
      statementEq allocationEq success signatureFormation functionsCanonical
      initialInvariant resultSubstitutionExtension
    intro actualInitializer actualCondition actualConditionState actualBody
      actualPost actualInitializerSuccess actualConditionSuccess
      actualBodySuccess actualPostSuccess
    rw [initializerSuccess] at actualInitializerSuccess
    have actualInitializerEq := (Except.ok.inj actualInitializerSuccess).symm
    subst actualInitializer
    rw [conditionSuccess] at actualConditionSuccess
    obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualConditionSuccess).symm
    rw [bodySuccess] at actualBodySuccess
    have actualBodyEq := (Except.ok.inj actualBodySuccess).symm
    subst actualBody
    rw [postSuccess] at actualPostSuccess
    have actualPostEq := (Except.ok.inj actualPostSuccess).symm
    subst actualPost
    exact ⟨loopContext, bodyFinal, bodyFacts, postContext,
      initializerTyping, conditionTyping, bodyTyping, postTyping⟩
  obtain ⟨finalContext, facts, finalInvariant, typing, agreement⟩ := assembled
  have bindersEq : result.state.localBinders = initial.localBinders := by
    have allocatedBinders := congrArg LexicalScope.binders (Detail.allocateStatementId_success_lexicalScope allocationEq)
    simpa only [resultEq, State.recordNode, State.restoreLexicalScope, State.lexicalScope] using allocatedBinders
  have properties := Detail.inferStatementFuel_inferenceProperties initialInvariant.ready signatureFormation functionsCanonical initialInvariant.returnBelow success
  exact ⟨finalContext, facts, finalInvariant, actual.of_statement typing,
    operational.ofStatementPreservingBinders success bindersEq properties.1.next_le, typing, agreement⟩

theorem actualInferStatementFuelRootedSoundness_forLoop {fuel : Nat}
    (itemsSound : ActualInferForItemsFuelRootedSoundness fuel)
    (expressionSound : ActualInferExprFuelRootedSoundness fuel)
    (bodySound : ActualInferStatementsFuelRootedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {headerSpan : Syntax.SourceSpan}
    {initializer post : List Syntax.ForItem} {condition : Syntax.Expr} {body : Syntax.Block} {initial : State}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    statement.value = .forLoop headerSpan initializer condition post body →
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
  intro wholeContext inferenceContext wholeReturn expectedReturn statement headerSpan initializer post condition body
    initial result evidenceState roots finalized semanticSource frames semanticContext statementEq success resources
    interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical invariant actual
    operational returnAdmissible extension _semantic raw patterns literals requirements covered actualCovered
  generalize allocationEq : initial.allocateStatementId = pair
  obtain ⟨id, allocated⟩ := pair
  exact actualInferStatementFuel_success_forLoop_rooted statementEq allocationEq success resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical invariant actual operational
    returnAdmissible actualCovered extension (raw.finalized resources) raw patterns literals requirements covered
    itemsSound expressionSound bodySound itemsSound

end Solcore.SourceSemantics.SourceInferenceSoundness
