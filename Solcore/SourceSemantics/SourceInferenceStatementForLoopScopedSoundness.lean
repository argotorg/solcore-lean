import Solcore.SourceSemantics.SourceInferenceStatementForLoopAssembly
import Solcore.SourceSemantics.SourceInferenceStatementForLoopConditionSoundness
import Solcore.SourceSemantics.SourceInferenceStatementForLoopChildProgress
import Solcore.SourceSemantics.SourceInferenceForItemsCoverage

/-!
The recursive `for` statement step.  Each induction hypothesis is invoked
only on the actual initializer, condition, body, or post-header trace exposed
by the successful parent computation.  The completed local statement source
is separate from the whole-body finalization and coverage evidence.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

/-- Scoped soundness of one successful `for` statement, conditional only on
the four smaller-fuel recursive soundness propositions. -/
theorem inferStatementFuel_success_forLoop_scoped
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
    (statementEq : statement.value =
      .forLoop headerSpan initializer condition post body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
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
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource)
    (rawResultExtension : TypingSourceExtends
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (initializerSound : InferForItemsFuelScopedSoundness fuel)
    (expressionSound : InferExprFuelScopedSoundness fuel)
    (bodySound : InferStatementsFuelScopedSoundness fuel)
    (postSound : InferForItemsFuelScopedSoundness fuel) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
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
  have headerCovered := forItemsReferencesCovered_of_recordedForLoop
    containsRaw rfl resultExtension resources.graph_closed parentCovered
  have headerBindings := forItemsBindingsRetained_of_containedForLoop
    containsRaw rawResultExtension
  have initializerSourceOwner :
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution).owner = allocated.owner := by
    have ownerToInitializer := initializerProvenance.sourceExtension.owner_eq
    have initializerOwner :=
      Detail.inferForItemsFuel_preserves_owner initializerSuccess
    simpa [State.toTypedSource] using ownerToInitializer.trans initializerOwner
  obtain ⟨loopContext, initializerInvariant, initializerTyping⟩ :=
    (initializerSound (control := {
        returnType := finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth })
      initializerSuccess resources signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters allocatedInvariant initializerSubstitutionExtension
      (initializerProvenance.sourceExtension.applySubstitution
        finalized.substitution) resultExtension
      (initializerProvenance.sourceExtension.trans rawResultExtension)
      (List.Subset.trans initializerProvenance.integerPatternsSubset
        integerPatternsSubset)
      (List.Subset.trans initializerLiteralsParent integerLiteralsSubset)
      (List.Subset.trans initializerProvenance.requirementsSubset
        requirementsSubset)
      initializerSourceOwner headerCovered.1 headerBindings.1)
  have loopAssumptionsEq : loopContext.assumptions =
      semanticContext.assumptions :=
    forItemsHaveType_assumptions_eq initializerTyping
  have conditionTyping :=
    inferStatementFuel_success_forLoop_condition_scoped statementEq
      allocationEq success initializerSuccess conditionSuccess resources
      signaturesEq ownerEq parametersEq assumptionsEq signatureFormation
      functionsCanonical catalog signatureParameters initialInvariant
      initializerInvariant resultSubstitutionExtension resultExtension
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
  have bodyCovered : ∀ child, child ∈ bodyResult.statements →
      TemplateScopeCovered finalized.typedSource loopContext
        (.statement child) := by
    intro child member
    have childReference : (.statement child : NodeId) ∈
        (StatementForm.forLoop initializerResult.items inferredCondition.id
          postResult.items bodyResult.statements).references := by
      simp [StatementForm.references, member]
    apply TemplateScopeCovered.statementChild_of_recorded_reference
      containsRaw childReference resultExtension parentCovered
      resources.graph_closed
    intro predicate predicateMember
    simpa [loopAssumptionsEq] using predicateMember
  obtain ⟨bodyFinal, bodyFacts, bodyInvariant, bodyTyping,
    bodyAgreement⟩ :=
    bodySound bodySuccess resources
      (by simpa using signaturesEq)
      (by simpa using ownerEq)
      (by simpa using parametersEq)
      (by simpa using assumptionsEq)
      signatureFormation functionsCanonical catalog signatureParameters
      conditionInvariant bodySubstitutionExtension
      (bodyProvenance.sourceExtension.applySubstitution
        finalized.substitution) resultExtension
      (bodyProvenance.sourceExtension.trans rawResultExtension)
      (List.Subset.trans bodyProvenance.integerPatternsSubset
        integerPatternsSubset)
      (List.Subset.trans bodyLiteralsParent integerLiteralsSubset)
      (List.Subset.trans bodyProvenance.requirementsSubset
        requirementsSubset)
      bodyCovered
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
  obtain ⟨postContext, postInvariant, postTyping⟩ :=
    (postSound (control := ({
        returnType := finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth } : ControlContext).enterLoop)
      postSuccess resources
      (by simpa using signaturesEq)
      (by simpa using ownerEq)
      (by simpa using parametersEq)
      (by simpa using assumptionsEq)
      signatureFormation functionsCanonical catalog signatureParameters
      postInputInvariant postSubstitutionExtension
      (postProvenance.sourceExtension.applySubstitution
        finalized.substitution) resultExtension
      (postProvenance.sourceExtension.trans rawResultExtension)
      (List.Subset.trans postProvenance.integerPatternsSubset
        integerPatternsSubset)
      (List.Subset.trans postLiteralsParent integerLiteralsSubset)
      (List.Subset.trans postProvenance.requirementsSubset
        requirementsSubset)
      postSourceOwner postCovered headerBindings.2)
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

end Solcore.SourceSemantics.SourceInferenceSoundness
