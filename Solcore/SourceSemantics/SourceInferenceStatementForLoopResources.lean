import Solcore.SourceSemantics.SourceInferenceRecursiveSoundness

/-!
Actual-source provenance for the four source-ordered traversals in a `for`
statement.  In particular, later post-header inference may refine the
condition's substitution, so the condition must be transported through the
whole trace before its typing theorem can use finalization.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

/-- The actual `for` condition's final state is an append-only prefix of its
completed statement source, with all three evidence ledgers retained and the
whole-body substitution extending its inference substitution. -/
theorem inferStatementFuel_success_forLoop_condition_resources
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {headerSpan : Syntax.SourceSpan}
    {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value =
      .forLoop headerSpan initializer condition post body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements) :
    ∃ initializerResult inferredCondition conditionState bodyResult postResult,
      Detail.inferForItemsFuel fuel inferenceContext initializer allocated =
        .ok initializerResult ∧
      Detail.inferExprFuel fuel inferenceContext condition (some .bool)
        initializerResult.state = .ok (inferredCondition, conditionState) ∧
      Detail.inferStatementsFuel fuel
        { inferenceContext with
          loopDepth := inferenceContext.loopDepth + 1 }
        body.value expectedReturn conditionState = .ok bodyResult ∧
      Detail.inferForItemsFuel fuel
        { inferenceContext with
          loopDepth := inferenceContext.loopDepth + 1 } post
        (bodyResult.state.restoreLexicalScope
          initializerResult.state.lexicalScope) = .ok postResult ∧
      initializerResult.state.NodesBelowNextOccurrence ∧
      finalized.substitution.SemanticallyExtends
        conditionState.inference.substitution ∧
      TypingSourceExtends (conditionState.toTypedSource roots)
        (result.state.toTypedSource roots) ∧
      conditionState.integerPatterns ⊆ evidenceState.integerPatterns ∧
      conditionState.integerLiterals ⊆ evidenceState.integerLiterals ∧
      conditionState.requirements ⊆ evidenceState.requirements := by
  obtain ⟨initializerResult, inferredCondition, conditionState, bodyResult,
    postResult, initializerSuccess, conditionSuccess, bodySuccess,
    postSuccess, resultEq, _contains⟩ :=
    inferStatementFuel_success_forLoop_facts statementEq allocationEq success
      roots
  obtain ⟨provenanceInitializer, provenanceCondition,
    provenanceConditionState, provenanceBody, provenancePost,
    provenanceInitializerSuccess, provenanceConditionSuccess,
    provenanceBodySuccess, provenancePostSuccess,
    initializerProvenance, bodyProvenance,
    postProvenance⟩ :=
    inferStatementFuel_success_forLoop_child_provenance statementEq
      allocationEq success initialInvariant.nodesBelow roots
  have initializerEq : provenanceInitializer = initializerResult := by
    rw [initializerSuccess] at provenanceInitializerSuccess
    exact (Except.ok.inj provenanceInitializerSuccess).symm
  subst provenanceInitializer
  have conditionPairEq :
      (provenanceCondition, provenanceConditionState) =
        (inferredCondition, conditionState) := by
    rw [conditionSuccess] at provenanceConditionSuccess
    exact (Except.ok.inj provenanceConditionSuccess).symm
  obtain ⟨rfl, rfl⟩ := conditionPairEq
  have bodyEq : provenanceBody = bodyResult := by
    rw [bodySuccess] at provenanceBodySuccess
    exact (Except.ok.inj provenanceBodySuccess).symm
  subst provenanceBody
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have initializerProperties := Detail.inferForItemsFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical
    initializerSuccess
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    initializerProperties.2 signatureFormation functionsCanonical
    (by
      intro expected member
      simp only [Option.mem_def] at member
      injection member with expectedEq
      subst expected
      simp [Ty.bool]) conditionSuccess
  have initializerReturnBelow : expectedReturn.VariablesBelow
      initializerResult.state.inference.next :=
    allocatedInvariant.returnBelow.weaken initializerProperties.1.next_le
  have conditionReturnBelow : expectedReturn.VariablesBelow
      conditionState.inference.next :=
    initializerReturnBelow.weaken conditionProperties.1.next_le
  have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
    (context := { inferenceContext with
      loopDepth := inferenceContext.loopDepth + 1 })
    conditionProperties.2.1 signatureFormation functionsCanonical
    conditionReturnBelow bodySuccess
  have postInputProperties := State.restoreLexicalScope_inferenceProperties
    initializerProperties.2
    (conditionProperties.1.trans bodyProperties.1)
  have postProperties := Detail.inferForItemsFuel_inferenceProperties
    (context := { inferenceContext with
      loopDepth := inferenceContext.loopDepth + 1 })
    postInputProperties.2 signatureFormation functionsCanonical postSuccess
  have postSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        postResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      resultSubstitutionExtension
  have bodySubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        bodyResult.state.inference.substitution := by
    have postInputSubstitutionExtension :=
      Substitution.SemanticallyExtends.trans postSubstitutionExtension
        postProperties.1.substitution_extends
    simpa [State.restoreLexicalScope] using postInputSubstitutionExtension
  have conditionSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        conditionState.inference.substitution :=
    Substitution.SemanticallyExtends.trans bodySubstitutionExtension
      bodyProperties.1.substitution_extends
  have conditionToBody : TypingSourceExtends
      (conditionState.toTypedSource roots)
      (bodyResult.state.toTypedSource roots) :=
    inferStatementsFuel_success_typingSourceExtends bodySuccess
      bodyProvenance.initialBelow roots
  have conditionToResult : TypingSourceExtends
      (conditionState.toTypedSource roots)
      (result.state.toTypedSource roots) :=
    conditionToBody.trans bodyProvenance.sourceExtension
  have bodyLiteralsSubset : bodyResult.state.integerLiterals ⊆
      result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    simpa [State.restoreLexicalScope, State.recordNode] using
      (Detail.inferForItemsFuel_integerLiterals_subset postSuccess
        (by simpa [State.restoreLexicalScope] using member))
  have conditionLiteralsSubset : conditionState.integerLiterals ⊆
      result.state.integerLiterals :=
    List.Subset.trans
      (Detail.inferStatementsFuel_integerLiterals_subset bodySuccess)
      bodyLiteralsSubset
  refine ⟨initializerResult, inferredCondition, conditionState, bodyResult,
    postResult, initializerSuccess, conditionSuccess, bodySuccess,
    postSuccess, ?_, conditionSubstitutionExtension, conditionToResult,
    ?_, ?_, ?_⟩
  · exact (Detail.inferForItemsFuel_occurrenceBoundExtends
      initializerSuccess).nodesBelowNextOccurrence
      initializerProvenance.initialBelow
  · exact List.Subset.trans
      (List.Subset.trans
        (Detail.inferStatementsFuel_integerPatterns_subset bodySuccess)
        bodyProvenance.integerPatternsSubset)
      integerPatternsSubset
  · exact List.Subset.trans conditionLiteralsSubset integerLiteralsSubset
  · exact List.Subset.trans
      (List.Subset.trans
        (Detail.inferStatementsFuel_requirements_subset bodySuccess)
        bodyProvenance.requirementsSubset)
      requirementsSubset

end Solcore.SourceSemantics.SourceInferenceSoundness
