import Solcore.SourceSemantics.SourceInferenceSelectedStatementState
import Solcore.SourceSemantics.SourceInferenceActualRootedContracts

/-! Actual control statements without child inference retain the current
source context and operational state conditions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferStatementFuel_returnUnit_atomicBranch
    {fuel : Nat} {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial allocated evidenceState : State} {id : StatementId}
    {result : Detail.StatementResult} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .returnStmt none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation : ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (initialInvariant : RecursiveStatementInvariant wholeContext expectedReturn
      finalized initial semanticContext)
    (actual : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution result facts := by
  obtain ⟨active, statementType, agreement⟩ :=
    inferStatementFuel_success_returnUnit_sound statementEq allocationEq success
      initialInvariant.active resultSubstitutionExtension roots
  have allocationScope := congrArg LexicalScope.binders
    (Detail.allocateStatementId_success_lexicalScope allocationEq)
  obtain ⟨unified, unifiedSuccess, _, resultEq, _⟩ :=
    inferStatementFuel_success_returnUnit_facts statementEq allocationEq success roots
  have unifiedScope := congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope unifiedSuccess)
  have bindersEq : result.state.localBinders = initial.localBinders := by
    simpa only [resultEq, State.recordNode, State.lexicalScope] using unifiedScope.trans allocationScope
  have properties := Detail.inferStatementFuel_inferenceProperties initialInvariant.ready
    signatureFormation functionsCanonical initialInvariant.returnBelow success
  have finalInvariant := initialInvariant.of_statement_typing success signatureFormation functionsCanonical
    active (inferStatementFuel_preserves_localBindersBelowNextLocal initialInvariant.bindersBelow success)
    resultSubstitutionExtension (activeSchemeQuantifierIsolation_transport initialInvariant.schemeIsolation bindersEq)
    statementType
  exact ⟨semanticContext, _, finalInvariant, actual,
    operational.ofStatementPreservingBinders success bindersEq properties.1.next_le, statementType, agreement⟩

theorem actualInferStatementFuel_break_atomicBranch
    {fuel : Nat} {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial allocated evidenceState : State} {id : StatementId}
    {result : Detail.StatementResult} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .breakStmt)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation : ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (initialInvariant : RecursiveStatementInvariant wholeContext expectedReturn
      finalized initial semanticContext)
    (actual : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution result facts := by
  obtain ⟨active, statementType, agreement⟩ :=
    inferStatementFuel_success_break_sound statementEq allocationEq success
      initialInvariant.active roots
  have allocationScope := congrArg LexicalScope.binders
    (Detail.allocateStatementId_success_lexicalScope allocationEq)
  obtain ⟨_, resultEq, _⟩ :=
    inferStatementFuel_success_break_facts statementEq allocationEq success roots
  have bindersEq : result.state.localBinders = initial.localBinders := by
    simpa only [resultEq, State.recordNode, State.lexicalScope] using allocationScope
  have properties := Detail.inferStatementFuel_inferenceProperties initialInvariant.ready
    signatureFormation functionsCanonical initialInvariant.returnBelow success
  have finalInvariant := initialInvariant.of_statement_typing success signatureFormation functionsCanonical
    active (inferStatementFuel_preserves_localBindersBelowNextLocal initialInvariant.bindersBelow success)
    resultSubstitutionExtension (activeSchemeQuantifierIsolation_transport initialInvariant.schemeIsolation bindersEq)
    statementType
  exact ⟨semanticContext, _, finalInvariant, actual,
    operational.ofStatementPreservingBinders success bindersEq properties.1.next_le, statementType, agreement⟩

theorem actualInferStatementFuel_continue_atomicBranch
    {fuel : Nat} {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial allocated evidenceState : State} {id : StatementId}
    {result : Detail.StatementResult} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .continueStmt)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation : ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (initialInvariant : RecursiveStatementInvariant wholeContext expectedReturn
      finalized initial semanticContext)
    (actual : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution result facts := by
  obtain ⟨active, statementType, agreement⟩ :=
    inferStatementFuel_success_continue_sound statementEq allocationEq success
      initialInvariant.active roots
  have allocationScope := congrArg LexicalScope.binders
    (Detail.allocateStatementId_success_lexicalScope allocationEq)
  obtain ⟨_, resultEq, _⟩ :=
    inferStatementFuel_success_continue_facts statementEq allocationEq success roots
  have bindersEq : result.state.localBinders = initial.localBinders := by
    simpa only [resultEq, State.recordNode, State.lexicalScope] using allocationScope
  have properties := Detail.inferStatementFuel_inferenceProperties initialInvariant.ready
    signatureFormation functionsCanonical initialInvariant.returnBelow success
  have finalInvariant := initialInvariant.of_statement_typing success signatureFormation functionsCanonical
    active (inferStatementFuel_preserves_localBindersBelowNextLocal initialInvariant.bindersBelow success)
    resultSubstitutionExtension (activeSchemeQuantifierIsolation_transport initialInvariant.schemeIsolation bindersEq)
    statementType
  exact ⟨semanticContext, _, finalInvariant, actual,
    operational.ofStatementPreservingBinders success bindersEq properties.1.next_le, statementType, agreement⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
