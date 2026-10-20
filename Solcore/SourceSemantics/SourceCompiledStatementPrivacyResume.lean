import Solcore.SourceSemantics.SourceInferenceStatementPrivacyResume
import Solcore.SourceSemantics.SourceCompiledInitializerReturnPrivacy
import Solcore.SourceSemantics.SourceInferenceActiveQuantifierOrigins

/-! Actual statement prefixes in lambda bodies. The expected return type may
contain variables allocated before the body; each new declaration proves its
privacy from its real initializer and the selected finalizer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness ProtectedVariables

theorem statement_operational_return_privacy
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (scope : CheckingScope selected.toBodySelection inferenceContext)
    (ready : initial.InferenceReady)
    (operational : GeneralizedActualStateInvariant initial (evidenceSource selected.toBodySelection))
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (returnSafe : ∀ binder ∈ initial.localBinders,
      Safe binder.scheme.quantified initial expectedReturn)
    (retained : TypingSourceExtends (result.state.toTypedSource (bodyRoots selected.toBodySelection))
      (evidenceSource selected.toBodySelection))
    (extension : selected.body.finalized.substitution.SemanticallyExtends result.state.inference.substitution)
    (accepted : Detail.inferStatementFuel childFuel inferenceContext statement expectedReturn initial = .ok result) :
    GeneralizedActualStateInvariant result.state (evidenceSource selected.toBodySelection) ∧
      ∀ binder ∈ result.state.localBinders,
        Safe binder.scheme.quantified result.state expectedReturn := by
  have formation := scope.formation checked
  have canonical := scope.functionsCanonical checked
  have catalog := scope.catalog checked
  have afterPrivacy : ActiveQuantifiersPrivate result.state := by
    intro binder member
    rcases inferStatementFuel_quantified_origin accepted binder member with old | mono | created
    · exact (inferStatementFuel_private binder.scheme.quantified childFuel inferenceContext statement expectedReturn
        initial ready operational.requirements (operational.quantifiersBelow binder old)
        (operational.privacy binder old) catalog formation canonical returnBelow
        (returnSafe binder old) result accepted).2.2.1
    · rw [mono]
      exact liveBindersSafe_nil _
    · obtain ⟨initializerFuel, receipt, rfl⟩ := created
      have after := operational.ofInitializer receipt selected.body.resources ready catalog formation canonical
        retained.nodes_prefix retained extension
      exact after.privacy _ member
  obtain ⟨pending, ledger⟩ := operational.ledger
  have after : GeneralizedActualStateInvariant result.state (evidenceSource selected.toBodySelection) := {
    ledger := ⟨pending, (actualLedgerFamily childFuel).statements.statement accepted ledger⟩
    origins := inferStatementFuel_captureOrigins accepted operational.origins retained
    quantifiersBelow := activeQuantifiersBelowNext_inferStatementFuel operational.quantifiersBelow
      ready formation canonical returnBelow accepted
    privacy := afterPrivacy
    backed := operational.backed.inferStatementFuel ready formation canonical returnBelow accepted }
  refine ⟨after,?_⟩
  intro binder member
  rcases inferStatementFuel_quantified_origin accepted binder member with old | mono | created
  · exact (inferStatementFuel_private binder.scheme.quantified childFuel inferenceContext statement expectedReturn
      initial ready operational.requirements (operational.quantifiersBelow binder old)
      (operational.privacy binder old) catalog formation canonical returnBelow
      (returnSafe binder old) result accepted).1 _ (returnSafe binder old)
  · intro quantified occurs protectedMember
    simp [mono] at protectedMember
  · obtain ⟨initializerFuel, receipt, rfl⟩ := created
    let occurrence := InitializerOccurrence.ofReceipt checked scope receipt ready operational
      (retained.nodes_prefix.subset receipt.recorded) extension
    have safe := occurrence.generalized_type_safe checked scope ready operational returnBelow
    simpa only [occurrence, InitializerOccurrence.ofReceipt, Safe, State.resolve,
      InferState.resolve, receipt.inference_eq] using safe

def ResumeEntryInvariant
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} (selected : Selected compiled row fuel) (expected : Ty) (state : State) : Prop :=
  GeneralizedActualStateInvariant state (evidenceSource selected.toBodySelection) ∧
    (∀ binder ∈ state.localBinders, Safe binder.scheme.quantified state expected) ∧
    state.owner = (evidenceSource selected.toBodySelection).owner

theorem selected_statement_privacy_resume
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}
    {inferenceContext : SourceInference.Context} {sources : List Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : Detail.BlockResult}
    {index : Nat} {statement : Syntax.Statement}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (scope : CheckingScope selected.toBodySelection inferenceContext)
    (ready : initial.InferenceReady) (nodesBelow : initial.NodesBelowNextOccurrence)
    (entering : ResumeEntryInvariant selected expectedReturn initial)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (retained : result.state.nodes <+: selected.body.returned.nodes)
    (extension : selected.body.finalized.substitution.SemanticallyExtends result.state.inference.substitution)
    (accepted : Detail.inferStatementsFuel childFuel inferenceContext sources expectedReturn initial = .ok result)
    (position : sources[index]? = some statement) :
    Nonempty (StatementPrivacyResume inferenceContext statement expectedReturn initial result
      (ResumeEntryInvariant selected expectedReturn)) := by
  apply statementPrivacyResume_of_position_with_invariant ready entering.1.requirements nodesBelow
    (scope.catalog checked) (scope.formation checked) (scope.functionsCanonical checked)
    returnBelow accepted position entering
  intro stepFuel source before after beforeReady _ beforeBelow continuation afterRetained executed invariant
  have afterOwner := (Detail.inferStatementFuel_preserves_owner executed).trans invariant.2.2
  have afterSource : TypingSourceExtends (after.state.toTypedSource (bodyRoots selected.toBodySelection))
      (evidenceSource selected.toBodySelection) :=
    ⟨afterOwner.symm, afterRetained.trans retained⟩
  have afterInvariant := statement_operational_return_privacy checked scope beforeReady invariant.1
    beforeBelow invariant.2.1 afterSource (extension.trans continuation.substitution_extends) executed
  exact ⟨afterInvariant.1,afterInvariant.2,afterOwner⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
