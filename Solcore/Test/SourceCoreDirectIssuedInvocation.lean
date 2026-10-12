import Solcore.Test.SourceCoreDirectIssuedIssuance
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallablePublicHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning

/-! The same public proof consumes actual named and builtin handles. Argument
and callee representations are derived from their current retained history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreDirectIssued
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open RecursiveNamedPublicFunctionHistory (Entry)

def SourceInvocation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (source argument : Dynamic.Value)
    (word : Core.Word) (after : Dynamic.Heap) : Prop :=
  ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
    support.makeHeader.header.function.context before source [argument] (.value (.word word)) after

/-- Exact observed public completion fixes the Source result; structural input
receipts and the actual packed encoder fix the Source argument. -/
theorem invoke {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) {parameter : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = .function parameter .word)
    {argument : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context parameter argument source)
    (simple : SourceCoreIndexedSession.FunctionTreeSimple argument)
    (singleton : ∀ sources, Dynamic.ValuesPack sources source → sources = [source])
    (call : ObservedInvocation publicSession handle argument)
    {word : Core.Word} (returned : call.completion.value = .word word)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.completion.session entries,
      SourceInvocation support invocation state.heap entry.source source word after.heap := by
  obtain ⟨checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
      nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, outcome,
      after, finalMap, finalWorld, reached, started, _parameterView, _resultView, succeeded,
      actualAt, packing, trace, result, _related, retained, _encodedRegistry, returnedRegistry⟩ :=
    RecursiveNamedPublicDirectCallablePublicHistory.public_invoke_succeeded_function_tree
      (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion)
      (receiver := CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
      (stagePrepared := actualStagePrepared fixture) (profile := observed.profile)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (history := state.history)
      (entry := entry) (member := member) (entryType := entryType)
      (input := input) (atRecipe := state.atRecipe)
      state.registry receiver.completion.result.extension simple
      state.atSession (by simpa only [entryHandle] using call.executed) invocation
  have handleType : entry.handle.sourceType = .function parameter .word := entryHandle ▸ handleType
  have requested := started.requested_exact handleType
  have signature := started.selected.signature handleType
  have projected := started.resultProjection
  rw [signature.2] at projected
  have nativeResultEq : nativeResult = .word := (Except.ok.inj projected).symm
  rw [nativeResultEq] at result
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.represented_word succeeded requested
    (actualAt.1.symm.trans returned) result.1
  have sourcesEq := singleton sources packing
  let next : RetainedState support call.completion.session entries :=
    ⟨state.artifact, actual.session, finalMap, finalWorld, after, finalStore, reached,
      actualAt.2.2.2, state.atRecipe, returnedRegistry, retained⟩
  refine ⟨next, sourceSize, ?_⟩
  simpa only [sourcesEq, outcomeValue] using trace

end Tests.SourceCoreDirectIssued
