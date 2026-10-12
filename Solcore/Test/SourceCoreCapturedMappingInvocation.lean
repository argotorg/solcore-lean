import Solcore.Test.SourceCoreCapturedMappingCommon
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryReflection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning

/-! Mapping inputs use the actual metadata encoder and its authentic receiver.
Each returned state retains that receiver for the following public call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedMapping
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def publicArgument (rows : List (Core.Word × Core.Word)) : SourceCorePublicValues.Value :=
  .mapping .word .word (rows.map (fun row => (.word row.1, .word row.2)))

def sourceArgument (rows : List (Core.Word × Core.Word)) : Dynamic.Value :=
  .mapping .word .word (rows.map (fun row => (.word row.1, .word row.2)))

theorem mapping_input {entries : List Entry} {context : SourceSemantics.Context}
    (rows : List (Core.Word × Core.Word)) :
    RecursiveNamedPublicFunctionHistoryInputs.Input entries context (.mapping .word .word)
      (publicArgument rows) (sourceArgument rows) := by
  apply RecursiveNamedPublicFunctionHistoryInputs.Input.mapping
  induction rows with
  | nil => exact .empty _ _
  | cons row rest ih =>
    exact .entry (.data ⟨.word row.1, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word row.1⟩ ⟨.word row.1, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word row.1⟩)
      (.data ⟨.word row.2, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word row.2⟩ ⟨.word row.2, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word row.2⟩) ih

structure ObservedInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : List (Core.Word × Core.Word)) where
  completion : SourceCoreExecution.Completion artifact
  executed : session.InvokeAt handle (publicArgument argument) runOptions (.ok (.succeeded completion))

def observeInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : List (Core.Word × Core.Word)) : IO (ObservedInvocation session handle argument) := do
  let executed ← session.invokePackedWithReceipt handle (publicArgument argument) runOptions
  match result : executed.val with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (.failed _ _) => throw (IO.userError "mapping captured call failed")
  | .ok (.exportError error _) => throw (IO.userError (reprStr error))
  | .ok (.outOfFuel _) => throw (IO.userError "mapping captured call exhausted")
  | .ok (.succeeded completion) => return ⟨completion, result ▸ executed.property⟩

def SourceInvocation {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (source : Dynamic.Value)
    (argument : List (Core.Word × Core.Word)) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
    support.actual.header.function.context before source [sourceArgument argument] outcome after

/-- Current history supplies the callee; literal input rows supply its argument.
No registry equality, arbitrary receiving table or metadata extension is assumed. -/
theorem invoke {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries)
    (entryType : entry.sourceType = .function (.mapping .word .word) .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = .function (.mapping .word .word) .word)
    {argument : List (Core.Word × Core.Word)} (call : ObservedInvocation publicSession handle argument)
    {word : Core.Word} (returned : call.completion.value = .word word)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.completion.session entries,
      SourceInvocation support invocation state.heap entry.source argument (.value (.word word)) after.heap := by
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨receiving, checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
      nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, outcome,
      after, finalMap, finalWorld, reached, contextAt, issued, extended, _diagnostics,
      started, _parameterView, _resultView, succeeded, actualAt, packing, trace, result,
      _related, retained, returnedRegistry⟩ :=
    RecursiveNamedPublicActualRegistryReflection.public_invoke_succeeded
      (completion := state.receiving) state.issued (actualStagePrepared fixture) observed.profile
      support.observations semantic support.family
      (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member))
      support.supports fixture.source_wellFormed state.history entry member entryType
      (mapping_input argument) state.atRecipe state.registry state.atSession
      (by simpa only [entryHandle] using call.executed) invocation
  have handleType : entry.handle.sourceType = .function (.mapping .word .word) .word := entryHandle ▸ handleType
  have requested := started.requested_exact handleType
  have signature := started.selected.signature handleType
  have projected := started.resultProjection
  rw [signature.2] at projected
  have nativeResultEq : nativeResult = .word := (Except.ok.inj projected).symm
  rw [nativeResultEq] at result
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.represented_word succeeded requested
    (actualAt.1.symm.trans returned) result.1
  have sourcesEq : sources = [sourceArgument argument] := by
    cases packing
    rfl
  let next : RetainedState support call.completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := retained }
  exact ⟨next, sourceSize, by simpa only [sourcesEq, outcomeValue] using trace⟩

end Tests.SourceCoreCapturedMapping
