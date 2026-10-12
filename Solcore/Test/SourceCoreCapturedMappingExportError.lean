import Solcore.Test.SourceCoreCapturedMappingPublicExecution
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryExportErrors

/-! A native mapping-input call completes but export fuel is zero. The next
call uses the exact session returned by exportError and the earlier closure. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedMapping
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def zeroOutputOptions : SourceCoreExecution.RunOptions :=
  { runOptions with outputValidationFuel := 0 }

structure ObservedExportError {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : List (Core.Word × Core.Word)) where
  error : SourceCoreIndexedSession.Error
  returned : SourceCoreExecution.Session artifact
  executed : session.InvokeAt handle (publicArgument argument) zeroOutputOptions
    (.ok (.exportError error returned))

def observeExportError {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : List (Core.Word × Core.Word)) : IO (ObservedExportError session handle argument) := do
  let executed ← session.invokePackedWithReceipt handle (publicArgument argument) zeroOutputOptions
  match result : executed.val with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (.failed _ _) => throw (IO.userError "mapping call failed before export")
  | .ok (.outOfFuel _) => throw (IO.userError "mapping execution fuel exhausted")
  | .ok (.succeeded _) => throw (IO.userError "zero output fuel unexpectedly exported a value")
  | .ok (.exportError error returned) => return ⟨error, returned, result ▸ executed.property⟩

/-- The exported session carries the completed Source heap even though no new
public value was produced. The existing handle remains in the same history. -/
theorem export_error_meaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries)
    (entryType : entry.sourceType = .function (.mapping .word .word) .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    {argument : List (Core.Word × Core.Word)} (call : ObservedExportError publicSession handle argument)
    (exportsReady : publicSession.ExportsReady) (invocation : Staging.Recursive.Scope) :
    ∃ source : Dynamic.Value, ∃ after : RetainedState support call.returned entries,
      SourceInvocation support invocation state.heap entry.source argument (.value source) after.heap ∧
      call.returned.ExportsReady := by
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨receiving, checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
      nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, source,
      after, finalMap, finalWorld, reached, contextAt, issued, extended, _diagnostics,
      _started, _parameterView, _resultView, _exported, actualAt, packing, trace, _result,
      _related, retained, returnedRegistry, returnedReady⟩ :=
    RecursiveNamedPublicActualRegistryExportErrors.public_invoke_export_error
      (completion := state.receiving) state.issued (actualStagePrepared fixture) observed.profile
      support.observations semantic support.family
      (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member))
      support.supports fixture.source_wellFormed state.history entry member entryType
      (mapping_input argument) state.atRecipe state.registry (state.atSession.exportsReady_iff.mp exportsReady)
      state.atSession (by simpa only [entryHandle] using call.executed) invocation
  have sourcesEq : sources = [sourceArgument argument] := by cases packing; rfl
  let next : RetainedState support call.returned entries := {
    artifact := state.artifact
    session := actual
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := retained }
  exact ⟨source, next, ⟨sourceSize, by simpa only [sourcesEq] using trace⟩,
    actualAt.exportsReady_iff.mpr returnedReady⟩

structure ObservedExportSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  factory : ObservedPublicRun fixture observed
  noOutput : ObservedExportError factory.completion.session factory.handle firstArgument
  continued : ObservedInvocation noOutput.returned factory.handle secondArgument
  finalValue : continued.completion.value = .word seed

def observeExportSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedExportSequence fixture observed) := do
  let factory ← observePublicRun fixture observed
  let noOutput ← observeExportError factory.completion.session factory.handle firstArgument
  let continued ← observeInvocation noOutput.returned factory.handle secondArgument
  if finalValue : continued.completion.value = .word seed then
    return ⟨factory, noOutput, continued, finalValue⟩
  else throw (IO.userError "export error lost the original captured seed")

/-- The actual compiler and bootstrap supply all static and initial-state
facts. The failed export and following successful call share the same Source
heap and authenticated closure; no native completion is assumed separately. -/
theorem closed_export_sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (sequence : ObservedExportSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed) (support : PublicSupports receiver),
      let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
      ∃ (entry : Entry) (source : Dynamic.Value),
        entry.sourceType = .function (.mapping .word .word) .word ∧ entry.handle = sequence.factory.handle ∧
      ∃ initial : RetainedState support sequence.factory.completion.session [entry],
      ∃ noOutput : RetainedState support sequence.noOutput.returned [entry],
      ∃ final : RetainedState support sequence.continued.completion.session [entry],
        SourceCall support support.actual.header scope ⟨[]⟩ [.word seed] (.value entry.source) initial.heap ∧
        SourceInvocation support scope initial.heap entry.source firstArgument (.value source) noOutput.heap ∧
        sequence.noOutput.returned.ExportsReady ∧
        SourceInvocation support scope noOutput.heap entry.source secondArgument (.value (.word seed)) final.heap := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  obtain ⟨support⟩ := static_supports fixture observed stages receiver.completion.result.context.registry receiver.issued
  let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
  obtain ⟨entry, entryType, handle, handleType, initial, factoryTrace⟩ := first_meaning support stages sequence.factory
  have ready := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.factory.ready).exportsReady sequence.factory.authority
  have factoryReady := sequence.factory.executed.exportsReady ready
  obtain ⟨source, noOutput, firstTrace, returnedReady⟩ :=
    export_error_meaning initial entry (by simp) entryType handle sequence.noOutput factoryReady scope
  obtain ⟨final, finalTrace⟩ := invoke noOutput entry (by simp) entryType handle handleType
    sequence.continued sequence.finalValue scope
  exact ⟨receiver, support, entry, source, entryType, handle, initial, noOutput, final,
    factoryTrace, firstTrace, returnedReady, finalTrace⟩

def runExportError : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeExportSequence fixture observed
  have _meaning := closed_export_sequence_meaning fixture observed stages sequence
  IO.println "Actual exportError continuation: output fuel 0, retained mapping-call effects, earlier closure returns 10"

end Tests.SourceCoreCapturedMapping
