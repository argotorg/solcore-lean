import Solcore.Test.SourceCoreDirectOutputIssuance
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableOutputHistory

/-! A directly invoked factory's actual exported function is collected into
its current history, retaining the Source value from that same call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreDirectOutput
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicOutputSelections (Selection Selected)

private theorem selected_function {raw : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {handle : SourceCorePublicValues.Handle} (same : value = .function handle)
    {source : Dynamic.Value} {native : Core.Value} {nativeType : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : Selected (same.symm ▸ (Selection.function (type := raw))) source native nativeType fuel entries) :
    entries = [⟨raw, source, handle, native, nativeType, fuel⟩] := by
  cases same
  cases selected
  rfl

/-- The returned singleton is taken from the genuine codec selection and
successful Source trace; its capture is never reconstructed from a new run. -/
theorem invoke_factory {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (named : Entry) (member : named ∈ entries)
    (namedType : named.sourceType = .function .word (.function .unit .word))
    (namedSource : named.source = .global (CallableNamedReversal.global (CallableNamedMetadata.global
      support.makePacket.header.named.specialized support.makeInput.prepared.available)))
    {handle : SourceCorePublicValues.Handle} (namedHandle : named.handle = handle)
    (handleType : handle.sourceType = .function .word (.function .unit .word))
    (call : ObservedFunctionInvocation publicSession handle) (invocation : Staging.Recursive.Scope) :
    ∃ entry : Entry,
      entry.sourceType = .function .unit .word ∧ entry.handle = call.handle ∧
      call.handle.sourceType = .function .unit .word ∧
      ∃ next : RetainedState support call.completion.session (entries ++ [entry]),
        SourceCall support support.makeHeader.header invocation state.heap [.word secondSeed]
          (.value entry.source) next.heap := by
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context .word (.word secondSeed) (.word secondSeed) :=
    .data ⟨.word secondSeed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word secondSeed⟩
      ⟨.word secondSeed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word secondSeed⟩
  let selection : Selection (.function .unit .word) call.completion.value :=
    call.returned.symm ▸ Selection.function
  obtain ⟨checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
      nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, source,
      payload, after, finalMap, finalWorld, reached, added, started, _parameterView, _resultView,
      succeeded, actualAt, packing, trace, result, nativeValue, selected, _handles, _related,
      retained, _encodedRegistry, returnedRegistry⟩ :=
    RecursiveNamedPublicDirectCallableOutputHistory.public_invoke_succeeded_collects_function_tree
      (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion)
      (receiver := CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
      (stagePrepared := actualStagePrepared fixture) (profile := observed.profile)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (history := state.history)
      (entry := named) (member := member) (entryType := namedType)
      (input := input) (atRecipe := state.atRecipe)
      state.registry receiver.completion.result.extension (.simple (.word secondSeed))
      state.atSession (by simpa only [namedHandle] using call.executed) selection invocation
  have handleType : named.handle.sourceType = .function .word (.function .unit .word) := namedHandle ▸ handleType
  have requested := started.requested_exact handleType
  have returnedType := succeeded.function_source_type requested (actualAt.1.symm.trans call.returned)
  have sourcesEq : sources = [.word secondSeed] := by cases packing; rfl
  have addedEq := selected_function call.returned selected
  rw [addedEq] at retained
  let entry : Entry := ⟨.function .unit .word, source, call.handle, payload, nativeResult,
    runOptions.outputValidationFuel⟩
  let next : RetainedState support call.completion.session (entries ++ [entry]) :=
    ⟨state.artifact, actual.session, finalMap, finalWorld, after, finalStore, reached,
      actualAt.2.2.2, state.atRecipe, returnedRegistry, retained⟩
  refine ⟨entry, rfl, rfl, returnedType, next, support.makeInput.prepared.available,
    CallableNamedReversal.global (CallableNamedMetadata.global
      support.makePacket.header.named.specialized support.makeInput.prepared.available), sourceSize, ?_, ?_⟩
  · rw [support.makeEq]
    exact support.makePacket.sourceAt
  · simpa only [namedSource, sourcesEq] using trace

end Tests.SourceCoreDirectOutput
