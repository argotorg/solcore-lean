import Solcore.Test.SourceCoreDirectFailureCommon
import Solcore.Test.SourceCoreInitialLexicalFailureSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedHistoryFailures
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreDirectFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem first_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver)
    (stages : ObservedStages fixture observed.failedRow)
    (first : ObservedPublicRun fixture observed) :
    ∃ state : RetainedState support first.returned [],
      ∃ failure : Staging.Recursive.Failure,
        SourceCall support support.failedHeader.header
          (RecursiveStageRegistry.scope stages.sidecar [] support.failedHeader.header.function)
          ⟨[]⟩ [] (.fault failure) state.heap := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := first.start_receipt
  have startupRegistry := first.metadata_at_start opened sessionAt started
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.failedHeader.header := by
    apply selected_failed_root support.failedHeader support.identityHeader (root := root)
      (support.header_list ▸ selected)
    exact of_decide_eq_true (List.find?_some
      (p := fun root : SourceCoreIndexedSession.Root fixture.recipe.compiled => decide (root.key = observed.failedRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.failedHeader.header.function.context
      (support.failedHeader.header.bindings.map (fun binding => binding.1.scheme.body)) [] [] := by
    rw [support.failedHeader.failed_inputs]
    exact .nil
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.failedHeader.header support.failedInput.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global support.failedPacket.header.named.specialized support.failedInput.prepared.available)) := by
    rw [support.failedEq]
    exact support.failedPacket.sourceAt
  obtain ⟨caller, returnedSession, value, finalStore, capture, sourceSize, failure, after,
      finalMap, finalWorld, failed, returnedAt, trace, _fullResult, returnedCaller, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedHistoryFailures.public_run_failed_seeds
      (inputs := [support.failedInput, support.identityInput]) (rows := support.rows) (distinct := support.distinct)
      (stagePrepared := actualStagePrepared fixture)
      (completion := receiver.completion)
      (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := .single first.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (atCheckpoint := checkpointAt) (started := started) (inputReceipts := inputs)
      (metadata := metadata) (sourceAt := sourceAt)
      (invocation := RecursiveStageRegistry.scope stages.sidecar [] support.failedHeader.header.function)
      first.started first.executed support.failedDescriptor
  have returnedRegistry : returnedSession.RegistryAt encodedValues.registry := by
    have values := failed.2.2.2.2.1.trans started.values
    cases checkpoint
    exact congrArg SourceCoreCompatibleValues.Context.registry values
  rw [startupRegistry] at returnedRegistry
  let state : RetainedState support first.returned [] := {
    artifact := artifact, session := returnedSession, mapping := finalMap, world := finalWorld
    heap := after, store := finalStore, caller := returnedCaller
    atSession := returnedAt, atRecipe := started.recipe_eq, registry := returnedRegistry, history := retained }
  exact ⟨state, failure, support.failedInput.prepared.available, _, sourceSize, sourceAt, trace⟩

end Tests.SourceCoreDirectFailure
