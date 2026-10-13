import Solcore.Test.SourceCoreCoercionPublicCommon
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionInitial
import Solcore.Test.SourceCoreCoercionPublicResults
import Solcore.Test.SourceCoreCoercionPublicSelection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalBodyPublicInvocationBounds

/-! The initial method-bearing public call connects its actual bootstrap and input
encoding to the Source result and the full returned physical cache. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def ObservedPublicRun.as_function_call {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (first : ObservedPublicRun fixture observed.makeRow.toObservedRow) :
    ObservedFunctionCall first.session observed.makeRow.row.key [.bool true] :=
  ⟨⟨⟨first.checkpoint, first.started⟩, first.completion, first.executed⟩, first.handle, first.returned⟩

theorem ObservedPublicRun.initial_start {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed)
    (first : ObservedPublicRun fixture observed.makeRow.toObservedRow) :
    Nonempty (RecursiveNamedPublicPhysicalSessionInitial.Started inventory.rows fixture.recipePrepared
      inventory.makeHeader.header first.as_function_call.toCall.toStartedCall) := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := fixture.actual_start first.opened first.started
  have selected := inventory.selected_row_issued observed.makeRow.toObservedRow
    inventory.makeHeader inventory.make_member inventory.makeSlot
    (SourceCoreIndexedSession.Recipe.prepare_roots prepared (List.mem_of_find?_eq_some started.selected))
    (of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
      decide (candidate.key = observed.makeRow.row.key)) started.selected))
  exact ⟨{
    publicCompiled := fixture.facadeCompiled
    artifact := artifact, nativeSession := session, checkpoint := checkpoint, root := root
    world := world, store := store, native := native, encodedValues := encodedValues
    opened := opened, atSession := sessionAt, atCheckpoint := checkpointAt
    started := started, selected := selected, bootstrap := first.bootstrap
    bootstrapFuel := 102400, fresh := first.fresh, authority := first.authority
    ready := .single first.ready }⟩

theorem first_meaning_typed_handle {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (inventory : OrdinaryInventory fixture observed)
    (distinct : ([inventory.makeInput, inventory.useInput, inventory.keepInput].map (fun input => input.prepared.index)).Nodup)
    (program : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
      (headers inventory.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) receiver.completion)
    (stages : ObservedStages fixture observed.makeRow.toObservedRow)
    (first : ObservedPublicRun fixture observed.makeRow.toObservedRow) :
    ∃ entry : RecursiveNamedPublicFunctionHistory.Entry,
      entry.sourceType = closureType .word ∧ entry.handle = first.handle ∧
      ∃ state : RetainedState inventory receiver first.completion.session [entry],
        SourceCall inventory inventory.makeHeader.header
          (RecursiveStageRegistry.scope stages.sidecar [] inventory.makeHeader.header.function)
          ⟨[]⟩ [.bool true] (.value entry.source) state.heap := by
  obtain ⟨start⟩ := first.initial_start inventory
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      inventory.makeHeader.header.function.context [.bool true] inventory.makeHeader.header.types := by
    rw [inventory.makeHeader.make_types]
    exact .cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool true] [.bool true] :=
    .cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil
  obtain ⟨entry, type, handle, state, trace⟩ :=
    RecursiveNamedPublicPhysicalSessionInitial.first_function inventory.rows fixture.recipePrepared
      inventory.makeHeader.header inventory.makeHeader.header program distinct first.as_function_call start
      (bool_simple true) inputTypes inputMeanings (stages.descriptor_at inventory.makeHeader)
      (RecursiveStageRegistry.scope stages.sidecar [] inventory.makeHeader.header.function)
  exact ⟨entry, type.trans inventory.makeHeader.make_result_type, handle, state, trace⟩

end Tests.SourceCoreCoercionPublic
