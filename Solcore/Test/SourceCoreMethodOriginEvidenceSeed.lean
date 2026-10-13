import Solcore.Test.SourceCoreMethodOriginEvidenceCommon
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionInitial
import Solcore.Test.SourceCoreMethodOriginEvidenceResults
import Solcore.Test.SourceCoreMethodOriginEvidenceSelection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalBodyPublicInvocationBounds

/-! The initial method-bearing public call connects its actual bootstrap and input
encoding to the Source result and the full returned physical cache. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def ObservedPublicRun.as_function_call {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) :
    ObservedFunctionCall first.session observed.wordRow.row.key [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] :=
  ⟨⟨⟨first.checkpoint, first.started⟩, first.completion, first.executed⟩, first.handle, first.returned⟩

theorem ObservedPublicRun.initial_start {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) :
    Nonempty (RecursiveNamedPublicPhysicalSessionInitial.Started inventory.rows fixture.recipePrepared
      inventory.wordHeader.header first.as_function_call.toCall.toStartedCall) := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := fixture.actual_start first.opened first.started
  obtain ⟨selectedHeader, selected⟩ := RecursiveNamedPublicRootCoverage.selection_of_recipe
    prepared (List.mem_of_find?_eq_some started.selected) inventory.public_coverage
  have selectedEq : selectedHeader = inventory.wordHeader.header := by
    apply selected_word_root inventory.wordHeader inventory.boolHeader inventory.makeWordHeader inventory.makeBoolHeader inventory.relayWordHeader inventory.relayBoolHeader inventory.useWordHeader inventory.useBoolHeader inventory.identityWordHeader inventory.identityBoolHeader
      (root := root) (header := selectedHeader)
    · exact inventory.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.wordRow.row.key)) started.selected)
  subst selectedHeader
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
    (distinct : ([inventory.wordInput, inventory.boolInput, inventory.makeWordInput, inventory.makeBoolInput, inventory.relayWordInput, inventory.relayBoolInput, inventory.useWordInput, inventory.useBoolInput, inventory.identityWordInput, inventory.identityBoolInput].map (fun input => input.prepared.index)).Nodup)
    (program : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
      (headers inventory.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) receiver.completion)
    (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) :
    ∃ entry : RecursiveNamedPublicFunctionHistory.Entry,
      entry.sourceType = closureType .word ∧ entry.handle = first.handle ∧
      ∃ state : RetainedState inventory receiver first.completion.session [entry],
        SourceCall inventory inventory.wordHeader.header
          (RecursiveStageRegistry.scope stages.sidecar [] inventory.wordHeader.header.function)
          ⟨[]⟩ [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] (.value entry.source) state.heap := by
  obtain ⟨start⟩ := first.initial_start inventory
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      inventory.wordHeader.header.function.context [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] inventory.wordHeader.header.types := by
    rw [inventory.wordHeader.word_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  obtain ⟨entry, type, handle, state, trace⟩ :=
    RecursiveNamedPublicPhysicalSessionInitial.first_function inventory.rows fixture.recipePrepared
      inventory.wordHeader.header inventory.wordHeader.header program distinct first.as_function_call start
      (word_simple seed (Core.Word.ofNatModulo 33) true) inputTypes inputMeanings (stages.descriptor_at inventory.wordHeader)
      (RecursiveStageRegistry.scope stages.sidecar [] inventory.wordHeader.header.function)
  exact ⟨entry, type.trans inventory.wordHeader.word_result_type, handle, state, trace⟩

end Tests.SourceCoreMethodOriginEvidence
