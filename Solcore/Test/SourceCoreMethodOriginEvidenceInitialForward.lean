import Solcore.Test.SourceCoreMethodOriginEvidenceSeed
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionInitialForward
import Solcore.Test.SourceCoreMethodOriginEvidenceSelection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation

/-! Initial Source success determines sufficient execution and export budgets
at the original public checkpoint. Every sufficient output appends its actual
new closure handle and retains all installed method cells. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def InitialForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed) (receiver : ObservedReceiver fixture observed)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome first.artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      first.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion first.artifact,
        outcome = .succeeded completion ∧ completion.session.ExportsReady ∧
        ∃ entry : RecursiveNamedPublicFunctionHistory.Entry,
          entry.sourceType = closureType .word ∧ entry.source = source ∧
          completion.value = .function entry.handle ∧ entry.handle.sourceType = closureType .word ∧
          ∃ returned : RetainedState inventory receiver completion.session [entry], returned.heap = after

theorem forward_initial {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (inventory : OrdinaryInventory fixture observed)
    (distinct : ([inventory.wordInput, inventory.boolInput, inventory.makeWordInput, inventory.makeBoolInput, inventory.relayWordInput, inventory.relayBoolInput, inventory.useWordInput, inventory.useBoolInput, inventory.identityWordInput, inventory.identityBoolInput].map
      (fun input => input.prepared.index)).Nodup)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow)
    (program : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
      (headers inventory.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) receiver.completion)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall inventory inventory.wordHeader.header invocation ⟨[]⟩ [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] (.value source) after) :
    InitialForwardAt inventory receiver first source after := by
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
  have result : SourceCoreRawMetadata.runtimeType inventory.wordHeader.header.function.resultType =
      .function .unit .word := by
    rw [inventory.wordHeader.word_result_type]
    rfl
  have enough := RecursiveNamedPublicPhysicalSessionInitialForward.first_function
    inventory.rows fixture.recipePrepared inventory.wordHeader.header inventory.wordHeader.header
    program distinct first.as_function_call.toCall.toStartedCall start (word_simple seed (Core.Word.ofNatModulo 33) true)
    inputTypes inputMeanings result trace
  obtain ⟨requiredExecution, requiredOutput, enough⟩ := enough
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, succeeded, ready, entry, entryType, sourceEq, returned, handleType, state, heap⟩ :=
    enough executionFuel outputFuel outcome executionBound outputBound resumed
  exact ⟨completion, succeeded, ready, entry, entryType.trans inventory.wordHeader.word_result_type,
    sourceEq, returned, handleType.trans inventory.wordHeader.word_result_type, state, heap⟩

end Tests.SourceCoreMethodOriginEvidence
