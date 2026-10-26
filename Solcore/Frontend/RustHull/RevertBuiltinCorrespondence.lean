import Solcore.Frontend.RustHull.RevertCorrespondence
import Solcore.Frontend.RustHull.RevertSemantics
import Solcore.Frontend.RustHull.RuntimeChildCallTerminationCorrespondence
import Solcore.Frontend.RustHull.MemoryEffectCorrespondence

/-! Hull's explicit revert through the actual `Effects.revertMessage` code. The
message word the lowering computes is the specified left-aligned word, the
actual `mstore` code writes it at offset zero, and the actual revert
termination records the exit and the message range. The frame model, catalog
links and captured context survive. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RevertBuiltinCorrespondence
open Core Correspondence ScalarExecution EffectBuiltinCorrespondence
open RuntimeCallEffectsCorrespondence (Layout Handlers account_related runtime_related)
open RuntimeChildCallEffectsCorrespondence

theorem foldl_value (bytes : List UInt8) (accumulator : Nat) :
    bytes.foldl (fun value byte => value * 256 + byte.toNat) accumulator =
      accumulator * 256 ^ bytes.length + RevertSemantics.bytesValue bytes := by
  induction bytes generalizing accumulator with
  | nil => simp [RevertSemantics.bytesValue]
  | cons byte rest ih =>
      rw [List.foldl_cons, ih, RevertSemantics.bytesValue, List.length_cons, Nat.pow_succ, Nat.add_mul,
        Nat.mul_assoc, Nat.mul_comm 256 (256 ^ rest.length), Nat.add_assoc]

theorem store_components {scope : Scope} {offset value : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "mstore" [offset, value] = .ok lowered) :
    ∃ memory size, Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      lowered = ⟨.unit, Memory.mstore memory size offset value⟩ := by
  change (do
    let raw ← (do
      let memory ← Effects.reference scope "memory" WordMapping.type
      let size ← Effects.reference scope "memorySize" .word
      pure (Lowered.mk .unit (Memory.mstore memory size offset value)) : LowerM Lowered)
    pure raw) = .ok lowered at compiled
  obtain ⟨memory, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨size, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨memory, size, memoryCompiled, sizeCompiled, (Except.ok.inj returned).symm⟩

private theorem revert_components {scope : Scope} {offset length : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "revert" [offset, length] = .ok lowered) :
    ∃ expression, Effects.terminate scope 2 offset length = .ok expression ∧ lowered = ⟨.unit, expression⟩ := by
  have expanded : Effects.lowerBuiltin scope "revert" [offset, length] = (do
      let raw ← (do
        let expression ← Effects.terminate scope 2 offset length
        pure (Lowered.mk .unit expression) : LowerM Lowered)
      pure raw) := rfl
  rw [expanded] at compiled
  obtain ⟨expression, terminated, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨expression, terminated, (Except.ok.inj returned).symm⟩

/-- The accepted revert writes the specified message word and exits through
the revert termination over the message bytes. -/
theorem message_components {scope : Scope} {message : String} {exit : Core.Expr}
    (compiled : Effects.revertMessage scope message = .ok exit) :
    ∃ memory size halt, Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      Effects.terminate scope 2 (.word Word.zero) (.word (RevertSemantics.messageLength message)) = .ok halt ∧
      exit = LocalSequence.discard .unit
        (Memory.mstore memory size (.word Word.zero) (.word (RevertSemantics.messageWord message))) halt := by
  unfold Effects.revertMessage at compiled
  dsimp only at compiled
  split at compiled
  · cases compiled
  · obtain ⟨write, writeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨halted, haltCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨memory, size, memoryCompiled, sizeCompiled, rfl⟩ := store_components writeCompiled
    obtain ⟨halt, terminated, rfl⟩ := revert_components haltCompiled
    refine ⟨memory, size, halt, memoryCompiled, sizeCompiled, terminated, ?_⟩
    rw [← Except.ok.inj returned]
    simp only [RevertSemantics.messageWord, ← Array.foldl_toList, foldl_value, Nat.zero_mul, Nat.zero_add]

theorem weaken_rename (expression : Core.Expr) (mapping : Renaming) :
    (expression.weakenAt 0).rename mapping.lift =
      expression.rename (fun index => [Value.unit].length + mapping index) := by
  rw [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
  congr 1
  funext index
  change mapping index + 1 = [Value.unit].length + mapping index
  simp only [List.length_cons, List.length_nil]
  omega

theorem exit_rename (memory size halt : Core.Expr) (word : Word) (mapping : Renaming) :
    (LocalSequence.discard .unit (Memory.mstore memory size (.word Word.zero) (.word word)) halt).rename mapping =
      LanguageResult.bind .unit (Memory.mstore (memory.rename mapping) (size.rename mapping) (.word Word.zero) (.word word))
        ((halt.weakenAt 0).rename mapping.lift) := by
  rw [LocalSequence.discard, LanguageResult.bind, Core.Expr.rename, MemoryCorrespondence.mstore_rename]
  rfl

theorem world_separate (layout : RuntimeEffectsCorrespondence.Layout) :
    layout.storage.world ≠ layout.memory ∧ layout.storage.world ≠ layout.storage.memorySize ∧
      layout.storage.exit ≠ layout.storage.world ∧ layout.storage.returnOffset ≠ layout.storage.world ∧
      layout.storage.returnSize ≠ layout.storage.world := by
  have distinct := layout.distinct
  simp only [StorageBuiltinCorrespondence.Locations.all, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at distinct
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [ne_comm]

/-- The revert termination writes only the memory size and the exit registers,
so the world cell survives. -/
theorem finalStore_world {layout : RuntimeEffectsCorrespondence.Layout}
    {state : RuntimeEffectsSemantics.State} {kind : Nat} {offset length : Word} {store : Store} {value : Value}
    (found : store.read? layout.storage.world = some value) :
    (TerminationBuiltinCorrespondence.finalStore layout.storage state kind offset length store).read?
      layout.storage.world = some value := by
  obtain ⟨_, notSize, notExit, notOffset, notLength⟩ := world_separate layout
  unfold TerminationBuiltinCorrespondence.finalStore
  split
  · exact found
  · simp only [TerminationBuiltinCorrespondence.finishStore, Store.read?]
    rw [List.getElem?_set_ne notExit, List.getElem?_set_ne notLength, List.getElem?_set_ne notOffset]
    exact (MemoryCorrespondence.touchStore_other store notSize _ _ _).trans found

section
variable {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
variable {layout : Layout} {baseline : Nat → Option Value} {image : Option (List UInt8)}
variable {handlers : Handlers layout} {anchors : Anchors} {context : Context layout} {world : World}
variable {state : Semantics.State RuntimeCallEffectsSemantics.State}

/-- Hull's explicit revert simulates its actual lowering in the frame model:
the exit code fails with the termination reason, and the message write and
exit registers are published. -/
theorem preserves (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (memoryMember : ⟨"memory", WordMapping.type, layout.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    {message : String} {control : Semantics.Control} {final : RuntimeCallEffectsSemantics.State}
    (reverted : RevertSemantics.Reverted message state.external control final)
    {scope : Scope} {exit : Core.Expr} (compiled : Effects.revertMessage scope message = .ok exit)
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (stateRelated : StateRel (model layout baseline slots image handlers anchors context) world state store) :
    ∃ reason finalStore, control = .fault (.language reason) ∧
      Evaluates environment store (exit.rename mapping) (.inLeft .unit (.word reason)) finalStore ∧
      StateRel (model layout baseline slots image handlers anchors context) world {state with external := final}
        finalStore ∧
      ClosuresPreserved store finalStore := by
  cases reverted with
  | reverted fits stored terminated =>
  rename_i memory fault halted
  obtain ⟨memoryReference, sizeReference, halt, memoryCompiled, sizeCompiled, haltCompiled, rfl⟩ :=
    message_components compiled
  have base := base_related stateRelated
  have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related
    (RuntimeLogEffectsCorrespondence.runtime_related (RuntimeAccountEffectsCorrespondence.runtime_related (account_related base)))
  have memoryBefore : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize
      state.external.runtime.runtime.runtime.runtime.runtime.memory store :=
    RuntimeEffectsCorrespondence.memory_related beforeRuntime
  have storageBefore : StorageBuiltinCorrespondence.StateRel layout.storage
      state.external.runtime.runtime.runtime.runtime.runtime.storage store :=
    RuntimeEffectsCorrespondence.storage_related beforeRuntime
  -- the message word at offset zero
  obtain ⟨storedResult, memoryStored, storedFrame⟩ := MemoryCorrespondence.mstore_preserves memoryBefore Word.zero
    (RevertSemantics.messageWord message) environment
  rw [stored] at storedResult memoryStored
  have mstoreEvaluated := MemoryCorrespondence.mstore_evaluates (environment := environment) (initial := store)
    (first := store) (second := store) (third := store) (store := store)
    state.external.runtime.runtime.runtime.runtime.runtime.memory Word.zero (RevertSemantics.messageWord message)
    (reference_evaluates runtime memoryMember memoryCompiled store)
    (reference_evaluates runtime memorySizeMember sizeCompiled store) .word .word
    memoryBefore.memory memoryBefore.size memoryBefore.distinct
  generalize MemoryCorrespondence.mstoreResult state.external.runtime.runtime.runtime.runtime.runtime.memory Word.zero =
    storedValue at storedResult mstoreEvaluated
  generalize MemoryCorrespondence.mstoreStore store layout.memory layout.storage.memorySize
    state.external.runtime.runtime.runtime.runtime.runtime.memory Word.zero (RevertSemantics.messageWord message)
    environment = storedStore at memoryStored storedFrame mstoreEvaluated
  cases storedResult with
  | value related =>
  cases related
  -- the revert exit over the message bytes
  have storageStored := RuntimeEffectsCorrespondence.memory_preserves_storage storageBefore storedFrame
  have haltEvaluated := TerminationBuiltinCorrespondence.terminate_evaluates haltCompiled (runtime.prepend [.unit])
    memorySizeMember exitMember offsetMember sizeMember
    (state := {state.external.runtime.runtime.runtime.runtime.runtime with memory := memory})
    storageStored memoryStored.size Word.zero (RevertSemantics.messageLength message) (fun _ _ => .word) (fun _ _ => .word)
  obtain ⟨haltResult, memoryFinal, storageFinal, haltFrame⟩ := TerminationBuiltinCorrespondence.terminate_state
    (state := {state.external.runtime.runtime.runtime.runtime.runtime with memory := memory})
    memoryStored storageStored 2 Word.zero (RevertSemantics.messageLength message)
  rw [terminated] at haltResult memoryFinal storageFinal
  have storedClosures : ClosuresPreserved store storedStore :=
    MemoryEffectCorrespondence.closures_preserved memoryBefore storedFrame
  have haltClosures : ClosuresPreserved _ _ := TerminationBuiltinCorrespondence.terminate_closures
    (state := {state.external.runtime.runtime.runtime.runtime.runtime with memory := memory})
    memoryStored storageStored 2 Word.zero (RevertSemantics.messageLength message)
  generalize TerminationBuiltinCorrespondence.target
    {state.external.runtime.runtime.runtime.runtime.runtime with memory := memory} Word.zero
    (RevertSemantics.messageLength message) = haltValue at haltResult haltEvaluated
  have worldKept : ∀ value, store.read? layout.storage.world = some value →
      (TerminationBuiltinCorrespondence.finalStore layout.storage
        {state.external.runtime.runtime.runtime.runtime.runtime with memory := memory} 2 Word.zero
        (RevertSemantics.messageLength message) storedStore).read? layout.storage.world = some value := by
    obtain ⟨notMemory, notSize, _⟩ := world_separate layout.toLayout
    intro value found
    exact finalStore_world (layout := layout.toLayout) (storedFrame.read _ value notMemory notSize found)
  generalize TerminationBuiltinCorrespondence.finalStore layout.storage
    {state.external.runtime.runtime.runtime.runtime.runtime with memory := memory} 2 Word.zero
    (RevertSemantics.messageLength message) storedStore = finalStore
    at memoryFinal storageFinal haltFrame haltEvaluated haltClosures worldKept
  cases haltResult with
  | language reason =>
  -- the frame update lifts through the return-data and call layers
  have storedEffects := RuntimeEffectsCorrespondence.Frame.of_memory (layout := layout.toLayout) storedFrame
  have totalFrame : RuntimeEffectsCorrespondence.Frame layout.toLayout store finalStore :=
    ⟨Nat.le_trans storedEffects.length_le haltFrame.length_le, fun location value outside found =>
      haltFrame.read location value outside (storedEffects.read location value outside found)⟩
  have returnDataFinal := RuntimeReturnDataEffectsCorrespondence.runtime_updated passive (runtime_related base)
    memoryFinal storageFinal totalFrame
  have finalRelated := RuntimeCallEffectsCorrespondence.runtime_updated base returnDataFinal rfl
  have linked : RuntimeLinkedWorldCorrespondence.StateRel anchors
      (sourceWorld {state.external with
        runtime := RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime halted})
      layout.storage.world finalStore := by
    have sameWorld : halted.storage.world = state.external.runtime.runtime.runtime.runtime.runtime.storage.world := by
      unfold TerminationSemantics.terminate at terminated
      split at terminated <;> cases terminated <;> rfl
    change RuntimeLinkedWorldCorrespondence.StateRel anchors halted.storage.world layout.storage.world finalStore
    rw [sameWorld]
    exact (linked_related stateRelated).read_preserved worldKept
  refine ⟨reason, finalStore, rfl, ?_,
    of_base finalRelated linked (context.updated base finalRelated stateRelated.external.2.2.1.2),
    ClosuresPreserved.trans storedClosures haltClosures⟩
  rw [exit_rename]
  apply LanguageResult.bind_success .unit mstoreEvaluated
  rw [weaken_rename]
  exact haltEvaluated
end

end Solcore.Frontend.RustHull.RevertBuiltinCorrespondence
