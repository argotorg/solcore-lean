import Solcore.Frontend.RustHull.YulBlockCorrespondence
import Solcore.Frontend.RustHull.RevertBuiltinCorrespondence

/-! The builtins of the connected inline Yul fragment in the frame model. The
actual code of `mload`, `msize`, `mstore`, `mstore8`, `return` and `revert`
over the argument words matches `YulSemantics.Builtin`; catalog links and the
captured context survive. This meets `YulBlockCorrespondence.BuiltinStep`. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.YulBuiltinCorrespondence
open Core Correspondence ScalarExecution EffectBuiltinCorrespondence
open RuntimeCallEffectsCorrespondence (Layout Handlers account_related runtime_related)
open RuntimeChildCallEffectsCorrespondence

theorem mload_components {scope : Scope} {offset : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "mload" [offset] = .ok lowered) :
    ∃ memory size, Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      lowered = ⟨.word, Memory.mload memory size offset⟩ := by
  change (do
    let raw ← (do
      let memory ← Effects.reference scope "memory" WordMapping.type
      let size ← Effects.reference scope "memorySize" .word
      pure (Lowered.mk .word (Memory.mload memory size offset)) : LowerM Lowered)
    pure raw) = .ok lowered at compiled
  obtain ⟨memory, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨size, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨memory, size, memoryCompiled, sizeCompiled, (Except.ok.inj returned).symm⟩

theorem msize_components {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "msize" [] = .ok lowered) :
    ∃ size, Effects.reference scope "memorySize" .word = .ok size ∧
      lowered = ⟨.word, LanguageResult.success (.loadCell size)⟩ := by
  change (do
    let raw ← (do
      let size ← Effects.reference scope "memorySize" .word
      pure (Lowered.mk .word (LanguageResult.success (.loadCell size))) : LowerM Lowered)
    pure raw) = .ok lowered at compiled
  obtain ⟨size, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨size, sizeCompiled, (Except.ok.inj returned).symm⟩

theorem mstore8_components {scope : Scope} {offset value : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "mstore8" [offset, value] = .ok lowered) :
    ∃ memory size, Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      lowered = ⟨.unit, Memory.mstore8 memory size offset value⟩ := by
  change (do
    let raw ← (do
      let memory ← Effects.reference scope "memory" WordMapping.type
      let size ← Effects.reference scope "memorySize" .word
      pure (Lowered.mk .unit (Memory.mstore8 memory size offset value)) : LowerM Lowered)
    pure raw) = .ok lowered at compiled
  obtain ⟨memory, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨size, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨memory, size, memoryCompiled, sizeCompiled, (Except.ok.inj returned).symm⟩

theorem terminate_components {scope : Scope} {name : String} {kind : Nat} {offset length : Core.Expr}
    {lowered : Lowered} (named : name = "return" ∧ kind = 1 ∨ name = "revert" ∧ kind = 2)
    (compiled : Effects.lowerBuiltin scope name [offset, length] = .ok lowered) :
    ∃ expression, Effects.terminate scope kind offset length = .ok expression ∧ lowered = ⟨.unit, expression⟩ := by
  have expanded : Effects.lowerBuiltin scope name [offset, length] = (do
      let raw ← (do
        let expression ← Effects.terminate scope kind offset length
        pure (Lowered.mk .unit expression) : LowerM Lowered)
      pure raw) := by
    rcases named with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  rw [expanded] at compiled
  obtain ⟨expression, terminated, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨expression, terminated, (Except.ok.inj returned).symm⟩

section
variable {slots : List EffectSlot} {store : Store}
variable {layout : Layout} {baseline : Nat → Option Value} {image : Option (List UInt8)}
variable {handlers : Handlers layout} {anchors : Anchors} {context : Context layout} {world : World}
variable {state : Semantics.State RuntimeCallEffectsSemantics.State}

/-- A memory write of the fragment publishes the frame's new memory; the world
cell and source world are unchanged. -/
private theorem memory_related (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (stateRelated : StateRel (model layout baseline slots image handlers anchors context) world state store)
    {memory : MemorySemantics.State} {final : Store}
    (memoryFinal : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize memory final)
    (frame : MemoryCorrespondence.Frame layout.memory layout.storage.memorySize store final) :
    StateRel (model layout baseline slots image handlers anchors context) world
      {state with external := {state.external with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime
        state.external.runtime {state.external.runtime.runtime.runtime.runtime.runtime with memory := memory})}}
      final := by
  have base := base_related stateRelated
  have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related
    (RuntimeLogEffectsCorrespondence.runtime_related (RuntimeAccountEffectsCorrespondence.runtime_related (account_related base)))
  have storageBefore : StorageBuiltinCorrespondence.StateRel layout.storage
      state.external.runtime.runtime.runtime.runtime.runtime.storage store :=
    RuntimeEffectsCorrespondence.storage_related beforeRuntime
  have returnDataFinal := RuntimeReturnDataEffectsCorrespondence.runtime_updated passive (runtime_related base)
    (runtime := {state.external.runtime.runtime.runtime.runtime.runtime with memory := memory}) memoryFinal
    (RuntimeEffectsCorrespondence.memory_preserves_storage storageBefore frame)
    (RuntimeEffectsCorrespondence.Frame.of_memory (layout := layout.toLayout) frame)
  have finalRelated := RuntimeCallEffectsCorrespondence.runtime_updated base returnDataFinal rfl
  obtain ⟨notMemory, notSize, _⟩ := RevertBuiltinCorrespondence.world_separate layout.toLayout
  exact of_base finalRelated
    ((linked_related stateRelated).read_preserved (fun value found => frame.read _ value notMemory notSize found))
    (context.updated base finalRelated stateRelated.external.2.2.1.2)

/-- A termination of the fragment publishes the exit registers and memory
size; the world cell and source world are unchanged. -/
private theorem terminated_related (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (stateRelated : StateRel (model layout baseline slots image handlers anchors context) world state store)
    (kind : Nat) (offset length : Word) :
    StateRel (model layout baseline slots image handlers anchors context) world
      {state with external := {state.external with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime
        state.external.runtime (TerminationSemantics.terminate state.external.runtime.runtime.runtime.runtime.runtime
          kind offset length).2)}}
      (TerminationBuiltinCorrespondence.finalStore layout.storage state.external.runtime.runtime.runtime.runtime.runtime
        kind offset length store) := by
  have base := base_related stateRelated
  have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related
    (RuntimeLogEffectsCorrespondence.runtime_related (RuntimeAccountEffectsCorrespondence.runtime_related (account_related base)))
  have memoryBefore : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize
      state.external.runtime.runtime.runtime.runtime.runtime.memory store :=
    RuntimeEffectsCorrespondence.memory_related beforeRuntime
  have storageBefore : StorageBuiltinCorrespondence.StateRel layout.storage
      state.external.runtime.runtime.runtime.runtime.runtime.storage store :=
    RuntimeEffectsCorrespondence.storage_related beforeRuntime
  obtain ⟨_, memoryFinal, storageFinal, haltFrame⟩ :=
    TerminationBuiltinCorrespondence.terminate_state memoryBefore storageBefore kind offset length
  have returnDataFinal := RuntimeReturnDataEffectsCorrespondence.runtime_updated passive (runtime_related base)
    memoryFinal storageFinal haltFrame
  have finalRelated := RuntimeCallEffectsCorrespondence.runtime_updated base returnDataFinal rfl
  have sameWorld : (TerminationSemantics.terminate state.external.runtime.runtime.runtime.runtime.runtime
      kind offset length).2.storage.world = state.external.runtime.runtime.runtime.runtime.runtime.storage.world := by
    unfold TerminationSemantics.terminate
    split <;> rfl
  have linked : RuntimeLinkedWorldCorrespondence.StateRel anchors
      (sourceWorld {state.external with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime
        (TerminationSemantics.terminate state.external.runtime.runtime.runtime.runtime.runtime kind offset length).2)})
      layout.storage.world
      (TerminationBuiltinCorrespondence.finalStore layout.storage state.external.runtime.runtime.runtime.runtime.runtime
        kind offset length store) := by
    change RuntimeLinkedWorldCorrespondence.StateRel anchors
      (TerminationSemantics.terminate state.external.runtime.runtime.runtime.runtime.runtime kind offset length).2.storage.world
      layout.storage.world _
    rw [sameWorld]
    exact (linked_related stateRelated).read_preserved
      (fun value found => RevertBuiltinCorrespondence.finalStore_world (layout := layout.toLayout) found)
  exact of_base finalRelated linked (context.updated base finalRelated stateRelated.external.2.2.1.2)

/-- The fragment's builtins run their actual code over the argument words in the
frame model. -/
theorem step (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (memoryMember : ⟨"memory", WordMapping.type, layout.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots) :
    YulBlockCorrespondence.BuiltinStep (model layout baseline slots image handlers anchors context) slots := by
  intro name words state result next scope effect mapping environment world store effectNamed computed compiled runtime
    fixed stateRelated
  have base := base_related stateRelated
  have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related
    (RuntimeLogEffectsCorrespondence.runtime_related (RuntimeAccountEffectsCorrespondence.runtime_related (account_related base)))
  have memoryBefore : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize
      (YulSemantics.frame state).memory store :=
    RuntimeEffectsCorrespondence.memory_related beforeRuntime
  have storageBefore : StorageBuiltinCorrespondence.StateRel layout.storage (YulSemantics.frame state).storage store :=
    RuntimeEffectsCorrespondence.storage_related beforeRuntime
  have read : ∀ (index : Nat) (word : Word), index < words.length →
      (words.map Value.word ++ environment)[index]? = some (.word word) →
      Evaluates (words.map Value.word ++ environment) store ((Core.Expr.var index).rename mapping) (.word word) store := by
    intro index word below found
    apply Evaluates.var
    show (words.map Value.word ++ environment)[mapping index]? = some (.word word)
    rw [fixed index below]
    exact found
  have stable : ∀ (index : Nat) (word : Word), index < words.length →
      (words.map Value.word ++ environment)[index]? = some (.word word) →
      TerminationBuiltinCorrespondence.StableWord (words.map Value.word ++ environment) mapping (.var index) word := by
    intro index word below found extra other
    apply Evaluates.var
    show (extra ++ (words.map Value.word ++ environment))[extra.length + mapping index]? = some (.word word)
    rw [fixed index below, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact found
  cases computed with
  | @mload _ offset =>
      obtain ⟨memoryReference, sizeReference, memoryCompiled, sizeCompiled, rfl⟩ := mload_components compiled
      obtain ⟨loadedResult, memoryLoaded, loadedFrame⟩ := MemoryCorrespondence.mload_preserves memoryBefore offset
        (Value.word offset :: environment)
      have loaded : Evaluates (Value.word offset :: environment) store
          ((Memory.mload memoryReference sizeReference (.var 0)).rename mapping)
          (MemoryCorrespondence.mloadResult (YulSemantics.frame state).memory offset)
          (MemoryCorrespondence.mloadStore store layout.memory layout.storage.memorySize
            (YulSemantics.frame state).memory offset (Value.word offset :: environment)) := by
        rw [MemoryCorrespondence.mload_rename]
        exact MemoryCorrespondence.mload_evaluates _ offset
          (reference_evaluates runtime memoryMember memoryCompiled store)
          (reference_evaluates runtime memorySizeMember sizeCompiled store) (read 0 offset (by simp) rfl)
          memoryBefore.memory memoryBefore.size memoryBefore.distinct
      exact ⟨_, _, loadedResult, loaded, memory_related passive stateRelated memoryLoaded loadedFrame,
        MemoryEffectCorrespondence.closures_preserved memoryBefore loadedFrame⟩
  | msize =>
      obtain ⟨sizeReference, sizeCompiled, rfl⟩ := msize_components compiled
      exact ⟨_, store, .value (.word _), LanguageResult.success_evaluates
        (.loadCell (reference_evaluates runtime memorySizeMember sizeCompiled store) memoryBefore.size), stateRelated,
        ClosuresPreserved.refl store⟩
  | @mstore _ offset value =>
      obtain ⟨memoryReference, sizeReference, memoryCompiled, sizeCompiled, rfl⟩ :=
        RevertBuiltinCorrespondence.store_components compiled
      obtain ⟨storedResult, memoryStored, storedFrame⟩ := MemoryCorrespondence.mstore_preserves memoryBefore
        offset value (Value.word offset :: Value.word value :: environment)
      have stored : Evaluates (Value.word offset :: Value.word value :: environment) store
          ((Memory.mstore memoryReference sizeReference (.var 0) (.var 1)).rename mapping)
          (MemoryCorrespondence.mstoreResult (YulSemantics.frame state).memory offset)
          (MemoryCorrespondence.mstoreStore store layout.memory layout.storage.memorySize
            (YulSemantics.frame state).memory offset value (Value.word offset :: Value.word value :: environment)) := by
        rw [MemoryCorrespondence.mstore_rename]
        exact MemoryCorrespondence.mstore_evaluates _ offset value
          (reference_evaluates runtime memoryMember memoryCompiled store)
          (reference_evaluates runtime memorySizeMember sizeCompiled store) (read 0 offset (by simp) rfl)
          (read 1 value (by simp) rfl) memoryBefore.memory memoryBefore.size memoryBefore.distinct
      exact ⟨_, _, storedResult, stored, memory_related passive stateRelated memoryStored storedFrame,
        MemoryEffectCorrespondence.closures_preserved memoryBefore storedFrame⟩
  | @mstore8 _ offset value =>
      obtain ⟨memoryReference, sizeReference, memoryCompiled, sizeCompiled, rfl⟩ := mstore8_components compiled
      obtain ⟨storedResult, memoryStored, storedFrame⟩ := MemoryCorrespondence.mstore8_preserves memoryBefore
        offset value (Value.word offset :: Value.word value :: environment)
      have stored : Evaluates (Value.word offset :: Value.word value :: environment) store
          ((Memory.mstore8 memoryReference sizeReference (.var 0) (.var 1)).rename mapping)
          (MemoryCorrespondence.mstore8Result (YulSemantics.frame state).memory offset)
          (MemoryCorrespondence.mstore8Store store layout.memory layout.storage.memorySize
            (YulSemantics.frame state).memory offset value (Value.word offset :: Value.word value :: environment)) := by
        rw [MemoryCorrespondence.mstore8_rename]
        exact MemoryCorrespondence.mstore8_evaluates _ offset value
          (reference_evaluates runtime memoryMember memoryCompiled store)
          (reference_evaluates runtime memorySizeMember sizeCompiled store) (read 0 offset (by simp) rfl)
          (read 1 value (by simp) rfl) memoryBefore.memory memoryBefore.size memoryBefore.distinct
      exact ⟨_, _, storedResult, stored, memory_related passive stateRelated memoryStored storedFrame,
        MemoryEffectCorrespondence.closures_preserved memoryBefore storedFrame⟩
  | @returned _ offset length =>
      obtain ⟨halt, haltCompiled, rfl⟩ := terminate_components (.inl ⟨rfl, rfl⟩) compiled
      have haltEvaluated := TerminationBuiltinCorrespondence.terminate_evaluates haltCompiled runtime
        memorySizeMember exitMember offsetMember sizeMember storageBefore memoryBefore.size offset length
        (stable 0 offset (by simp) rfl) (stable 1 length (by simp) rfl)
      obtain ⟨haltResult, _, _, _⟩ :=
        TerminationBuiltinCorrespondence.terminate_state memoryBefore storageBefore 1 offset length
      exact ⟨_, _, haltResult, haltEvaluated, terminated_related passive stateRelated 1 offset length,
        TerminationBuiltinCorrespondence.terminate_closures memoryBefore storageBefore 1 offset length⟩
  | @reverted _ offset length =>
      obtain ⟨halt, haltCompiled, rfl⟩ := terminate_components (.inr ⟨rfl, rfl⟩) compiled
      have haltEvaluated := TerminationBuiltinCorrespondence.terminate_evaluates haltCompiled runtime
        memorySizeMember exitMember offsetMember sizeMember storageBefore memoryBefore.size offset length
        (stable 0 offset (by simp) rfl) (stable 1 length (by simp) rfl)
      obtain ⟨haltResult, _, _, _⟩ :=
        TerminationBuiltinCorrespondence.terminate_state memoryBefore storageBefore 2 offset length
      exact ⟨_, _, haltResult, haltEvaluated, terminated_related passive stateRelated 2 offset length,
        TerminationBuiltinCorrespondence.terminate_closures memoryBefore storageBefore 2 offset length⟩
  | add => exact absurd effectNamed (by decide)
  | sub => exact absurd effectNamed (by decide)
  | lt => exact absurd effectNamed (by decide)
  | gt => exact absurd effectNamed (by decide)
  | eq => exact absurd effectNamed (by decide)
  | iszero => exact absurd effectNamed (by decide)

end

end Solcore.Frontend.RustHull.YulBuiltinCorrespondence
