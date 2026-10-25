import Solcore.Frontend.RustHull.RuntimeEffectsCorrespondence
import Solcore.Frontend.RustHull.MemoryFrameCorrespondence

/-! Interleaved memory and storage effects reach actual frame compilation,
installed closure calls and snapshots of the final independent source state. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeEffectsFrameCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence RuntimeEffectsCorrespondence

abbrev slotTypes := MemoryFrameCorrespondence.slotTypes

/-- Passive observations are supplied by concrete initialization. They exclude
all locations that either component may change. -/
def PassiveCell (layout : Layout) (slots : List EffectSlot) (store : Core.Store)
    (name : String) (value : Core.Value) : Prop :=
  ∃ slot ∈ slots, slot.name = name ∧ slot.location ∉ mutable layout ∧
    slot.location < layout.boundary ∧ store.read? slot.location = some value

def passiveSnapshotNames : List String := ["logs", "logSize", "balances"]

theorem cell_observed {slots : List EffectSlot} {store : Core.Store}
    {cells : AccountRuntime.References} {environment : Core.Environment}
    (references : AccountRuntime.frameReferences (slotTypes slots) = .ok cells)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id environment)
    {name : String} {type : Core.Ty} {location : Nat} {value : Core.Value}
    (member : ⟨name, type, location⟩ ∈ slots) (found : store.read? location = some value) :
    FrameCellObserved cells environment store name value := by
  apply FrameCellObserved.of_compilation references
    (List.mem_map.mpr ⟨⟨name, type, location⟩, member, rfl⟩)
  · exact runtime _ member
  · exact found

theorem passive_observed {layout : Layout} {slots : List EffectSlot} {initial final : Core.Store}
    {world : World} {source : Semantics.State RuntimeEffectsSemantics.State}
    {cells : AccountRuntime.References} {environment : Core.Environment}
    (references : AccountRuntime.frameReferences (slotTypes slots) = .ok cells)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id environment)
    (related : StateRel (model layout (prefixRead layout.boundary initial)) world source final)
    {name : String} {value : Core.Value} (observed : PassiveCell layout slots initial name value) :
    FrameCellObserved cells environment final name value := by
  obtain ⟨slot, member, named, outside, below, stored⟩ := observed
  apply FrameCellObserved.of_compilation (type := slot.type) references
    (List.mem_map.mpr ⟨slot, member, by simp only [named]⟩)
  · intro binding index looked
    exact runtime slot member binding index (by simpa only [named] using looked)
  · have retained := related.external.2.2.other slot.location outside
    simpa only [prefixRead, below, ↓reduceIte, stored] using retained

def snapshotValues (values : String → Core.Value) (state : RuntimeEffectsSemantics.State)
    (accounts : StorageCorrespondence.Accounts) (name : String) : Core.Value :=
  match name with
  | "memory" => Core.WordMapping.encode state.memory.words
  | "world" => StorageCorrespondence.world accounts
  | "exit" => .word state.storage.exit
  | "returnOffset" => .word state.storage.returnOffset
  | "returnSize" => .word state.storage.returnSize
  | _ => values name

/-- A frame installed earlier retains its captured environment. The body and
completion wrapper observe the final source world, including storage writes
and static-write termination, through the compiler's actual frame references. -/
theorem compileFrame_call_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {memoryLocation : Nat} {locations : StorageBuiltinCorrespondence.Locations}
    {initial : RuntimeEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument : Core.Expr} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, memoryLocation⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, locations.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, locations.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ slots)
    (memoryInitial : MemoryCorrespondence.StateRel memoryLocation locations.memorySize initial.memory store)
    (storageInitial : StorageBuiltinCorrespondence.StateRel locations initial.storage store)
    (distinct : (memoryLocation :: locations.all).Nodup)
    {final : Semantics.State RuntimeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell (initialLayout memoryInitial storageInitial distinct) slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues snapshot final.external accounts)
          (StorageCorrespondence.get accounts final.external.storage.address final.external.storage.complete)) finalStore ∧
      StateRel (model (initialLayout memoryInitial storageInitial distinct) (prefixRead store.length store))
        extension final finalStore := by
  obtain ⟨own, body, cells, assembled, references, rfl⟩ := compileFrame_components accepted
  have selected := MemoryFrameCorrespondence.frame_selected accepted
  obtain ⟨signatures, codes, selectedFunction, selectedCode, index, _, sourceSelected,
    signatureCompiled, _, _, _, _, _⟩ := assemble_selection assembled
  have sameFunction := Option.some.inj (sourceSelected.symm.trans selected)
  subst selectedFunction
  obtain ⟨parameters, resultType⟩ := MemoryFrameCorrespondence.frame_signature signatureCompiled
  have argumentValues : ValuesRel own.parameters [] [] := by rw [parameters]; exact .nil
  obtain ⟨extension, status, bodyStore, related, executed, state, _⟩ :=
    assemble_program (initialLayout memoryInitial storageInitial distinct) (prefixRead store.length store) slots
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      assembled selected eligible argumentValues evaluated
      (runtimeValues := values.reverse) (caller := bundleValues values :: captured)
      (by simpa [AccountRuntime.frameScope, slotTypes, MemoryFrameCorrespondence.slotTypes] using length)
      (MemoryFrameCorrespondence.frame_coverage _) runtime separated
      (initial_state memoryInitial storageInitial distinct)
  have finalStorage := storage_related state
  obtain ⟨accounts, sourceWorld, worldRead⟩ := finalStorage.world
  have finalWorld := cell_observed references runtime worldMember worldRead
  have finalAddress := cell_observed references runtime addressMember finalStorage.address
  have finalComplete := cell_observed references runtime completeMember finalStorage.complete
  have finalSnapshot : ∀ name ∈ frameSnapshotNames,
      FrameCellObserved cells (values.reverse ++ .unit :: bundleValues values :: captured)
        bodyStore name (snapshotValues snapshot final.external accounts name) := by
    intro name member
    simp [frameSnapshotNames] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cell_observed references runtime exitMember finalStorage.exit
    · exact cell_observed references runtime offsetMember finalStorage.returnOffset
    · exact cell_observed references runtime sizeMember finalStorage.returnSize
    · exact cell_observed references runtime memoryMember (memory_related state).memory
    · exact passive_observed references runtime state (snapshotObserved "logs" (by simp [passiveSnapshotNames]))
    · exact passive_observed references runtime state (snapshotObserved "logSize" (by simp [passiveSnapshotNames]))
    · exact passive_observed references runtime state (snapshotObserved "balances" (by simp [passiveSnapshotNames]))
    · exact finalWorld
  have completed := frameCompletion_evaluates executed accounts final.external.storage.address final.external.storage.complete
    finalWorld finalAddress finalComplete finalSnapshot
  obtain ⟨suffix, _, extended⟩ := StorageCorrespondence.getStore_extension accounts
    final.external.storage.address final.external.storage.complete
    (status :: (values.reverse ++ .unit :: bundleValues values :: captured)) bodyStore
  refine ⟨extension, status, accounts, _, sourceWorld, by simpa only [resultType] using related,
    frameUnpack_call_evaluates (by simpa only [slotTypes, MemoryFrameCorrespondence.slotTypes, List.length_map] using length)
      closureRelated resolved supplied completed, ?_⟩
  rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
  simpa only [List.nil_append] using state.appendCore suffix

/-- Direct evaluation of freshly compiled frame code is a special case of the
same theorem for captured calls. -/
theorem compileFrame_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {memoryLocation : Nat} {locations : StorageBuiltinCorrespondence.Locations}
    {initial : RuntimeEffectsSemantics.State}
    {initialStore store : Core.Store} {values environment : Core.Environment} {argument : Core.Expr}
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: environment))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, memoryLocation⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, locations.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, locations.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ slots)
    (memoryInitial : MemoryCorrespondence.StateRel memoryLocation locations.memorySize initial.memory store)
    (storageInitial : StorageBuiltinCorrespondence.StateRel locations initial.storage store)
    (distinct : (memoryLocation :: locations.all).Nodup)
    {final : Semantics.State RuntimeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell (initialLayout memoryInitial storageInitial distinct) slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment initialStore (.apply compiled argument)
        (frameCompletionValue status (snapshotValues snapshot final.external accounts)
          (StorageCorrespondence.get accounts final.external.storage.address final.external.storage.complete)) finalStore ∧
      StateRel (model (initialLayout memoryInitial storageInitial distinct) (prefixRead store.length store))
        extension final finalStore := by
  obtain ⟨own, body, cells, _, _, rfl⟩ := compileFrame_components accepted
  exact compileFrame_call_preserves accepted eligible (CapturedClosure.lambda _ _ _ environment)
    Core.Evaluates.lambda supplied length runtime separated memoryMember worldMember addressMember completeMember
    staticMember memorySizeMember exitMember offsetMember sizeMember memoryInitial storageInitial distinct
    evaluated snapshot snapshotObserved

end Solcore.Frontend.RustHull.RuntimeEffectsFrameCorrespondence
