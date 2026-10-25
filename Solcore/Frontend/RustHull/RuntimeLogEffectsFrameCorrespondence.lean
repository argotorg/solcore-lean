import Solcore.Frontend.RustHull.RuntimeLogEffectsCorrespondence
import Solcore.Frontend.RustHull.RuntimeEffectsFrameCorrespondence
import Solcore.Frontend.RustHull.MemoryFrameCorrespondence

/-! Interleaved memory, storage, environment and event operations reach actual frame compilation,
installed closure calls and snapshots of the final independent source state. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeLogEffectsFrameCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence RuntimeLogEffectsCorrespondence

abbrev slotTypes := MemoryFrameCorrespondence.slotTypes
abbrev cell_observed := @RuntimeEffectsFrameCorrespondence.cell_observed

def PassiveCell (layout : Layout) (slots : List EffectSlot) (store : Core.Store)
    (name : String) (value : Core.Value) : Prop :=
  ∃ slot ∈ slots, slot.name = name ∧ slot.location ∉ mutable layout ∧
    slot.location < layout.boundary ∧ store.read? slot.location = some value

def passiveSnapshotNames : List String := ["balances"]

def snapshotValues (values : String → Core.Value) (state : RuntimeLogEffectsSemantics.State)
    (accounts : StorageCorrespondence.Accounts) (name : String) : Core.Value :=
  match name with
  | "memory" => Core.WordMapping.encode state.runtime.runtime.memory.words
  | "world" => StorageCorrespondence.world accounts
  | "exit" => .word state.runtime.runtime.storage.exit
  | "returnOffset" => .word state.runtime.runtime.storage.returnOffset
  | "returnSize" => .word state.runtime.runtime.storage.returnSize
  | "logs" => Core.WordMapping.encode state.words
  | "logSize" => .word state.cursor
  | _ => values name

theorem passive_observed {layout : Layout} {slots : List EffectSlot} {initial final : Core.Store}
    {world : World} {source : Semantics.State RuntimeLogEffectsSemantics.State}
    {cells : AccountRuntime.References} {environment : Core.Environment}
    (references : AccountRuntime.frameReferences (slotTypes slots) = .ok cells)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id environment)
    (related : StateRel (model layout (prefixRead layout.boundary initial) slots) world source final)
    {name : String} {value : Core.Value} (observed : PassiveCell layout slots initial name value) :
    FrameCellObserved cells environment final name value :=
by
  obtain ⟨slot, member, named, outside, below, stored⟩ := observed
  apply FrameCellObserved.of_compilation (type := slot.type) references
    (List.mem_map.mpr ⟨slot, member, by simp only [named]⟩)
  · intro binding index looked
    exact runtime slot member binding index (by simpa only [named] using looked)
  · have retained := other_related related outside
    simpa only [prefixRead, below, ↓reduceIte, stored] using retained

/-- A frame installed earlier retains its captured environment. The body and
completion wrapper observe the final source world, including storage writes
and static-write termination, through the compiler's actual frame references. -/
theorem compileFrame_call_preserves_observed {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout}
    {initial : RuntimeLogEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument : Core.Expr} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : Passive layout slots)
    {final : Semantics.State RuntimeLogEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeLogEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell layout slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues snapshot final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots)
        extension final finalStore ∧
      finalStore.read? layout.storage.world = some (StorageCorrespondence.world accounts) := by
  obtain ⟨own, body, cells, assembled, references, rfl⟩ := compileFrame_components accepted
  have selected := MemoryFrameCorrespondence.frame_selected accepted
  obtain ⟨signatures, codes, selectedFunction, selectedCode, index, _, sourceSelected,
    signatureCompiled, _, _, _, _, _⟩ := assemble_selection assembled
  have sameFunction := Option.some.inj (sourceSelected.symm.trans selected)
  subst selectedFunction
  obtain ⟨parameters, resultType⟩ := MemoryFrameCorrespondence.frame_signature signatureCompiled
  have argumentValues : ValuesRel own.parameters [] [] := by rw [parameters]; exact .nil
  obtain ⟨extension, status, bodyStore, related, executed, state, _⟩ :=
    assemble_program layout (prefixRead layout.boundary store) slots passive
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember assembled selected eligible argumentValues evaluated
      (runtimeValues := values.reverse) (caller := bundleValues values :: captured)
      (by simpa [AccountRuntime.frameScope, slotTypes, MemoryFrameCorrespondence.slotTypes] using length)
      (MemoryFrameCorrespondence.frame_coverage _) runtime separated
      initialRelated
  have finalStorage := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related (runtime_related state))
  have finalLogs := logs_related state
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
    · exact cell_observed references runtime memoryMember finalLogs.logs.memory
    · exact cell_observed references runtime logsMember finalLogs.logs.logs
    · exact cell_observed references runtime logSizeMember finalLogs.logs.logSize
    · exact passive_observed references runtime state (snapshotObserved "balances" (by decide))
    · exact finalWorld
  have completed := frameCompletion_evaluates executed accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete
    finalWorld finalAddress finalComplete finalSnapshot
  obtain ⟨suffix, _, extended⟩ := StorageCorrespondence.getStore_extension accounts
    final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete
    (status :: (values.reverse ++ .unit :: bundleValues values :: captured)) bodyStore
  refine ⟨extension, status, accounts, _, sourceWorld, by simpa only [resultType] using related,
    frameUnpack_call_evaluates (by simpa only [slotTypes, MemoryFrameCorrespondence.slotTypes, List.length_map] using length)
      closureRelated resolved supplied completed, ?_, ?_⟩
  · rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
    simpa only [List.nil_append] using state.appendCore suffix
  · rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
    exact ((StoreRetains.append bodyStore suffix).read layout.storage.world
      (List.getElem?_eq_some_iff.mp worldRead).1).trans worldRead

theorem compileFrame_call_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout}
    {initial : RuntimeLogEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument : Core.Expr} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : Passive layout slots)
    {final : Semantics.State RuntimeLogEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeLogEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell layout slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues snapshot final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots)
        extension final finalStore := by
  obtain ⟨extension, status, accounts, finalStore, represented, related, executed, state, _⟩ :=
    compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length runtime separated
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember initialRelated passive evaluated snapshot snapshotObserved
  exact ⟨extension, status, accounts, finalStore, represented, related, executed, state⟩

/-- Direct evaluation of freshly compiled frame code is a special case of the
same theorem for captured calls. -/
theorem compileFrame_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout}
    {initial : RuntimeLogEffectsSemantics.State}
    {initialStore store : Core.Store} {values environment : Core.Environment} {argument : Core.Expr}
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: environment))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : Passive layout slots)
    {final : Semantics.State RuntimeLogEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeLogEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell layout slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment initialStore (.apply compiled argument)
        (frameCompletionValue status (snapshotValues snapshot final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots)
        extension final finalStore := by
  obtain ⟨own, body, cells, _, _, rfl⟩ := compileFrame_components accepted
  exact compileFrame_call_preserves accepted eligible (CapturedClosure.lambda _ _ _ environment)
    Core.Evaluates.lambda supplied length runtime separated memoryMember worldMember addressMember completeMember
    staticMember memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember initialRelated passive
    evaluated snapshot snapshotObserved

end Solcore.Frontend.RustHull.RuntimeLogEffectsFrameCorrespondence
