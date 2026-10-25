import Solcore.Frontend.RustHull.RuntimeEnvironmentEffectsCorrespondence
import Solcore.Frontend.RustHull.RuntimeEffectsFrameCorrespondence
import Solcore.Frontend.RustHull.MemoryFrameCorrespondence

/-! Interleaved memory, storage and environment observations reach actual frame compilation,
installed closure calls and snapshots of the final independent source state. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeEnvironmentEffectsFrameCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence RuntimeEnvironmentEffectsCorrespondence

abbrev slotTypes := MemoryFrameCorrespondence.slotTypes
abbrev PassiveCell := RuntimeEffectsFrameCorrespondence.PassiveCell
abbrev passiveSnapshotNames := RuntimeEffectsFrameCorrespondence.passiveSnapshotNames
abbrev cell_observed := @RuntimeEffectsFrameCorrespondence.cell_observed
abbrev snapshotValues := RuntimeEffectsFrameCorrespondence.snapshotValues
abbrev initialLayout := @RuntimeEffectsCorrespondence.initialLayout

theorem passive_observed {layout : Layout} {slots : List EffectSlot} {initial final : Core.Store}
    {world : World} {source : Semantics.State RuntimeEnvironmentEffectsSemantics.State}
    {cells : AccountRuntime.References} {environment : Core.Environment}
    (references : AccountRuntime.frameReferences (slotTypes slots) = .ok cells)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id environment)
    (related : StateRel (model layout (prefixRead layout.boundary initial) slots) world source final)
    {name : String} {value : Core.Value} (observed : PassiveCell layout slots initial name value) :
    FrameCellObserved cells environment final name value :=
  RuntimeEffectsFrameCorrespondence.passive_observed references runtime (runtime_related related) observed

/-- A frame installed earlier retains its captured environment. The body and
completion wrapper observe the final source world, including storage writes
and static-write termination, through the compiler's actual frame references. -/
theorem compileFrame_call_preserves_observed {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {memoryLocation : Nat} {locations : StorageBuiltinCorrespondence.Locations}
    {initial : RuntimeEnvironmentEffectsSemantics.State}
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
    (memoryInitial : MemoryCorrespondence.StateRel memoryLocation locations.memorySize initial.runtime.memory store)
    (storageInitial : StorageBuiltinCorrespondence.StateRel locations initial.runtime.storage store)
    (distinct : (memoryLocation :: locations.all).Nodup)
    (observationsInitial : EnvironmentBuiltinCorrespondence.StateRel slots initial.environment store)
    (passive : Passive (initialLayout memoryInitial storageInitial distinct) slots)
    {final : Semantics.State RuntimeEnvironmentEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEnvironmentEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell (initialLayout memoryInitial storageInitial distinct) slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues snapshot final.external.runtime accounts)
          (StorageCorrespondence.get accounts final.external.runtime.storage.address final.external.runtime.storage.complete)) finalStore ∧
      StateRel (model (initialLayout memoryInitial storageInitial distinct) (prefixRead store.length store) slots)
        extension final finalStore ∧
      finalStore.read? locations.world = some (StorageCorrespondence.world accounts) := by
  obtain ⟨own, body, cells, assembled, references, rfl⟩ := compileFrame_components accepted
  have selected := MemoryFrameCorrespondence.frame_selected accepted
  obtain ⟨signatures, codes, selectedFunction, selectedCode, index, _, sourceSelected,
    signatureCompiled, _, _, _, _, _⟩ := assemble_selection assembled
  have sameFunction := Option.some.inj (sourceSelected.symm.trans selected)
  subst selectedFunction
  obtain ⟨parameters, resultType⟩ := MemoryFrameCorrespondence.frame_signature signatureCompiled
  have argumentValues : ValuesRel own.parameters [] [] := by rw [parameters]; exact .nil
  obtain ⟨extension, status, bodyStore, related, executed, state, _⟩ :=
    assemble_program (initialLayout memoryInitial storageInitial distinct) (prefixRead store.length store) slots passive
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      assembled selected eligible argumentValues evaluated
      (runtimeValues := values.reverse) (caller := bundleValues values :: captured)
      (by simpa [AccountRuntime.frameScope, slotTypes, MemoryFrameCorrespondence.slotTypes] using length)
      (MemoryFrameCorrespondence.frame_coverage _) runtime separated
      (initial_state memoryInitial storageInitial distinct observationsInitial)
  have finalStorage := RuntimeEffectsCorrespondence.storage_related (runtime_related state)
  obtain ⟨accounts, sourceWorld, worldRead⟩ := finalStorage.world
  have finalWorld := cell_observed references runtime worldMember worldRead
  have finalAddress := cell_observed references runtime addressMember finalStorage.address
  have finalComplete := cell_observed references runtime completeMember finalStorage.complete
  have finalSnapshot : ∀ name ∈ frameSnapshotNames,
      FrameCellObserved cells (values.reverse ++ .unit :: bundleValues values :: captured)
        bodyStore name (snapshotValues snapshot final.external.runtime accounts name) := by
    intro name member
    simp [frameSnapshotNames] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cell_observed references runtime exitMember finalStorage.exit
    · exact cell_observed references runtime offsetMember finalStorage.returnOffset
    · exact cell_observed references runtime sizeMember finalStorage.returnSize
    · exact cell_observed references runtime memoryMember (RuntimeEffectsCorrespondence.memory_related (runtime_related state)).memory
    · exact passive_observed references runtime state (snapshotObserved "logs" (by decide))
    · exact passive_observed references runtime state (snapshotObserved "logSize" (by decide))
    · exact passive_observed references runtime state (snapshotObserved "balances" (by decide))
    · exact finalWorld
  have completed := frameCompletion_evaluates executed accounts final.external.runtime.storage.address final.external.runtime.storage.complete
    finalWorld finalAddress finalComplete finalSnapshot
  obtain ⟨suffix, _, extended⟩ := StorageCorrespondence.getStore_extension accounts
    final.external.runtime.storage.address final.external.runtime.storage.complete
    (status :: (values.reverse ++ .unit :: bundleValues values :: captured)) bodyStore
  refine ⟨extension, status, accounts, _, sourceWorld, by simpa only [resultType] using related,
    frameUnpack_call_evaluates (by simpa only [slotTypes, MemoryFrameCorrespondence.slotTypes, List.length_map] using length)
      closureRelated resolved supplied completed, ?_, ?_⟩
  · rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
    simpa only [List.nil_append] using state.appendCore suffix
  · rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
    exact ((StoreRetains.append bodyStore suffix).read locations.world
      (List.getElem?_eq_some_iff.mp worldRead).1).trans worldRead

theorem compileFrame_call_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {memoryLocation : Nat} {locations : StorageBuiltinCorrespondence.Locations}
    {initial : RuntimeEnvironmentEffectsSemantics.State}
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
    (memoryInitial : MemoryCorrespondence.StateRel memoryLocation locations.memorySize initial.runtime.memory store)
    (storageInitial : StorageBuiltinCorrespondence.StateRel locations initial.runtime.storage store)
    (distinct : (memoryLocation :: locations.all).Nodup)
    (observationsInitial : EnvironmentBuiltinCorrespondence.StateRel slots initial.environment store)
    (passive : Passive (initialLayout memoryInitial storageInitial distinct) slots)
    {final : Semantics.State RuntimeEnvironmentEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEnvironmentEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell (initialLayout memoryInitial storageInitial distinct) slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues snapshot final.external.runtime accounts)
          (StorageCorrespondence.get accounts final.external.runtime.storage.address final.external.runtime.storage.complete)) finalStore ∧
      StateRel (model (initialLayout memoryInitial storageInitial distinct) (prefixRead store.length store) slots)
        extension final finalStore := by
  obtain ⟨extension, status, accounts, finalStore, represented, related, executed, state, _⟩ :=
    compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length runtime separated
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      memoryInitial storageInitial distinct observationsInitial passive evaluated snapshot snapshotObserved
  exact ⟨extension, status, accounts, finalStore, represented, related, executed, state⟩

/-- Direct evaluation of freshly compiled frame code is a special case of the
same theorem for captured calls. -/
theorem compileFrame_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {memoryLocation : Nat} {locations : StorageBuiltinCorrespondence.Locations}
    {initial : RuntimeEnvironmentEffectsSemantics.State}
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
    (memoryInitial : MemoryCorrespondence.StateRel memoryLocation locations.memorySize initial.runtime.memory store)
    (storageInitial : StorageBuiltinCorrespondence.StateRel locations initial.runtime.storage store)
    (distinct : (memoryLocation :: locations.all).Nodup)
    (observationsInitial : EnvironmentBuiltinCorrespondence.StateRel slots initial.environment store)
    (passive : Passive (initialLayout memoryInitial storageInitial distinct) slots)
    {final : Semantics.State RuntimeEnvironmentEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEnvironmentEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell (initialLayout memoryInitial storageInitial distinct) slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment initialStore (.apply compiled argument)
        (frameCompletionValue status (snapshotValues snapshot final.external.runtime accounts)
          (StorageCorrespondence.get accounts final.external.runtime.storage.address final.external.runtime.storage.complete)) finalStore ∧
      StateRel (model (initialLayout memoryInitial storageInitial distinct) (prefixRead store.length store) slots)
        extension final finalStore := by
  obtain ⟨own, body, cells, _, _, rfl⟩ := compileFrame_components accepted
  exact compileFrame_call_preserves accepted eligible (CapturedClosure.lambda _ _ _ environment)
    Core.Evaluates.lambda supplied length runtime separated memoryMember worldMember addressMember completeMember
    staticMember memorySizeMember exitMember offsetMember sizeMember memoryInitial storageInitial distinct observationsInitial passive
    evaluated snapshot snapshotObserved

end Solcore.Frontend.RustHull.RuntimeEnvironmentEffectsFrameCorrespondence
