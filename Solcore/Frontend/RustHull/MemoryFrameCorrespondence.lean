import Solcore.Frontend.RustHull.MemoryEffectCorrespondence
import Solcore.Frontend.RustHull.RuntimeClosureCorrespondence

/-! Independent memory-bearing Hull executions pass through the actual object
frame compiler, including its runtime-reference unpacking and final snapshot. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.MemoryFrameCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence MemoryEffectCorrespondence

def slotTypes (slots : List EffectSlot) : List (String × Core.Ty) :=
  slots.map fun slot => (slot.name, slot.type)

theorem frame_selected {program : Program} {code : CodeBlock} {slots : List (String × Core.Ty)}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code slots fuel = .ok compiled) :
    (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]).find?
      (·.name == AccountRuntime.frameEntry) = some (AccountRuntime.frameFunction code) := by
  unfold AccountRuntime.compileFrame at accepted
  split at accepted
  · simp [fail, Bind.bind, Except.bind] at accepted
  · rename_i notReserved
    have absent : (program.functions ++ code.functions).find? (·.name == AccountRuntime.frameEntry) = none := by
      apply List.find?_eq_none.mpr
      intro function member
      intro named
      exact notReserved (List.any_eq_true.mpr ⟨function, member, named⟩)
    simp only [List.find?_append, absent, Option.none_or, List.find?_cons,
      AccountRuntime.frameFunction, beq_self_eq_true]

theorem frame_signature {code : CodeBlock} {fuel : Nat} {own : Signature}
    (compiled : signature fuel (AccountRuntime.frameFunction code) = .ok own) :
    own.parameters = [] ∧ own.result = .unit := by
  obtain ⟨arity, result⟩ := StatementCorrespondence.signature_components compiled
  have parameters : own.parameters = [] := List.eq_nil_of_length_eq_zero arity.symm
  refine ⟨parameters, ?_⟩
  cases fuel with
  | zero => cases result
  | succ fuel => exact (Except.ok.inj result).symm

theorem frame_coverage (slots : List (String × Core.Ty)) :
    ScopeCoverage [] (AccountRuntime.frameScope slots) := by
  apply ScopeCoverage.of_reserved
  intro binding member name named
  obtain ⟨⟨slot, type⟩, _, rfl⟩ := List.mem_map.mp member
  cases Option.some.inj named
  exact slotName_reserved slot

/-- An unchanged runtime cell is observed at its real pre-body store location.
The initializer supplies these finite facts directly from allocation. -/
def PassiveCell (layout : Layout) (slots : List EffectSlot) (store : Core.Store)
    (name : String) (value : Core.Value) : Prop :=
  ∃ slot ∈ slots, slot.name = name ∧ slot.location ≠ layout.memory ∧
    slot.location ≠ layout.size ∧ slot.location < layout.boundary ∧
    store.read? slot.location = some value

theorem passive_observed {layout : Layout} {slots : List EffectSlot} {initial final : Core.Store}
    {world : World} {source : Semantics.State MemorySemantics.State}
    {cells : AccountRuntime.References} {environment : Core.Environment}
    (references : AccountRuntime.frameReferences (slotTypes slots) = .ok cells)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id environment)
    (related : StateRel (model layout (prefixRead layout.boundary initial)) world source final)
    {name : String} {value : Core.Value} (observed : PassiveCell layout slots initial name value) :
    FrameCellObserved cells environment final name value := by
  obtain ⟨slot, member, named, memory, size, below, stored⟩ := observed
  apply FrameCellObserved.of_compilation (type := slot.type) references
    (List.mem_map.mpr ⟨slot, member, by simp only [named]⟩)
  · intro binding index looked
    exact runtime slot member binding index (by simpa only [named] using looked)
  · have retained := related.external.2.2.2.2 slot.location memory size
    simpa only [prefixRead, below, ↓reduceIte, stored] using retained

theorem memory_observed {layout : Layout} {baseline : Nat → Option Core.Value}
    {slots : List EffectSlot} {store : Core.Store} {world : World}
    {source : Semantics.State MemorySemantics.State} {cells : AccountRuntime.References}
    {environment : Core.Environment}
    (references : AccountRuntime.frameReferences (slotTypes slots) = .ok cells)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id environment)
    (member : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (related : StateRel (model layout baseline) world source store) :
    FrameCellObserved cells environment store "memory" (Core.WordMapping.encode source.external.words) := by
  apply FrameCellObserved.of_compilation references
    (List.mem_map.mpr ⟨⟨"memory", Core.WordMapping.type, layout.memory⟩, member, rfl⟩)
  · exact runtime _ member
  · exact (memory_related related).memory

def snapshotValues (values : String → Core.Value) (memory : MemorySemantics.State) (name : String) : Core.Value :=
  if name = "memory" then Core.WordMapping.encode memory.words else values name

/-- Compilation, the independent source derivation and initialized cells are
sufficient for the complete emitted frame, including snapshot lookup faults. -/
theorem compileFrame_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {memoryLocation sizeLocation : Nat} {initialMemory : MemorySemantics.State}
    {initialStore store : Core.Store} {values environment : Core.Environment} {argument : Core.Expr}
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: environment))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, memoryLocation⟩ ∈ slots)
    (sizeMember : ⟨"memorySize", .word, sizeLocation⟩ ∈ slots)
    (memoryInitial : MemoryCorrespondence.StateRel memoryLocation sizeLocation initialMemory store)
    {final : Semantics.State MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) MemorySemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initialMemory⟩ result final)
    (accounts : StorageCorrespondence.Accounts) (address : Core.Word) (complete : Bool)
    (worldObserved : PassiveCell (initialLayout memoryInitial) slots store "world" (StorageCorrespondence.world accounts))
    (addressObserved : PassiveCell (initialLayout memoryInitial) slots store "address" (.word address))
    (completeObserved : PassiveCell (initialLayout memoryInitial) slots store "worldComplete" (.bool complete))
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ frameSnapshotNames, name ≠ "memory" →
      PassiveCell (initialLayout memoryInitial) slots store name (snapshot name)) :
    ∃ extension status finalStore,
      ResultRel .unit result status ∧
      Core.Evaluates environment initialStore (.apply compiled argument)
        (frameCompletionValue status (snapshotValues snapshot final.external)
          (StorageCorrespondence.get accounts address complete)) finalStore ∧
      StateRel (model (initialLayout memoryInitial) (prefixRead store.length store)) extension final finalStore := by
  obtain ⟨own, body, cells, assembled, references, rfl⟩ := compileFrame_components accepted
  have selected := frame_selected accepted
  obtain ⟨signatures, codes, selectedFunction, selectedCode, index, _, sourceSelected,
    signatureCompiled, _, _, _, _, _⟩ := assemble_selection assembled
  have sameFunction := Option.some.inj (sourceSelected.symm.trans selected)
  subst selectedFunction
  obtain ⟨parameters, resultType⟩ := frame_signature signatureCompiled
  have argumentValues : ValuesRel own.parameters [] [] := by rw [parameters]; exact .nil
  obtain ⟨extension, status, bodyStore, related, executed, state, _⟩ :=
    assemble_program (initialLayout memoryInitial) (prefixRead store.length store) slots
      memoryMember sizeMember assembled selected eligible argumentValues evaluated
      (runtimeValues := values.reverse) (caller := bundleValues values :: environment)
      (by simpa [AccountRuntime.frameScope, slotTypes] using length)
      (frame_coverage _) runtime separated (initial_state memoryInitial)
  have finalWorld := passive_observed references runtime state worldObserved
  have finalAddress := passive_observed references runtime state addressObserved
  have finalComplete := passive_observed references runtime state completeObserved
  have finalSnapshot : ∀ name ∈ frameSnapshotNames,
      FrameCellObserved cells (values.reverse ++ .unit :: bundleValues values :: environment)
        bodyStore name (snapshotValues snapshot final.external name) := by
    intro name member
    by_cases memory : name = "memory"
    · subst name
      exact memory_observed references runtime memoryMember state
    · simpa only [snapshotValues, memory, ↓reduceIte] using
        passive_observed references runtime state (snapshotObserved name member memory)
  have completed := frameCompletion_evaluates executed accounts address complete
    finalWorld finalAddress finalComplete finalSnapshot
  obtain ⟨suffix, _, extended⟩ := StorageCorrespondence.getStore_extension accounts address complete
    (status :: (values.reverse ++ .unit :: bundleValues values :: environment)) bodyStore
  refine ⟨extension, status, _, by simpa only [resultType] using related,
    frameUnpack_evaluates (by simpa only [slotTypes, List.length_map] using length) supplied completed, ?_⟩
  rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
  simpa only [List.nil_append] using state.appendCore suffix

/-- The same source-driven frame theorem applies to the installed closure,
with its original capture environment and the actual later call expression. -/
theorem compileFrame_call_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {memoryLocation sizeLocation : Nat} {initialMemory : MemorySemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment} {function argument : Core.Expr}
    {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, memoryLocation⟩ ∈ slots)
    (sizeMember : ⟨"memorySize", .word, sizeLocation⟩ ∈ slots)
    (memoryInitial : MemoryCorrespondence.StateRel memoryLocation sizeLocation initialMemory store)
    {final : Semantics.State MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) MemorySemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initialMemory⟩ result final)
    (accounts : StorageCorrespondence.Accounts) (address : Core.Word) (complete : Bool)
    (worldObserved : PassiveCell (initialLayout memoryInitial) slots store "world" (StorageCorrespondence.world accounts))
    (addressObserved : PassiveCell (initialLayout memoryInitial) slots store "address" (.word address))
    (completeObserved : PassiveCell (initialLayout memoryInitial) slots store "worldComplete" (.bool complete))
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ frameSnapshotNames, name ≠ "memory" →
      PassiveCell (initialLayout memoryInitial) slots store name (snapshot name)) :
    ∃ extension status finalStore,
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues snapshot final.external)
          (StorageCorrespondence.get accounts address complete)) finalStore ∧
      StateRel (model (initialLayout memoryInitial) (prefixRead store.length store)) extension final finalStore := by
  obtain ⟨own, body, cells, assembled, references, rfl⟩ := compileFrame_components accepted
  have selected := frame_selected accepted
  obtain ⟨signatures, codes, selectedFunction, selectedCode, index, _, sourceSelected,
    signatureCompiled, _, _, _, _, _⟩ := assemble_selection assembled
  have sameFunction := Option.some.inj (sourceSelected.symm.trans selected)
  subst selectedFunction
  obtain ⟨parameters, resultType⟩ := frame_signature signatureCompiled
  have argumentValues : ValuesRel own.parameters [] [] := by rw [parameters]; exact .nil
  obtain ⟨extension, status, bodyStore, related, executed, state, _⟩ :=
    assemble_program (initialLayout memoryInitial) (prefixRead store.length store) slots
      memoryMember sizeMember assembled selected eligible argumentValues evaluated
      (runtimeValues := values.reverse) (caller := bundleValues values :: captured)
      (by simpa [AccountRuntime.frameScope, slotTypes] using length)
      (frame_coverage _) runtime separated (initial_state memoryInitial)
  have finalWorld := passive_observed references runtime state worldObserved
  have finalAddress := passive_observed references runtime state addressObserved
  have finalComplete := passive_observed references runtime state completeObserved
  have finalSnapshot : ∀ name ∈ frameSnapshotNames,
      FrameCellObserved cells (values.reverse ++ .unit :: bundleValues values :: captured)
        bodyStore name (snapshotValues snapshot final.external name) := by
    intro name member
    by_cases memory : name = "memory"
    · subst name
      exact memory_observed references runtime memoryMember state
    · simpa only [snapshotValues, memory, ↓reduceIte] using
        passive_observed references runtime state (snapshotObserved name member memory)
  have completed := frameCompletion_evaluates executed accounts address complete
    finalWorld finalAddress finalComplete finalSnapshot
  obtain ⟨suffix, _, extended⟩ := StorageCorrespondence.getStore_extension accounts address complete
    (status :: (values.reverse ++ .unit :: bundleValues values :: captured)) bodyStore
  refine ⟨extension, status, _, by simpa only [resultType] using related,
    frameUnpack_call_evaluates (by simpa only [slotTypes, List.length_map] using length) closureRelated resolved supplied completed, ?_⟩
  rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
  simpa only [List.nil_append] using state.appendCore suffix

end Solcore.Frontend.RustHull.MemoryFrameCorrespondence
