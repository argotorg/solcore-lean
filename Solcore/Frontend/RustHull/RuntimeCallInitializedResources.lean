import Solcore.Frontend.RustHull.RuntimeCallInitializedEffects
import Solcore.Frontend.RustHull.RuntimeCallResourcesCorrespondence
import Solcore.Frontend.RustHull.RuntimeReturnDataInitializedEffects

/-! Actual named slots distinguish mutable caller and shared data from all
other environment observations, including optional code images. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallInitializedEffects
open Correspondence ContractCallCorrespondence RuntimeCallEffectsCorrespondence

theorem base_members {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {runtime : RuntimeInitializedEffects.StateReady cells store state}
    {words : LogsSemantics.Words} {cursor : Core.Word} {logs : RuntimeLogInitializedEffects.Ready runtime words cursor}
    {balances : StorageSemantics.Words} {accounts : RuntimeAccountInitializedEffects.Ready logs balances}
    {withCode : Bool} {image : Option (List UInt8)} {data : MemorySemantics.Entries} {size : Core.Word}
    (ready : RuntimeReturnDataInitializedEffects.Ready accounts withCode image data size) :
    ∀ slot ∈ baseSlots ready.layout, slot ∈ cells.map InitializedCell.effectSlot := by
  intro slot member
  simp only [baseSlots, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact ready.dataMember
    | exact ready.dataSizeMember
    | (simpa only [ready.base] using accounts.balancesMember)
    | (simpa only [ready.base, accounts.base] using logs.logsMember)
    | (simpa only [ready.base, accounts.base] using logs.logSizeMember)
    | (simpa only [ready.base, accounts.base, logs.base, RuntimeEffectsCorrespondence.initialLayout] using runtime.memoryMember)
    | (simpa only [ready.base, accounts.base, logs.base, RuntimeEffectsCorrespondence.initialLayout] using runtime.worldMember)
    | (simpa only [ready.base, accounts.base, logs.base, RuntimeEffectsCorrespondence.initialLayout] using runtime.addressMember)
    | (simpa only [ready.base, accounts.base, logs.base, RuntimeEffectsCorrespondence.initialLayout] using runtime.completeMember)
    | (simpa only [ready.base, accounts.base, logs.base, RuntimeEffectsCorrespondence.initialLayout] using runtime.staticMember)
    | (simpa only [ready.base, accounts.base, logs.base, RuntimeEffectsCorrespondence.initialLayout] using runtime.exitMember)
    | (simpa only [ready.base, accounts.base, logs.base, RuntimeEffectsCorrespondence.initialLayout] using runtime.offsetMember)
    | (simpa only [ready.base, accounts.base, logs.base, RuntimeEffectsCorrespondence.initialLayout] using runtime.returnSizeMember)
    | (simpa only [ready.base, accounts.base, logs.base, RuntimeEffectsCorrespondence.initialLayout] using runtime.sizeMember)

def mutableSlots (layout : Layout) : List EffectSlot :=
  [⟨"memory", Core.WordMapping.type, layout.memory⟩,
   ⟨"memorySize", .word, layout.storage.memorySize⟩,
   ⟨"returnData", Core.WordMapping.type, layout.returnData⟩,
   ⟨"returnDataSize", .word, layout.returnDataSize⟩,
   ⟨"world", AccountState.type, layout.storage.world⟩,
   ⟨"logs", Core.WordMapping.type, layout.logs⟩,
   ⟨"logSize", .word, layout.logSize⟩,
   ⟨"balances", Core.WordMapping.type, layout.balances⟩]

theorem call_passive {cells : List InitializedCell} {layout : Layout}
    (unique : (cells.map InitializedCell.name).Nodup) (separate : CellLocations cells)
    (members : ∀ slot ∈ baseSlots layout.toReturnDataLayout, slot ∈ cells.map InitializedCell.effectSlot)
    (codeMembers : ∀ code, layout.codeCells = some code →
      ⟨"code", Core.WordMapping.type, code.code⟩ ∈ cells.map InitializedCell.effectSlot ∧
      ⟨"codeKnown", .bool, code.known⟩ ∈ cells.map InitializedCell.effectSlot) :
    CallPassive layout (cells.map InitializedCell.effectSlot) := by
  have names : ∀ first ∈ cells.map InitializedCell.effectSlot, ∀ second ∈ cells.map InitializedCell.effectSlot,
      first.location = second.location → first.name = second.name := by
    intro first firstMember second secondMember same
    obtain ⟨left, leftMember, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨right, rightMember, rfl⟩ := List.mem_map.mp secondMember
    exact separate left leftMember right rightMember same
  have mutableMember : ∀ slot ∈ mutableSlots layout, slot ∈ cells.map InitializedCell.effectSlot := by
    intro slot member
    apply members slot
    simp only [mutableSlots, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [baseSlots]
  have mutableProjection : (mutableSlots layout).map EffectSlot.location = callMutable layout := rfl
  have outside : ∀ slot ∈ cells.map InitializedCell.effectSlot,
      slot.name ∉ ["memory", "memorySize", "returnData", "returnDataSize", "world", "logs", "logSize", "balances"] →
      slot.location ∉ callMutable layout := by
    intro slot member absent inside
    rw [← mutableProjection] at inside
    obtain ⟨other, otherMember, same⟩ := List.mem_map.mp inside
    have named := names slot member other (mutableMember other otherMember) same.symm
    apply absent
    rw [named]
    have present := List.mem_map_of_mem (f := EffectSlot.name) otherMember
    exact present
  refine ⟨?_, ?_, ?_⟩
  · intro code present
    obtain ⟨codeMember, knownMember⟩ := codeMembers code present
    exact ⟨outside _ codeMember (by simp), outside _ knownMember (by simp)⟩
  · intro slot member named _
    exact named_slot_location unique member
      (members ⟨"returnDataSize", .word, layout.returnDataSize⟩ (by simp [baseSlots])) named
  · intro slot member different state value observed inside
    rw [← mutableProjection] at inside
    obtain ⟨other, otherMember, same⟩ := List.mem_map.mp inside
    have named := names slot member other (mutableMember other otherMember) same.symm
    simp only [mutableSlots, List.mem_cons, List.not_mem_nil, or_false] at otherMember
    rcases otherMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact different named
      | (rw [named] at observed; cases slot.type <;> contradiction)

theorem shared_cells {cells sharedCells : List InitializedCell} {base : Base}
    (members : ∀ slot ∈ baseSlots base, slot ∈ cells.map InitializedCell.effectSlot)
    (origin : ∀ cell ∈ cells, sharedOrigin sharedCells cell) :
    SharedCells sharedCells ⟨base.storage.world, base.logs, base.logSize, base.balances, base.storage.complete⟩ := by
  have selected : ∀ slot ∈ baseSlots base, slot.name ∈ dispatchSharedNames →
      ∃ cell ∈ sharedCells, cell.name = slot.name ∧ cell.reference = .cellRef slot.type slot.location := by
    intro slot member named
    obtain ⟨cell, cellMember, rfl⟩ := List.mem_map.mp (members slot member)
    exact ⟨cell, origin cell cellMember named, rfl, rfl⟩
  exact ⟨selected ⟨"world", AccountState.type, base.storage.world⟩ (by simp [baseSlots]) (by simp [dispatchSharedNames]),
    selected ⟨"logs", Core.WordMapping.type, base.logs⟩ (by simp [baseSlots]) (by simp [dispatchSharedNames]),
    selected ⟨"logSize", .word, base.logSize⟩ (by simp [baseSlots]) (by simp [dispatchSharedNames]),
    selected ⟨"balances", Core.WordMapping.type, base.balances⟩ (by simp [baseSlots]) (by simp [dispatchSharedNames]),
    selected ⟨"worldComplete", .bool, base.storage.complete⟩ (by simp [baseSlots]) (by simp [dispatchSharedNames])⟩

end Solcore.Frontend.RustHull.RuntimeCallInitializedEffects
