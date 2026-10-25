import Solcore.Frontend.RustHull.ChildFrameSharedResources
import Solcore.Frontend.RustHull.AccountCallSharedCorrespondence

/-! Child-local mutable cells are freshly allocated. Only the shared account,
log and balance cells can change below the child's allocation boundary. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildFrameCorrespondence
open Core Correspondence ScalarExecution

def sharedLocations (layout : RuntimeReturnDataEffectsCorrespondence.Layout) : AccountCallCorrespondence.SharedLocations :=
  ⟨layout.storage.world, layout.logs, layout.logSize, layout.balances, layout.storage.complete⟩

def mutable (layout : RuntimeReturnDataEffectsCorrespondence.Layout) : List Nat :=
  layout.returnData :: layout.returnDataSize :: RuntimeLogEffectsCorrespondence.mutable layout.toLogLayout

def mutableSlots (layout : RuntimeReturnDataEffectsCorrespondence.Layout) : List EffectSlot :=
  [⟨"returnData", WordMapping.type, layout.returnData⟩, ⟨"returnDataSize", .word, layout.returnDataSize⟩,
   ⟨"logs", WordMapping.type, layout.logs⟩, ⟨"logSize", .word, layout.logSize⟩,
   ⟨"memory", WordMapping.type, layout.memory⟩, ⟨"memorySize", .word, layout.storage.memorySize⟩,
   ⟨"world", AccountState.type, layout.storage.world⟩, ⟨"exit", .word, layout.storage.exit⟩,
   ⟨"returnOffset", .word, layout.storage.returnOffset⟩, ⟨"returnSize", .word, layout.storage.returnSize⟩]

theorem mutable_early_shared {cells sharedCells : List InitializedCell} {initial allocated : Store}
    {state : RuntimeReturnDataEffectsSemantics.State} {bytes : List UInt8}
    (ready : Ready cells allocated state bytes)
    (signature : sharedCells.map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse)
    (origins : ∀ cell ∈ cells, cell.location < initial.length → cell ∈ sharedCells ∨ cell.name = "createHandler")
    {location : Nat} (below : location < initial.length) (member : location ∈ mutable ready.layout) :
    location ∈ (sharedLocations ready.layout).mutable := by
  have mapped : (mutableSlots ready.layout).map EffectSlot.location = mutable ready.layout := rfl
  rw [← mapped] at member
  obtain ⟨slot, slotMember, same⟩ := List.mem_map.mp member
  have base : slot ∈ RuntimeCallInitializedEffects.baseSlots ready.layout := by
    simp only [mutableSlots, List.mem_cons, List.not_mem_nil, or_false] at slotMember
    rcases slotMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [RuntimeCallInitializedEffects.baseSlots]
  obtain ⟨cell, cellMember, slotEqual⟩ := List.mem_map.mp (ready.members slot base)
  have sameLocation : cell.location = location := (congrArg EffectSlot.location slotEqual).trans same
  rcases origins cell cellMember (sameLocation ▸ below) with shared | creator
  · have present : cell.name ∈ sharedSlotTypes.map Prod.fst := by
      have member := List.mem_map_of_mem (f := fun cell : InitializedCell => (cell.name, cell.type)) shared
      rw [signature] at member
      exact List.mem_map_of_mem (List.mem_reverse.mp member)
    have named : cell.name = slot.name := congrArg EffectSlot.name slotEqual
    rw [named] at present
    simp only [mutableSlots, List.mem_cons, List.not_mem_nil, or_false] at slotMember
    rcases slotMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (solve | simp [sharedSlotTypes, Ambient.slots] at present)
      | (rw [← same]; simp [sharedLocations, AccountCallCorrespondence.SharedLocations.mutable])
  · have named : slot.name = "createHandler" := (congrArg EffectSlot.name slotEqual).symm.trans creator
    simp only [mutableSlots, List.mem_cons, List.not_mem_nil, or_false] at slotMember
    rcases slotMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp at named

theorem other_related {layout : RuntimeReturnDataEffectsCorrespondence.Layout}
    {baseline : Nat → Option Value} {slots : List EffectSlot} {image : Option (List UInt8)}
    {world : World} {state : Semantics.State RuntimeReturnDataEffectsSemantics.State} {store : Store}
    (related : StateRel (RuntimeReturnDataEffectsCorrespondence.model layout baseline slots image) world state store)
    {location : Nat} (outside : location ∉ mutable layout) : prefixRead layout.boundary store location = baseline location := by
  have separate : location ≠ layout.returnData ∧ location ≠ layout.returnDataSize ∧
      location ∉ RuntimeLogEffectsCorrespondence.mutable layout.toLogLayout := by
    simpa only [mutable, List.mem_cons, not_or] using outside
  have passive := RuntimeLogEffectsCorrespondence.other_related
    (RuntimeAccountEffectsCorrespondence.runtime_related (RuntimeReturnDataEffectsCorrespondence.account_related related)) separate.2.2
  simpa only [RuntimeReturnDataEffectsCorrespondence.patched, separate.1, separate.2.1, ↓reduceIte] using passive

theorem parent_frame {cells sharedCells : List InitializedCell} {initial suffix final : Store}
    {state : RuntimeReturnDataEffectsSemantics.State} {bytes : List UInt8}
    (ready : Ready cells (initial ++ suffix) state bytes)
    (signature : sharedCells.map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse)
    (origins : ∀ cell ∈ cells, cell.location < initial.length → cell ∈ sharedCells ∨ cell.name = "createHandler")
    {world : World} {next : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    (related : StateRel (RuntimeReturnDataEffectsCorrespondence.model ready.layout
      (prefixRead ready.layout.boundary (initial ++ suffix)) (cells.map InitializedCell.effectSlot) (some bytes)) world next final) :
    AccountCallCorrespondence.SharedFrame (sharedLocations ready.layout) initial final := by
  refine ⟨?_, ?_⟩
  · have bounded := related.external.1
    rw [ready.boundary] at bounded
    exact Nat.le_trans (by simp) bounded
  · intro location value outside found
    have below : location < initial.length := (List.getElem?_eq_some_iff.mp found).1
    have beforeBoundary : location < ready.layout.boundary := by rw [ready.boundary]; exact Nat.lt_of_lt_of_le below (by simp)
    have preserved := other_related related
      (fun member => outside (mutable_early_shared ready signature origins below member))
    have same : final.read? location = initial.read? location := by
      simpa only [prefixRead, beforeBoundary, ↓reduceIte, Core.Store.read?, List.getElem?_append_left below] using preserved
    exact same.trans found

theorem shared_state {cells : List InitializedCell} {initial final : Store}
    {state : RuntimeReturnDataEffectsSemantics.State} {bytes : List UInt8}
    (ready : Ready cells initial state bytes) (separate : CellLocations cells)
    {world : World} {next : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    (related : StateRel (RuntimeReturnDataEffectsCorrespondence.model ready.layout
      (prefixRead ready.layout.boundary initial) (cells.map InitializedCell.effectSlot) (some bytes)) world next final)
    (depth : Word) :
    AccountCallCorrespondence.SharedStateRel (sharedLocations ready.layout)
      (RuntimeCallEffectsSemantics.shared ⟨next.external, depth⟩) final := by
  have account := RuntimeReturnDataEffectsCorrespondence.account_related related
  have logs := RuntimeAccountEffectsCorrespondence.runtime_related account
  have logState := RuntimeLogEffectsCorrespondence.logs_related logs
  have runtime := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related (RuntimeLogEffectsCorrespondence.runtime_related logs))
  refine ⟨runtime.world, logState.logs.logs, logState.logs.logSize,
    RuntimeAccountEffectsCorrespondence.balances_related account, runtime.complete, ?_⟩
  let selected : List EffectSlot := [⟨"world", AccountState.type, ready.layout.storage.world⟩,
    ⟨"logs", WordMapping.type, ready.layout.logs⟩, ⟨"logSize", .word, ready.layout.logSize⟩,
    ⟨"balances", WordMapping.type, ready.layout.balances⟩, ⟨"worldComplete", .bool, ready.layout.storage.complete⟩]
  have included : ∀ slot ∈ selected, slot ∈ cells.map InitializedCell.effectSlot := by
    intro slot member
    apply ready.members
    simp only [selected, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals simp [RuntimeCallInitializedEffects.baseSlots]
  exact ContractCallCorrespondence.effectSlots_distinct separate included (by change (["world", "logs", "logSize", "balances", "worldComplete"] : List String).Nodup; decide)

theorem shared_cells {cells sharedCells : List InitializedCell} {store : Store}
    {state : RuntimeReturnDataEffectsSemantics.State} {bytes : List UInt8}
    (ready : Ready cells store state bytes)
    (origins : ∀ cell ∈ cells, cell.name ∈ sharedSlotTypes.map Prod.fst → cell ∈ sharedCells) :
    ContractCallCorrespondence.SharedCells sharedCells (sharedLocations ready.layout) := by
  apply RuntimeCallInitializedEffects.shared_cells ready.members
  intro cell member named
  apply origins cell member
  simp only [ContractCallCorrespondence.dispatchSharedNames, List.mem_cons, List.not_mem_nil, or_false] at named
  rcases named with named | named | named | named | named
  all_goals simp [named, sharedSlotTypes]

theorem shared_references_unique {depth : Nat} {environment : Environment}
    {shared : AccountRuntime.References} {left right : AccountCallCorrespondence.SharedLocations}
    (first : AccountCallCorrespondence.SharedReferences depth environment shared left)
    (second : AccountCallCorrespondence.SharedReferences depth environment shared right) : left = right := by
  have world := (Value.cellRef.inj (Core.evaluation_deterministic (first.world.evaluates []) (second.world.evaluates [])).1).2
  have logs := (Value.cellRef.inj (Core.evaluation_deterministic (first.logs.evaluates []) (second.logs.evaluates [])).1).2
  have logSize := (Value.cellRef.inj (Core.evaluation_deterministic (first.logSize.evaluates []) (second.logSize.evaluates [])).1).2
  have balances := (Value.cellRef.inj (Core.evaluation_deterministic (first.balances.evaluates []) (second.balances.evaluates [])).1).2
  have complete := (Value.cellRef.inj (Core.evaluation_deterministic (first.complete.evaluates []) (second.complete.evaluates [])).1).2
  cases left
  cases right
  simp_all

end Solcore.Frontend.RustHull.ChildFrameCorrespondence
