import Solcore.Frontend.RustHull.RuntimeCallStateCorrespondence
import Solcore.Frontend.RustHull.CallTransportStateCorrespondence

/-! The caller's four writable cells and the shared account cells are extracted
from the full runtime model. Frame rules retain everything outside those cells. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
open Correspondence

abbrev LocalLocations := CallTransportCorrespondence.Locations

def localLocations (layout : Layout) : LocalLocations :=
  ⟨layout.memory, layout.storage.memorySize, layout.returnData, layout.returnDataSize⟩

def callMutable (layout : Layout) : List Nat :=
  [layout.memory, layout.storage.memorySize, layout.returnData, layout.returnDataSize,
    layout.storage.world, layout.logs, layout.logSize, layout.balances]

structure CallPassive (layout : Layout) (slots : List EffectSlot) : Prop where
  code : ∀ cells, layout.codeCells = some cells →
    cells.code ∉ callMutable layout ∧ cells.known ∉ callMutable layout
  size : ∀ slot ∈ slots, slot.name = "returnDataSize" → slot.type = .word → slot.location = layout.returnDataSize
  other : ∀ slot ∈ slots, slot.name ≠ "returnDataSize" → ∀ state value,
    EnvironmentBuiltinCorrespondence.observation state slot.name slot.type = some value → slot.location ∉ callMutable layout

theorem local_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image handlers) world state store) :
    CallTransportCorrespondence.StateRel (localLocations layout) (RuntimeCallEffectsSemantics.transport state.external) store := by
  have runtime := RuntimeEffectsCorrespondence.memory_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related
    (RuntimeLogEffectsCorrespondence.runtime_related
    (RuntimeAccountEffectsCorrespondence.runtime_related (account_related related))))
  refine ⟨?_, runtime.memory, runtime.size,
    RuntimeReturnDataEffectsCorrespondence.data_related (runtime_related related),
    RuntimeReturnDataEffectsCorrespondence.size_related (runtime_related related)⟩
  have distinct := layout.callDistinct
  simp only [StorageBuiltinCorrespondence.Locations.all, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at distinct
  simp only [localLocations, CallTransportCorrespondence.Locations.resources, LogsCorrespondence.Locations.all,
    List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
  simp_all [ne_comm]

theorem shared_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image handlers) world state store) :
    AccountCallCorrespondence.SharedStateRel (sharedLocations layout) (RuntimeCallEffectsSemantics.shared state.external) store := by
  have account := account_related related
  have logs := RuntimeAccountEffectsCorrespondence.runtime_related account
  have logState := RuntimeLogEffectsCorrespondence.logs_related logs
  have runtime := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related (RuntimeLogEffectsCorrespondence.runtime_related logs))
  refine ⟨runtime.world, logState.logs.logs, logState.logs.logSize,
    RuntimeAccountEffectsCorrespondence.balances_related account, runtime.complete, ?_⟩
  have distinct := layout.callDistinct
  simp only [StorageBuiltinCorrespondence.Locations.all, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at distinct
  simp only [sharedLocations, AccountCallCorrespondence.SharedLocations.all,
    List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
  simp_all [ne_comm]

structure Frame (layout : Layout) (initial final : Core.Store) : Prop where
  length_le : initial.length ≤ final.length
  read : ∀ location value, location ∉ callMutable layout → initial.read? location = some value → final.read? location = some value

theorem Frame.refl (layout : Layout) (store : Core.Store) : Frame layout store store :=
  ⟨Nat.le_refl _, fun _ _ _ found => found⟩

theorem Frame.trans {layout : Layout} {first second third : Core.Store}
    (left : Frame layout first second) (right : Frame layout second third) : Frame layout first third :=
  ⟨Nat.le_trans left.length_le right.length_le,
    fun location value outside found => right.read location value outside (left.read location value outside found)⟩

theorem Frame.of_local {layout : Layout} {initial final : Core.Store}
    (frame : CallTransportCorrespondence.Frame (localLocations layout) initial final) : Frame layout initial final := by
  refine ⟨frame.length, ?_⟩
  intro location value outside found
  apply frame.read location value _ found
  intro member
  apply outside
  simp only [localLocations, CallTransportCorrespondence.Locations.resources, LogsCorrespondence.Locations.all,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> simp [callMutable]

theorem mutable_below (layout : Layout) {location : Nat} (member : location ∈ callMutable layout) :
    location < layout.boundary := by
  simp only [callMutable, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact layout.below _ (by simp)
  · exact layout.below _ (by simp [StorageBuiltinCorrespondence.Locations.all])
  · exact layout.dataBelow
  · exact layout.sizeBelow
  · exact layout.below _ (by simp [StorageBuiltinCorrespondence.Locations.all])
  · exact layout.logsBelow
  · exact layout.logSizeBelow
  · exact layout.balancesBelow

theorem Frame.above {layout : Layout} {initial final : Core.Store} (frame : Frame layout initial final) :
    StoreRetainsFrom layout.boundary initial final := by
  refine ⟨frame.length_le, ?_⟩
  intro location above below
  have outside : location ∉ callMutable layout := fun member => Nat.not_lt_of_ge above (mutable_below layout member)
  exact (frame.read location _ outside (List.getElem?_eq_getElem below)).trans (List.getElem?_eq_getElem below).symm

theorem call_fixed_separation (layout : Layout) :
    ∀ location ∈ [layout.callDepth, layout.callHandler, layout.dispatcher, layout.storage.address,
      layout.storage.isStatic, layout.storage.exit, layout.storage.returnOffset, layout.storage.returnSize],
      location ∉ callMutable layout := by
  have distinct := layout.callDistinct
  simp only [StorageBuiltinCorrespondence.Locations.all, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at distinct
  intro location member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [callMutable, List.mem_cons, List.not_mem_nil, or_false, not_or]
  all_goals simp_all [ne_comm]

end Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
