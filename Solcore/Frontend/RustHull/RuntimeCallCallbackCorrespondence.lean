import Solcore.Frontend.RustHull.RuntimeCallTransportModel
import Solcore.Frontend.RustHull.AccountCallCallbackCorrespondence

/-! The caller transport uses the actual installed dispatcher and frame callback.
Their concrete bodies discharge the callback interface at call-tree height zero. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
open Core Correspondence

theorem callback_preserves (layout : Layout) (handlers : Handlers layout) :
    CallTransportCorrespondence.CallbackPreservation (transportModel layout handlers)
      (AccountCallSemantics.Dispatch AccountCallSemantics.noChildren .ordinary handlers.source)
      handlers.handlerValue := by
  intro request shared finalShared result computed state environment store function argument sharedRelated localRelated resolved supplied
  obtain ⟨target, final, evaluated, resultRelated, finalSharedRelated, frame⟩ :=
    handlers.handler.apply_preserves handlers.dispatch computed sharedRelated.1 sharedRelated.2.2 resolved supplied
  have different : ∀ location ∈ [layout.memory, layout.storage.memorySize, layout.returnData,
      layout.returnDataSize, layout.callHandler, layout.dispatcher], location ≠ layout.balances := by
    have distinct := layout.callDistinct
    simp only [StorageBuiltinCorrespondence.Locations.all, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or] at distinct
    intro location member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [ne_comm]
  have keep {location : Nat} {value : Core.Value}
      (member : location ∈ [layout.memory, layout.storage.memorySize, layout.returnData,
        layout.returnDataSize, layout.callHandler, layout.dispatcher])
      (found : store.read? location = some value) : final.read? location = some value :=
    (frame.other location (different location member) (List.getElem?_eq_some_iff.mp found).1).trans found
  refine ⟨target, final, resultRelated, evaluated,
    ⟨localRelated.distinct, keep (by simp [localLocations, CallTransportCorrespondence.Locations.resources]) localRelated.memory,
      keep (by simp [localLocations, CallTransportCorrespondence.Locations.resources]) localRelated.memorySize,
      keep (by simp [localLocations, CallTransportCorrespondence.Locations.resources]) localRelated.logs,
      keep (by simp [localLocations, CallTransportCorrespondence.Locations.resources]) localRelated.logSize⟩,
    ⟨finalSharedRelated, keep (by simp) sharedRelated.2.1, keep (by simp) sharedRelated.2.2⟩,
    frame.length_le, ?_⟩
  intro location value outside found
  have notBalance : location ≠ layout.balances := fun same => outside (by simp [callMutable, same])
  exact (frame.other location notBalance (List.getElem?_eq_some_iff.mp found).1).trans found

theorem frame_closures {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {initial final : Store}
    (related : StateRel (model layout baseline slots image handlers) world state initial)
    (frame : Frame layout initial final) : ClosuresPreserved initial final := by
  have callerRelated := local_related related
  have shared := shared_related related
  intro location parameter result body captured found
  apply frame.read location _ _ found
  intro member
  simp only [callMutable, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have same := Option.some.inj (callerRelated.memory.symm.trans found)
    cases entries : state.external.runtime.runtime.runtime.runtime.runtime.memory.words <;>
      simp only [localLocations, CallTransportCorrespondence.resources, RuntimeCallEffectsSemantics.transport, entries, WordMapping.encode] at same <;> cases same
  · have same := Option.some.inj (callerRelated.memorySize.symm.trans found); cases same
  · have same := Option.some.inj (callerRelated.logs.symm.trans found)
    cases entries : state.external.runtime.returnData <;>
      simp only [localLocations, CallTransportCorrespondence.resources, RuntimeCallEffectsSemantics.transport, entries, WordMapping.encode] at same <;> cases same
  · have same := Option.some.inj (callerRelated.logSize.symm.trans found); cases same
  · obtain ⟨accounts, _, stored⟩ := shared.world
    have same := Option.some.inj (stored.symm.trans found)
    cases accounts <;> simp only [StorageCorrespondence.world] at same <;> cases same
  · have same := Option.some.inj (shared.logs.symm.trans found)
    cases entries : (RuntimeCallEffectsSemantics.shared state.external).logs <;>
      simp only [entries, WordMapping.encode] at same <;> cases same
  · have same := Option.some.inj (shared.logSize.symm.trans found); cases same
  · have same := Option.some.inj (shared.balances.symm.trans found)
    cases entries : (RuntimeCallEffectsSemantics.shared state.external).balances <;>
      simp only [entries, WordMapping.encode] at same <;> cases same

end Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
