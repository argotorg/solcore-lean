import Solcore.Frontend.RustHull.RuntimeChildCallStateCorrespondence
import Solcore.Frontend.RustHull.AccountCallChildCallbackCorrespondence

/-! Concrete child dispatch discharges the caller transport interface. Child
frames can change four shared cells; caller memory, return data and captured
context remain available for the subsequent transport steps. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeChildCallEffectsCorrespondence
open Core Correspondence
open RuntimeCallEffectsCorrespondence (Layout Handlers sharedLocations localLocations)

theorem shared_mutable_included (layout : Layout) {location : Nat}
    (member : location ∈ (sharedLocations layout).mutable) :
    location ∈ RuntimeCallEffectsCorrespondence.callMutable layout := by
  simp only [sharedLocations, AccountCallCorrespondence.SharedLocations.mutable,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> simp [RuntimeCallEffectsCorrespondence.callMutable]

theorem shared_frame {layout : Layout} {initial final : Core.Store}
    (frame : AccountCallCorrespondence.SharedFrame (sharedLocations layout) initial final) :
    RuntimeCallEffectsCorrespondence.Frame layout initial final :=
  ⟨frame.length_le, fun location value outside found =>
    frame.read location value (fun member => outside (shared_mutable_included layout member)) found⟩

def childReady (layout : Layout) (context : Context layout) (store : Core.Store) : Prop :=
  layout.boundary ≤ store.length ∧ context.valid (prefixRead layout.boundary store)

theorem childReady_preserved {layout : Layout} {context : Context layout} {initial final : Core.Store}
    (frame : AccountCallCorrespondence.SharedFrame (sharedLocations layout) initial final)
    (ready : childReady layout context initial) : childReady layout context final :=
  ⟨Nat.le_trans ready.1 frame.length_le, context.transport ready.1 (shared_frame frame) ready.2⟩

abbrev ChildExecution (layout : Layout) (handlers : Handlers layout) (anchors : Anchors)
    (context : Context layout) (children : AccountCallSemantics.Children) : Prop :=
  AccountCallCorrespondence.ChildRunPreservation anchors (sharedLocations layout)
    handlers.dispatch.shared handlers.dispatch.runFrame children (childReady layout context)
    handlers.dispatch.depth handlers.dispatch.captured

theorem callback_preserves (layout : Layout) (handlers : Handlers layout) (anchors : Anchors)
    (context : Context layout) (children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children)
    (parent : RuntimeCallEffectsSemantics.State)
    (source : parent.runtime.runtime.runtime.runtime.runtime.storage.address = handlers.source)
    (childExecution : ChildExecution layout handlers anchors context (children parent)) :
    CallbackPreservation layout handlers anchors context children parent := by
  intro request shared finalShared result computed state environment store function argument related localRelated resolved supplied
  rw [source] at computed
  obtain ⟨target, final, evaluated, resultRelated, sharedFinal, frame⟩ :=
    handlers.handler.apply_children_preserves handlers.dispatch childExecution (fun frame ready => childReady_preserved frame ready)
      computed ⟨related.1.1, related.2.1⟩ related.2.2 related.1.2.2 resolved supplied
  have separated : ∀ location ∈ [layout.memory, layout.storage.memorySize, layout.returnData,
      layout.returnDataSize, layout.callHandler, layout.dispatcher], location ∉ (sharedLocations layout).mutable := by
    have distinct := layout.callDistinct
    simp only [StorageBuiltinCorrespondence.Locations.all, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or] at distinct
    intro location member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [sharedLocations, AccountCallCorrespondence.SharedLocations.mutable,
      List.mem_cons, List.not_mem_nil, or_false, not_or]
    all_goals simp_all [ne_comm]
  have keep {location : Nat} {value : Core.Value}
      (member : location ∈ [layout.memory, layout.storage.memorySize, layout.returnData,
        layout.returnDataSize, layout.callHandler, layout.dispatcher])
      (found : store.read? location = some value) : final.read? location = some value :=
    frame.read location value (separated location member) found
  refine ⟨target, final, resultRelated, evaluated,
    ⟨localRelated.distinct, keep (by simp [localLocations, CallTransportCorrespondence.Locations.resources]) localRelated.memory,
      keep (by simp [localLocations, CallTransportCorrespondence.Locations.resources]) localRelated.memorySize,
      keep (by simp [localLocations, CallTransportCorrespondence.Locations.resources]) localRelated.logs,
      keep (by simp [localLocations, CallTransportCorrespondence.Locations.resources]) localRelated.logSize⟩,
    ⟨⟨sharedFinal.shared, keep (by simp) related.1.2.1, keep (by simp) related.1.2.2⟩,
      sharedFinal.linked, childReady_preserved frame related.2.2⟩, shared_frame frame⟩

end Solcore.Frontend.RustHull.RuntimeChildCallEffectsCorrespondence
