import Solcore.Frontend.RustHull.RuntimeCallModeStateCorrespondence
import Solcore.Frontend.RustHull.RuntimeChildCallCallbackCorrespondence
import Solcore.Frontend.RustHull.AccountCallModeCallbackCorrespondence

/-! Each selected call mode reaches the actual captured dispatcher. The fixed
handler captures survive child execution alongside the parent frame resources. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallModeEffectsCorrespondence
open Core Correspondence
open RuntimeCallEffectsCorrespondence (Layout sharedLocations localLocations)
open RuntimeChildCallEffectsCorrespondence
  (Anchors Context childReady childReady_preserved shared_frame)

abbrev ChildExecution (layout : Layout) (handlers : ModeHandlers layout) (anchors : Anchors)
    (context : Context layout) (mode : AccountCallSemantics.Mode) (children : AccountCallSemantics.Children) : Prop :=
  AccountCallModeCorrespondence.ChildRunPreservation mode anchors (sharedLocations layout)
    handlers.ordinary.dispatch.shared handlers.ordinary.dispatch.runFrame children (childReady layout (handlers.context context))
    handlers.ordinary.dispatch.depth handlers.ordinary.dispatch.captured

theorem callback_preserves (layout : Layout) (handlers : ModeHandlers layout) (anchors : Anchors)
    (context : Context layout) (children : RuntimeCallModeSemantics.State → AccountCallSemantics.Children)
    (operation : RuntimeCallModeSemantics.Operation) (parent : RuntimeCallModeSemantics.State)
    (source : parent.runtime.runtime.runtime.runtime.runtime.storage.address = handlers.ordinary.source)
    (childExecution : ChildExecution layout handlers anchors context operation.mode (children parent)) :
    CallbackPreservation layout handlers anchors context children operation parent := by
  intro request shared finalShared result computed state environment store function argument related localRelated resolved supplied
  rw [source] at computed
  obtain ⟨target, final, evaluated, resultRelated, sharedFinal, frame⟩ :=
    (handlers.closure operation).apply_children_preserves handlers.ordinary.dispatch childExecution (fun frame ready => childReady_preserved frame ready)
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


end Solcore.Frontend.RustHull.RuntimeCallModeEffectsCorrespondence
