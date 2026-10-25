import Solcore.Frontend.RustHull.RuntimeLinkedStateCorrespondence
import Solcore.Frontend.RustHull.RuntimeCallTransportModel
import Solcore.Frontend.RustHull.ChildFrameSemantics

/-! Child-capable callers retain exact catalog links in addition to the
existing memory, account, environment and installed-handler resources. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeChildCallEffectsCorrespondence
open Correspondence
open RuntimeCallEffectsCorrespondence (Layout Handlers SharedResources sharedLocations localLocations Frame)

abbrev Anchors := List CatalogWorldCorrespondence.Anchor

/-- Immutable captured resources, such as ambient observations and the creator
cell, may be inspected by a child initializer. Changes to caller/shared mutable
cells do not invalidate these concrete reads. -/
structure Context (layout : Layout) where
  valid : (Nat → Option Core.Value) → Prop
  frame : ∀ {before after : Nat → Option Core.Value},
    (∀ location, location ∉ RuntimeCallEffectsCorrespondence.mutable layout → after location = before location) →
    valid before → valid after

def Context.trivial (layout : Layout) : Context layout := ⟨fun _ => True, fun _ _ => True.intro⟩

theorem mutable_included (layout : Layout) {location : Nat}
    (member : location ∈ RuntimeCallEffectsCorrespondence.callMutable layout) :
    location ∈ RuntimeCallEffectsCorrespondence.mutable layout := by
  simp only [RuntimeCallEffectsCorrespondence.callMutable, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [RuntimeCallEffectsCorrespondence.mutable, RuntimeLogEffectsCorrespondence.mutable,
      RuntimeEffectsCorrespondence.mutable, StorageBuiltinCorrespondence.Locations.mutable]

theorem Context.transport {layout : Layout} (context : Context layout) {initial final : Core.Store}
    (bounded : layout.boundary ≤ initial.length) (frame : Frame layout initial final)
    (before : context.valid (prefixRead layout.boundary initial)) :
    context.valid (prefixRead layout.boundary final) := by
  apply context.frame _ before
  intro location outside
  by_cases below : location < layout.boundary
  · have bound := Nat.lt_of_lt_of_le below bounded
    simpa only [prefixRead, below, ↓reduceIte, Core.Store.read?] using
      (frame.read location _ (fun member => outside (mutable_included layout member))
        (List.getElem?_eq_getElem bound)).trans (List.getElem?_eq_getElem bound).symm
  · simp only [prefixRead, below, ↓reduceIte]

def sourceWorld (state : RuntimeCallEffectsSemantics.State) : StorageSemantics.World :=
  (RuntimeCallEffectsSemantics.shared state).world

def model (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot)
    (image : Option (List UInt8)) (handlers : Handlers layout) (anchors : Anchors) (context : Context layout) : StateModel RuntimeCallEffectsSemantics.State :=
  RuntimeLinkedStateCorrespondence.model layout.boundary
    (fun state read => RuntimeCallEffectsCorrespondence.Resources layout baseline slots image handlers state read ∧ context.valid read)
    anchors layout.storage.world sourceWorld

theorem world_below (layout : Layout) : layout.storage.world < layout.boundary :=
  layout.below _ (by simp [StorageBuiltinCorrespondence.Locations.all])

theorem base_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {anchors : Anchors} {context : Context layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image handlers anchors context) world state store) :
    StateRel (RuntimeCallEffectsCorrespondence.model layout baseline slots image handlers) world state store :=
  ⟨related.toHeapRel, related.external.1, related.external.2.1, related.external.2.2.1.1⟩

theorem linked_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {anchors : Anchors} {context : Context layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image handlers anchors context) world state store) :
    RuntimeLinkedWorldCorrespondence.StateRel anchors (sourceWorld state.external) layout.storage.world store :=
  RuntimeLinkedStateCorrespondence.linked_related (world_below layout) related

theorem of_base {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {anchors : Anchors} {context : Context layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (RuntimeCallEffectsCorrespondence.model layout baseline slots image handlers) world state store)
    (linked : RuntimeLinkedWorldCorrespondence.StateRel anchors (sourceWorld state.external) layout.storage.world store)
    (captured : context.valid (prefixRead layout.boundary store)) :
    StateRel (model layout baseline slots image handlers anchors context) world state store :=
  RuntimeLinkedStateCorrespondence.of_base (world_below layout)
    ⟨related.toHeapRel, related.external.1, related.external.2.1, related.external.2.2, captured⟩ linked

theorem Context.updated {layout : Layout} (context : Context layout)
    {baseline : Nat → Option Core.Value} {slots : List EffectSlot} {image : Option (List UInt8)} {handlers : Handlers layout}
    {beforeWorld afterWorld : World} {beforeState afterState : Semantics.State RuntimeCallEffectsSemantics.State}
    {initial final : Core.Store}
    (before : StateRel (RuntimeCallEffectsCorrespondence.model layout baseline slots image handlers) beforeWorld beforeState initial)
    (after : StateRel (RuntimeCallEffectsCorrespondence.model layout baseline slots image handlers) afterWorld afterState final)
    (captured : context.valid (prefixRead layout.boundary initial)) :
    context.valid (prefixRead layout.boundary final) := by
  apply context.frame _ captured
  intro location outside
  rw [RuntimeCallEffectsCorrespondence.other_related after outside,
    RuntimeCallEffectsCorrespondence.other_related before outside]

def transportModel (layout : Layout) (handlers : Handlers layout) (anchors : Anchors) (context : Context layout) :
    CallTransportCorrespondence.Model AccountCallSemantics.Shared (localLocations layout) where
  related shared store := SharedResources layout handlers shared store ∧
    RuntimeLinkedWorldCorrespondence.StateRel anchors shared.world layout.storage.world store ∧
    layout.boundary ≤ store.length ∧ context.valid (prefixRead layout.boundary store)
  frame := by
    intro shared initial final frame related
    exact ⟨(RuntimeCallEffectsCorrespondence.transportModel layout handlers).frame frame related.1,
      related.2.1.read_preserved (fun value found => frame.read _ value
        (RuntimeCallEffectsCorrespondence.shared_local_separation layout _ (by simp)) found), Nat.le_trans related.2.2.1 frame.length,
      context.transport related.2.2.1 (Frame.of_local frame) related.2.2.2⟩
  retains := Frame layout
  retainedFrame := Frame.of_local
  retainedTrans := Frame.trans

/-- Internal callback interface. The public theorem supplies this from actual
code selection, fresh child allocation, child execution and checkpoint handling. -/
def CallbackPreservation (layout : Layout) (handlers : Handlers layout) (anchors : Anchors) (context : Context layout)
    (children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children)
    (parent : RuntimeCallEffectsSemantics.State) : Prop :=
  CallTransportCorrespondence.CallbackPreservation (transportModel layout handlers anchors context)
    (AccountCallSemantics.Dispatch (children parent) .ordinary
      parent.runtime.runtime.runtime.runtime.runtime.storage.address) handlers.handlerValue

end Solcore.Frontend.RustHull.RuntimeChildCallEffectsCorrespondence
