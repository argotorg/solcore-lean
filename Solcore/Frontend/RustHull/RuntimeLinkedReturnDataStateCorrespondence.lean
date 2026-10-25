import Solcore.Frontend.RustHull.RuntimeLinkedStateCorrespondence
import Solcore.Frontend.RustHull.RuntimeReturnDataStateCorrespondence

/-! Call-free child frames preserve exact executable identities alongside their
ordinary runtime state. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeLinkedReturnDataEffectsCorrespondence
open Correspondence
open RuntimeReturnDataEffectsCorrespondence (Layout Resources)
abbrev Anchors := List CatalogWorldCorrespondence.Anchor

def sourceWorld (state : RuntimeReturnDataEffectsSemantics.State) : StorageSemantics.World :=
  state.runtime.runtime.runtime.runtime.storage.world

def model (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot)
    (image : Option (List UInt8)) (anchors : Anchors) : StateModel RuntimeReturnDataEffectsSemantics.State :=
  RuntimeLinkedStateCorrespondence.model layout.boundary (Resources layout baseline slots image)
    anchors layout.storage.world sourceWorld

theorem world_below (layout : Layout) : layout.storage.world < layout.boundary :=
  layout.below _ (by simp [StorageBuiltinCorrespondence.Locations.all])

theorem base_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {anchors : Anchors} {world : World}
    {state : Semantics.State RuntimeReturnDataEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image anchors) world state store) :
    StateRel (RuntimeReturnDataEffectsCorrespondence.model layout baseline slots image) world state store :=
  RuntimeLinkedStateCorrespondence.base_related related

theorem linked_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {anchors : Anchors} {world : World}
    {state : Semantics.State RuntimeReturnDataEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image anchors) world state store) :
    RuntimeLinkedWorldCorrespondence.StateRel anchors (sourceWorld state.external) layout.storage.world store :=
  RuntimeLinkedStateCorrespondence.linked_related (world_below layout) related

theorem of_base {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {anchors : Anchors} {world : World}
    {state : Semantics.State RuntimeReturnDataEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (RuntimeReturnDataEffectsCorrespondence.model layout baseline slots image) world state store)
    (linked : RuntimeLinkedWorldCorrespondence.StateRel anchors (sourceWorld state.external) layout.storage.world store) :
    StateRel (model layout baseline slots image anchors) world state store :=
  RuntimeLinkedStateCorrespondence.of_base (world_below layout) related linked

end Solcore.Frontend.RustHull.RuntimeLinkedReturnDataEffectsCorrespondence
