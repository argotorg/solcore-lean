import Solcore.Frontend.RustHull.RuntimeLinkedWorldCorrespondence
import Solcore.Frontend.RustHull.EffectStateCorrespondence

/-! Code links strengthen any concrete prefix-based runtime model. The source
world and the exact encoded world share one witness, including executable IDs. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeLinkedStateCorrespondence
open Correspondence

def LinkedRead (anchors : List CatalogWorldCorrespondence.Anchor) (source : StorageSemantics.World)
    (location : Nat) (read : Nat → Option Core.Value) : Prop :=
  ∃ accounts : StorageCorrespondence.Accounts, accounts.map Prod.fst = source ∧
    CatalogWorldCorrespondence.Links anchors accounts ∧ read location = some (StorageCorrespondence.world accounts)

def model {σ : Type} (boundary : Nat) (resources : σ → (Nat → Option Core.Value) → Prop)
    (anchors : List CatalogWorldCorrespondence.Anchor) (worldLocation : Nat)
    (sourceWorld : σ → StorageSemantics.World) : StateModel σ :=
  StateModel.cutoff boundary (fun state read => resources state read ∧ LinkedRead anchors (sourceWorld state) worldLocation read)

theorem base_related {σ : Type} {boundary : Nat} {resources : σ → (Nat → Option Core.Value) → Prop}
    {anchors : List CatalogWorldCorrespondence.Anchor} {worldLocation : Nat} {sourceWorld : σ → StorageSemantics.World}
    {world : World} {state : Semantics.State σ} {store : Core.Store}
    (related : StateRel (model boundary resources anchors worldLocation sourceWorld) world state store) :
    StateRel (StateModel.cutoff boundary resources) world state store :=
  ⟨related.toHeapRel, related.external.1, related.external.2.1, related.external.2.2.1⟩

theorem linked_related {σ : Type} {boundary : Nat} {resources : σ → (Nat → Option Core.Value) → Prop}
    {anchors : List CatalogWorldCorrespondence.Anchor} {worldLocation : Nat} {sourceWorld : σ → StorageSemantics.World}
    {world : World} {state : Semantics.State σ} {store : Core.Store}
    (below : worldLocation < boundary)
    (related : StateRel (model boundary resources anchors worldLocation sourceWorld) world state store) :
    RuntimeLinkedWorldCorrespondence.StateRel anchors (sourceWorld state.external) worldLocation store := by
  obtain ⟨accounts, source, linked, read⟩ := related.external.2.2.2
  exact ⟨accounts, source, linked, by simpa only [prefixRead, below, ↓reduceIte] using read⟩

theorem of_base {σ : Type} {boundary : Nat} {resources : σ → (Nat → Option Core.Value) → Prop}
    {anchors : List CatalogWorldCorrespondence.Anchor} {worldLocation : Nat} {sourceWorld : σ → StorageSemantics.World}
    {world : World} {state : Semantics.State σ} {store : Core.Store}
    (below : worldLocation < boundary)
    (related : StateRel (StateModel.cutoff boundary resources) world state store)
    (linked : RuntimeLinkedWorldCorrespondence.StateRel anchors (sourceWorld state.external) worldLocation store) :
    StateRel (model boundary resources anchors worldLocation sourceWorld) world state store := by
  obtain ⟨accounts, source, links, read⟩ := linked
  exact ⟨related.toHeapRel, related.external.1, related.external.2.1, related.external.2.2,
    accounts, source, links, by simpa only [prefixRead, below, ↓reduceIte] using read⟩

end Solcore.Frontend.RustHull.RuntimeLinkedStateCorrespondence
