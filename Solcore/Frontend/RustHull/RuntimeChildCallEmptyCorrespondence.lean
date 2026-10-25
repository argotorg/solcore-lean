import Solcore.Frontend.RustHull.RuntimeChildCallStateCorrespondence
import Solcore.Frontend.RustHull.RuntimeCallCallbackCorrespondence

/-! Existing child-free callers instantiate the linked model with no anchors
and a trivial captured-context condition. The original public API is unchanged. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeChildCallEffectsCorrespondence
open Correspondence
open RuntimeCallEffectsCorrespondence (Layout Handlers)

theorem empty_state {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (RuntimeCallEffectsCorrespondence.model layout baseline slots image handlers) world state store) :
    StateRel (model layout baseline slots image handlers [] (Context.trivial layout)) world state store := by
  obtain ⟨accounts, same, read⟩ := (RuntimeCallEffectsCorrespondence.shared_related related).world
  exact of_base related ⟨accounts, same, by simp [CatalogWorldCorrespondence.Links], read⟩ True.intro

theorem empty_callback (layout : Layout) (handlers : Handlers layout)
    (parent : RuntimeCallEffectsSemantics.State)
    (source : parent.runtime.runtime.runtime.runtime.runtime.storage.address = handlers.source) :
    CallbackPreservation layout handlers [] (Context.trivial layout)
      (fun _ => AccountCallSemantics.noChildren) parent := by
  intro request shared finalShared result computed state environment store function argument related localRelated resolved supplied
  rw [source] at computed
  obtain ⟨target, final, resultRelated, evaluated, localFinal, sharedFinal, frame⟩ :=
    RuntimeCallEffectsCorrespondence.callback_preserves layout handlers computed related.1 localRelated resolved supplied
  obtain ⟨accounts, same, read⟩ := sharedFinal.1.world
  refine ⟨target, final, resultRelated, evaluated, localFinal, ?_, frame⟩
  exact ⟨sharedFinal, ⟨accounts, same, by simp [CatalogWorldCorrespondence.Links], read⟩,
    Nat.le_trans related.2.2.1 frame.length_le, True.intro⟩

end Solcore.Frontend.RustHull.RuntimeChildCallEffectsCorrespondence
