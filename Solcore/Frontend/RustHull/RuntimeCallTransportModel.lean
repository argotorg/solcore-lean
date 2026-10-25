import Solcore.Frontend.RustHull.RuntimeCallUpdateCorrespondence
import Solcore.Frontend.RustHull.CallTransportCallbackCorrespondence

/-! The transport callback model uses actual shared-account reads and installed
optional-cell values. It can be instantiated without assuming callback behavior. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
open Correspondence

def SharedResources (layout : Layout) (handlers : Handlers layout)
    (shared : AccountCallSemantics.Shared) (store : Core.Store) : Prop :=
  AccountCallCorrespondence.SharedStateRel (sharedLocations layout) shared store ∧
  store.read? layout.callHandler = some (.inRight .unit handlers.handlerValue) ∧
  store.read? layout.dispatcher = some (.inRight .unit handlers.dispatchValue)

theorem shared_local_separation (layout : Layout) :
    ∀ location ∈ [layout.storage.world, layout.logs, layout.logSize, layout.balances, layout.storage.complete,
      layout.callHandler, layout.dispatcher],
      location ∉ (localLocations layout).resources.all := by
  have distinct := layout.callDistinct
  simp only [StorageBuiltinCorrespondence.Locations.all, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at distinct
  intro location member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [localLocations, CallTransportCorrespondence.Locations.resources,
    LogsCorrespondence.Locations.all, List.mem_cons, List.not_mem_nil, or_false, not_or]
  all_goals simp_all [ne_comm]

def transportModel (layout : Layout) (handlers : Handlers layout) :
    CallTransportCorrespondence.Model AccountCallSemantics.Shared (localLocations layout) where
  related := SharedResources layout handlers
  frame := by
    intro shared initial final frame related
    have preserved (location : Nat) (value : Core.Value)
        (member : location ∈ [layout.storage.world, layout.logs, layout.logSize, layout.balances, layout.storage.complete,
          layout.callHandler, layout.dispatcher]) (found : initial.read? location = some value) :
        final.read? location = some value := frame.read location value (shared_local_separation layout location member) found
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, related.1.distinct⟩, ?_, ?_⟩
    · obtain ⟨accounts, same, found⟩ := related.1.world
      exact ⟨accounts, same, preserved _ _ (by simp [sharedLocations]) found⟩
    · exact preserved _ _ (by simp [sharedLocations]) related.1.logs
    · exact preserved _ _ (by simp [sharedLocations]) related.1.logSize
    · exact preserved _ _ (by simp [sharedLocations]) related.1.balances
    · exact preserved _ _ (by simp [sharedLocations]) related.1.complete
    · exact preserved _ _ (by simp) related.2.1
    · exact preserved _ _ (by simp) related.2.2
  retains := Frame layout
  retainedFrame := Frame.of_local
  retainedTrans := Frame.trans

theorem shared_resources {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image handlers) world state store) :
    SharedResources layout handlers (RuntimeCallEffectsSemantics.shared state.external) store := by
  refine ⟨shared_related related, ?_, ?_⟩
  · simpa only [prefixRead, layout.handlerBelow, ↓reduceIte] using related.external.2.2.handler
  · simpa only [prefixRead, layout.dispatcherBelow, ↓reduceIte] using related.external.2.2.dispatcher

theorem SharedResources.installed {layout : Layout} {handlers : Handlers layout}
    {shared : AccountCallSemantics.Shared} {store : Core.Store}
    (related : SharedResources layout handlers shared store) :
    Nonempty (AccountCallCorrespondence.InstalledHandlers (sharedLocations layout) handlers.source
      layout.callHandler layout.dispatcher store) :=
  ⟨⟨handlers.dispatchValue, handlers.handlerValue, handlers.dispatch, handlers.handler, related.2.2, related.2.1⟩⟩

theorem source_eq {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image handlers) world state store) :
    state.external.runtime.runtime.runtime.runtime.runtime.storage.address = handlers.source := by
  have old := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related
    (RuntimeLogEffectsCorrespondence.runtime_related
    (RuntimeAccountEffectsCorrespondence.runtime_related (account_related related))))
  have sourceRead : store.read? layout.storage.address = some (.word handlers.source) := by
    simpa only [prefixRead, layout.below layout.storage.address (by simp [StorageBuiltinCorrespondence.Locations.all]), ↓reduceIte]
      using related.external.2.2.source
  exact Core.Value.word.inj (Option.some.inj (old.address.symm.trans sourceRead))

end Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
