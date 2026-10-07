import Solcore.SourceSemantics.CoreLowering.ProtectedStateAllocationReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationProducer

/-! Actual body origins seed a fixed selected physical frame and its stable
authenticated native token. Reached pool authority provides the current ghost
receipt at each allocation; no ghost-history transport law is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationProducer
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

/-- A body origin supplies its fixed physical owner and stable native
authentication. This seed is independent of reached pools and heap effects. -/
def StableOwner (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program))
    (location : Location) (native : NativeFrame) : Prop :=
  ∃ selected : Fin keys.length, ∃ ghost metadata,
    keys[selected.val].frameLocation = location ∧
    Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata

theorem stableOwner_selected (selected : Fin keys.length)
    {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata) :
    StableOwner keys keys[selected.val].frameLocation native :=
  ⟨selected, ghost, metadata, rfl, stable⟩

theorem readyAt_of_stable_read {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
    (selected : Fin keys.length) {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt (producer headers keys model)
      keys[selected.val].frameLocation native := by
  intro index reached read
  exact ready_of_stable_read reached selected read stable

theorem readyAt_of_owner_eq {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
    (selected : Fin keys.length) {location : Location} {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (physicalOwner : keys[selected.val].frameLocation = location)
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt (producer headers keys model) location native := by
  subst location
  exact readyAt_of_stable_read model selected stable

theorem readyAt_of_stableOwner {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
    {location : Location} {native : NativeFrame} (seed : StableOwner keys location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt (producer headers keys model) location native := by
  obtain ⟨selected, ghost, metadata, physicalOwner, stable⟩ := seed
  exact readyAt_of_owner_eq model selected physicalOwner stable

/-- A read view is a transient Current receipt, so it cannot satisfy the
stable Carries acquisition required by ordinary snapshot production. -/
theorem not_ready_view {index : ProtectedStateTransition.Index} (state : State headers keys index)
    (location : Location) (id target : Word) (caller : Int) :
    ¬ Ready state location (.view id target caller) := by
  intro ready
  obtain ⟨selected, metadata, _physicalOwner, current, stable⟩ := ready
  rw [current] at stable
  cases stable

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationProducer
