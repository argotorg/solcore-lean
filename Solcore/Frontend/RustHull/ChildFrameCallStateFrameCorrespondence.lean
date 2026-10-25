import Solcore.Frontend.RustHull.ChildFrameCallAllocationCorrespondence
import Solcore.Frontend.RustHull.ChildFrameStateFrameCorrespondence
import Solcore.Frontend.RustHull.NestedChildCallbackContextCorrespondence

/-! A callable child preserves its parent's local cells. Its final shared
resources include changes made by nested calls and retain exact catalog links. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildFrameCorrespondence
open Core Correspondence ScalarExecution

/-- The same concrete inventory also records dispatcher separation for the
next child allocation. -/
theorem CallAllocationReady.nestedInventory {sharedCells cells : List InitializedCell} {store : Store}
    {parent : RuntimeCallEffectsSemantics.State} {request : AccountCallSemantics.Request}
    {shared : AccountCallSemantics.Shared} {bytes : List UInt8}
    {dispatcher creator : Nat} {dispatchValue : Value}
    (ready : CallAllocationReady sharedCells cells store parent request shared bytes dispatcher creator dispatchValue)
    (dispatcherSeparate : ∀ cell ∈ sharedCells, cell.location ≠ dispatcher)
    (creatorDispatcher : creator ≠ dispatcher) :
    NestedChildCallbackContextCorrespondence.Inventory ready.call.layout sharedCells creator where
  base := ready.inventory
  dispatcherSeparate := by simpa only [ready.call.dispatcherEqual] using dispatcherSeparate
  creatorDispatcher := by simpa only [ready.call.dispatcherEqual] using creatorDispatcher

theorem CallAllocationReady.nestedCaptured {sharedCells cells : List InitializedCell} {store : Store}
    {parent : RuntimeCallEffectsSemantics.State} {request : AccountCallSemantics.Request}
    {shared : AccountCallSemantics.Shared} {bytes : List UInt8}
    {dispatcher creator : Nat} {dispatchValue : Value}
    (ready : CallAllocationReady sharedCells cells store parent request shared bytes dispatcher creator dispatchValue)
    (dispatcherSeparate : ∀ cell ∈ sharedCells, cell.location ≠ dispatcher)
    (creatorDispatcher : creator ≠ dispatcher) :
    (NestedChildCallbackContextCorrespondence.context
      (ready.nestedInventory dispatcherSeparate creatorDispatcher) dispatchValue).valid
      (prefixRead ready.call.layout.boundary store) := by
  apply NestedChildCallbackContextCorrespondence.initial _ ready.captured
  simpa only [ready.call.dispatcherEqual] using ready.dispatcherRead

/-- Below the initial child boundary, balances and the old mutable cells are
all shared. Fresh child memory, return data and termination cells stay local. -/
theorem CallAllocationReady.mutable_early_shared {sharedCells cells : List InitializedCell}
    {initial allocated : Store} {parent : RuntimeCallEffectsSemantics.State}
    {request : AccountCallSemantics.Request} {shared : AccountCallSemantics.Shared} {bytes : List UInt8}
    {dispatcher creator : Nat} {dispatchValue : Value}
    (ready : CallAllocationReady sharedCells cells allocated parent request shared bytes dispatcher creator dispatchValue)
    (origins : ∀ cell ∈ cells, cell.location < initial.length → cell ∈ sharedCells ∨ cell.name = "createHandler")
    {location : Nat} (below : location < initial.length)
    (member : location ∈ RuntimeCallEffectsCorrespondence.mutable ready.call.layout) :
    location ∈ (RuntimeCallEffectsCorrespondence.sharedLocations ready.call.layout).mutable := by
  change location ∈ ready.call.layout.balances :: mutable ready.call.layout.toReturnDataLayout at member
  rcases List.mem_cons.mp member with same | member
  · simp [same, RuntimeCallEffectsCorrespondence.sharedLocations, AccountCallCorrespondence.SharedLocations.mutable]
  · have present : location ∈ mutable ready.base.layout := by
      simpa only [ready.call.baseEqual] using member
    have shared := ChildFrameCorrespondence.mutable_early_shared ready.base ready.inventory.signature origins below present
    change location ∈ (sharedLocations ready.call.layout.toReturnDataLayout).mutable
    simpa only [ready.call.baseEqual] using shared

/-- Calls made by the child may update balances; all older nonshared reads
still agree with the store from before the child frame was allocated. -/
theorem CallAllocationReady.parent_frame {sharedCells cells : List InitializedCell}
    {initial suffix final : Store} {parent : RuntimeCallEffectsSemantics.State}
    {request : AccountCallSemantics.Request} {shared : AccountCallSemantics.Shared} {bytes : List UInt8}
    {dispatcher creator : Nat} {dispatchValue : Value}
    (ready : CallAllocationReady sharedCells cells (initial ++ suffix) parent request shared bytes dispatcher creator dispatchValue)
    (origins : ∀ cell ∈ cells, cell.location < initial.length → cell ∈ sharedCells ∨ cell.name = "createHandler")
    {handlers : RuntimeCallEffectsCorrespondence.Handlers ready.call.layout}
    {anchors : RuntimeChildCallEffectsCorrespondence.Anchors}
    {context : RuntimeChildCallEffectsCorrespondence.Context ready.call.layout}
    {world : World} {next : Semantics.State RuntimeCallEffectsSemantics.State}
    (related : StateRel (RuntimeChildCallEffectsCorrespondence.model ready.call.layout
      (prefixRead ready.call.layout.boundary (initial ++ suffix)) (cells.map InitializedCell.effectSlot)
      (some bytes) handlers anchors context) world next final) :
    AccountCallCorrespondence.SharedFrame (RuntimeCallEffectsCorrespondence.sharedLocations ready.call.layout) initial final := by
  have boundary : ready.call.layout.boundary = (initial ++ suffix).length := by
    change ready.call.layout.toReturnDataLayout.boundary = _
    rw [ready.call.baseEqual]
    exact ready.base.boundary
  have base := RuntimeChildCallEffectsCorrespondence.base_related related
  refine ⟨?_, ?_⟩
  · have bounded := base.external.1
    rw [boundary] at bounded
    exact Nat.le_trans (by simp) bounded
  · intro location value outside found
    have below : location < initial.length := (List.getElem?_eq_some_iff.mp found).1
    have beforeBoundary : location < ready.call.layout.boundary := by
      rw [boundary]
      exact Nat.lt_of_lt_of_le below (by simp)
    have preserved := RuntimeCallEffectsCorrespondence.other_related base
      (fun member => outside (ready.mutable_early_shared origins below member))
    have same : final.read? location = initial.read? location := by
      simpa only [prefixRead, beforeBoundary, ↓reduceIte, Core.Store.read?, List.getElem?_append_left below] using preserved
    exact same.trans found

theorem CallAllocationReady.shared_state {sharedCells cells : List InitializedCell} {initial final : Store}
    {parent : RuntimeCallEffectsSemantics.State} {request : AccountCallSemantics.Request}
    {shared : AccountCallSemantics.Shared} {bytes : List UInt8}
    {dispatcher creator : Nat} {dispatchValue : Value}
    (ready : CallAllocationReady sharedCells cells initial parent request shared bytes dispatcher creator dispatchValue)
    {handlers : RuntimeCallEffectsCorrespondence.Handlers ready.call.layout}
    {anchors : RuntimeChildCallEffectsCorrespondence.Anchors}
    {context : RuntimeChildCallEffectsCorrespondence.Context ready.call.layout}
    {world : World} {next : Semantics.State RuntimeCallEffectsSemantics.State}
    (related : StateRel (RuntimeChildCallEffectsCorrespondence.model ready.call.layout
      (prefixRead ready.call.layout.boundary initial) (cells.map InitializedCell.effectSlot)
      (some bytes) handlers anchors context) world next final) :
    AccountCallCorrespondence.SharedStateRel (RuntimeCallEffectsCorrespondence.sharedLocations ready.call.layout)
      (RuntimeCallEffectsSemantics.shared next.external) final :=
  RuntimeCallEffectsCorrespondence.shared_related (RuntimeChildCallEffectsCorrespondence.base_related related)

theorem CallAllocationReady.linked_shared_state {sharedCells cells : List InitializedCell} {initial final : Store}
    {parent : RuntimeCallEffectsSemantics.State} {request : AccountCallSemantics.Request}
    {shared : AccountCallSemantics.Shared} {bytes : List UInt8}
    {dispatcher creator : Nat} {dispatchValue : Value}
    (ready : CallAllocationReady sharedCells cells initial parent request shared bytes dispatcher creator dispatchValue)
    {handlers : RuntimeCallEffectsCorrespondence.Handlers ready.call.layout}
    {anchors : RuntimeChildCallEffectsCorrespondence.Anchors}
    {context : RuntimeChildCallEffectsCorrespondence.Context ready.call.layout}
    {world : World} {next : Semantics.State RuntimeCallEffectsSemantics.State}
    (related : StateRel (RuntimeChildCallEffectsCorrespondence.model ready.call.layout
      (prefixRead ready.call.layout.boundary initial) (cells.map InitializedCell.effectSlot)
      (some bytes) handlers anchors context) world next final) :
    AccountCallCorrespondence.LinkedSharedStateRel anchors (RuntimeCallEffectsCorrespondence.sharedLocations ready.call.layout)
      (RuntimeCallEffectsSemantics.shared next.external) final :=
  ⟨ready.shared_state related, RuntimeChildCallEffectsCorrespondence.linked_related related⟩

end Solcore.Frontend.RustHull.ChildFrameCorrespondence
