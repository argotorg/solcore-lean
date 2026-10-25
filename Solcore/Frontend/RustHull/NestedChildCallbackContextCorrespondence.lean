import Solcore.Frontend.RustHull.ChildCallbackContextCorrespondence
import Solcore.Frontend.RustHull.RuntimeInstalledCallbacksCorrespondence

/-! Nested children retain the actual dispatcher cell as well as the shared
ambient and creator references. Refreshing a capture changes its store witness
and shared values, while retaining the same compiled closure and code references. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.NestedChildCallbackContextCorrespondence
open Core Correspondence ScalarExecution
open RuntimeCallEffectsCorrespondence (Layout)

structure Inventory (layout : Layout) (cells : List InitializedCell) (creator : Nat) : Prop
    extends base : ChildCallbackContextCorrespondence.Inventory layout cells creator where
  dispatcherSeparate : ∀ cell ∈ cells, cell.location ≠ layout.dispatcher
  creatorDispatcher : creator ≠ layout.dispatcher

def context {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    (inventory : Inventory layout cells creator) (dispatcher : Value) :
    RuntimeChildCallEffectsCorrespondence.Context layout where
  valid read := (ChildCallbackContextCorrespondence.context inventory.base).valid read ∧
    read layout.dispatcher = some (.inRight .unit dispatcher)
  frame := by
    intro before after retained valid
    refine ⟨(ChildCallbackContextCorrespondence.context inventory.base).frame retained valid.1, ?_⟩
    rw [retained _ (RuntimeCallEffectsCorrespondence.call_separation layout _ (by simp))]
    exact valid.2

theorem initial {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    (inventory : Inventory layout cells creator) {store : Store} {dispatcher : Value}
    (captured : (ChildCallbackContextCorrespondence.context inventory.base).valid (prefixRead layout.boundary store))
    (found : store.read? layout.dispatcher = some (.inRight .unit dispatcher)) :
    (context inventory dispatcher).valid (prefixRead layout.boundary store) := by
  refine ⟨captured, ?_⟩
  simpa only [prefixRead, layout.dispatcherBelow, ↓reduceIte] using found

theorem dispatcher_read {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    {inventory : Inventory layout cells creator} {store : Store} {dispatcher : Value}
    (valid : (context inventory dispatcher).valid (prefixRead layout.boundary store)) :
    store.read? layout.dispatcher = some (.inRight .unit dispatcher) := by
  simpa only [prefixRead, layout.dispatcherBelow, ↓reduceIte] using valid.2

def refreshCapture {slots : List (String × Core.Ty)} {count : Nat}
    {images : List (Nat × List UInt8)} {catalog : List AccountRuntime.CodeDefinition}
    {functions : List Value} {cells : List InitializedCell} {dispatcher creator : Nat} {initial : Store}
    (capture : ObjectCallbackCapture slots count images catalog functions cells dispatcher creator initial)
    (store : Store) (found : store.read? dispatcher = some (.inRight .unit capture.closure)) :
    ObjectCallbackCapture slots count images catalog functions (ChildFrameCorrespondence.refresh store cells)
      dispatcher creator store where
  depth := capture.depth
  environment := capture.environment
  functions := capture.functions
  shared := capture.shared
  dispatcher := capture.dispatcher
  creator := capture.creator
  functionValues := capture.functionValues
  names := by
    simpa only [ChildFrameCorrespondence.refresh, List.map_map, Function.comp_def,
      ChildFrameCorrespondence.refreshCell] using capture.names
  references := ChildFrameCorrespondence.refresh_references capture.references store
  dispatcherValue := capture.dispatcherValue
  creatorValue := capture.creatorValue
  closure := capture.closure
  captured := capture.captured
  stored := found

def withDispatcher {slots : List (String × Core.Ty)} {count : Nat}
    {images : List (Nat × List UInt8)} {catalog : List AccountRuntime.CodeDefinition}
    {functions : List Value} {cells : List InitializedCell} {dispatcher creator : Nat} {store : Store}
    (capture : ObjectCallbackCapture slots count images catalog functions cells dispatcher creator store)
    (location : Nat) (same : location = dispatcher) :
    ObjectCallbackCapture slots count images catalog functions cells location creator store where
  depth := capture.depth
  environment := capture.environment
  functions := capture.functions
  shared := capture.shared
  dispatcher := capture.dispatcher
  creator := capture.creator
  functionValues := capture.functionValues
  names := capture.names
  references := capture.references
  dispatcherValue := by simpa only [same] using capture.dispatcherValue
  creatorValue := capture.creatorValue
  closure := capture.closure
  captured := capture.captured
  stored := by simpa only [same] using capture.stored

end Solcore.Frontend.RustHull.NestedChildCallbackContextCorrespondence
