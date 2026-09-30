import Solcore.Core.OptionalCell
import Solcore.Core.Renaming

/-! Source-visible allocations use an artifact-owned nominal marker followed
by an ordinary optional payload cell. A marker's payload records actual lexical
references selected by its compiler capture-layout receipt. Its data identity
indexes the artifact's static allocation metadata.

The allocation expression returns only the payload reference. Marker bindings
stay inside that expression, so the caller's lexical environment is unchanged.
This library does not authenticate arbitrary marker IDs, export source heaps,
or modify any compiler allocation site yet. -/

set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreHeapMarkers
open Core

structure Layout where
  dataType : DataTypeId
  captureType : Ty
  deriving Repr, BEq, DecidableEq

def Layout.type (layout : Layout) : Ty := .namedData layout.dataType
def Layout.definition (layout : Layout) : DataDefinition := ⟨[layout.captureType]⟩
def Layout.constructor (layout : Layout) : ConstructorId := ⟨layout.dataType, 0⟩
def marker (layout : Layout) (captures : Expr) : Expr := .construct layout.constructor captures
def markerValue (layout : Layout) (captures : Value) : Value := .constructed layout.constructor captures

structure Layout.Registered (definitions : DataEnvironment) (layout : Layout) : Prop where
  capturesWellFormed : Ty.WellFormed definitions layout.captureType
  lookup : definitions[layout.dataType.index]? = some layout.definition

theorem Layout.Registered.typeWellFormed {definitions : DataEnvironment} {layout : Layout}
    (registered : layout.Registered definitions) : Ty.WellFormed definitions layout.type :=
  .namedData registered.lookup

theorem Layout.Registered.payloadLookup {definitions : DataEnvironment} {layout : Layout}
    (registered : layout.Registered definitions) :
    definitions.lookupConstructorPayloadType? layout.constructor = some layout.captureType := by
  simp [DataEnvironment.lookupConstructorPayloadType?, DataEnvironment.lookupDataType?,
    Layout.constructor, registered.lookup, Layout.definition]

theorem marker_hasType {definitions : DataEnvironment} {layout : Layout}
    {context : Core.Context} {captures : Expr}
    (registered : layout.Registered definitions)
    (typed : HasType context captures layout.captureType definitions) :
    HasType context (marker layout captures) layout.type definitions :=
  .construct registered.payloadLookup typed

/-- The initializer succeeds before either allocation. The marker captures
the caller's existing lexical references, beneath the temporary result binder. -/
def allocateInitialized (layout : Layout) (payloadType : Ty) (captures initializer : Expr) : Expr :=
  .letE initializer
    (.letE (.newCell layout.type (marker layout (captures.weakenAt 0)))
      (OptionalCell.allocateInitialized payloadType (.var 1)))

def allocate (layout : Layout) (payloadType : Ty) (captures : Expr) : Expr :=
  .letE (.newCell layout.type (marker layout captures)) (OptionalCell.allocate payloadType)

theorem allocateInitialized_hasType {definitions : DataEnvironment} {layout : Layout}
    {context : Core.Context} {payloadType : Ty} {captures initializer : Expr}
    (registered : layout.Registered definitions)
    (capturesTyped : HasType context captures layout.captureType definitions)
    (initializerTyped : HasType context initializer payloadType definitions) :
    HasType context (allocateInitialized layout payloadType captures initializer)
      (OptionalCell.referenceType payloadType) definitions := by
  apply HasType.letE initializerTyped
  apply HasType.letE
    (.newCell (marker_hasType registered
      (by simpa [Context.insertAt] using capturesTyped.weakenAt (inserted := payloadType) 0)))
  exact OptionalCell.allocateInitialized_hasType (.var rfl)

theorem allocate_hasType {definitions : DataEnvironment} {layout : Layout}
    {context : Core.Context} {payloadType : Ty} {captures : Expr}
    (registered : layout.Registered definitions)
    (capturesTyped : HasType context captures layout.captureType definitions)
    (payloadWellFormed : Ty.WellFormed definitions payloadType) :
    HasType context (allocate layout payloadType captures)
      (OptionalCell.referenceType payloadType) definitions :=
  .letE (.newCell (marker_hasType registered capturesTyped))
    (OptionalCell.allocate_hasType payloadWellFormed)

/-- Capture selection is pure. Both cells are appended after initializer
effects, with no allocation or write between the marker and source payload. -/
theorem allocateInitialized_evaluates {layout : Layout} {payloadType : Ty}
    {environment : Environment} {before middle : Store} {captures initializer : Expr}
    {captured payload : Value}
    (initialized : Evaluates environment before initializer payload middle)
    (selected : Evaluates (payload :: environment) middle (captures.weakenAt 0) captured middle) :
    Evaluates environment before (allocateInitialized layout payloadType captures initializer)
      (.cellRef (OptionalCell.cellType payloadType) (middle.length + 1))
      ((middle ++ [markerValue layout captured]) ++ [.inRight .unit payload]) := by
  simpa only [allocateInitialized, marker, markerValue, List.length_append, List.length_singleton] using
    (Evaluates.letE initialized
      (Evaluates.letE (Evaluates.newCell (Evaluates.construct selected))
        (OptionalCell.allocateInitialized_evaluates
          (Evaluates.var (index := 1) (by rfl)))))

theorem allocate_evaluates {layout : Layout} {payloadType : Ty}
    {environment : Environment} {store : Store} {captures : Expr} {captured : Value}
    (selected : Evaluates environment store captures captured store) :
    Evaluates environment store (allocate layout payloadType captures)
      (.cellRef (OptionalCell.cellType payloadType) (store.length + 1))
      ((store ++ [markerValue layout captured]) ++ [.inLeft payloadType .unit]) := by
  simpa only [allocate, marker, markerValue, List.length_append, List.length_singleton] using
    (Evaluates.letE (Evaluates.newCell (Evaluates.construct selected))
      (OptionalCell.allocate_evaluates payloadType
        (.cellRef layout.type store.length :: environment) (store ++ [markerValue layout captured])))

def completedPair (layout : Layout) (store : Store) (index : Nat) : Option (Value × Value) := do
  let .constructed constructor captures ← store[index]? | none
  if constructor = layout.constructor then
    pure (captures, ← store[index + 1]?)
  else none

/-- A partially executed allocation contributes no source cell until its
adjacent payload exists. This is a store observation, not a resume theorem. -/
theorem unfinished_not_completed (layout : Layout) (store : Store) (captured : Value) :
    completedPair layout (store ++ [markerValue layout captured]) store.length = none := by
  simp [completedPair, markerValue]

theorem completed_pair (layout : Layout) (store : Store) (captured payload : Value) :
    completedPair layout ((store ++ [markerValue layout captured]) ++ [payload]) store.length =
      some (captured, payload) := by
  simp [completedPair, markerValue, List.length_append]

theorem prefix_unchanged (store : Store) (layout : Layout) (captured payload : Value) :
    (((store ++ [markerValue layout captured]) ++ [payload]).take store.length) = store := by
  simp [List.append_assoc]

end Solcore.Frontend.SourceCoreHeapMarkers
