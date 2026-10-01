import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCallMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOrdinaryAllocation

/-! Protected named observations survive lexical source binders and the actual
three-cell marked allocation. Only the caller variable position changes when a
binder is prepended; installed closure code/captures and frame authority stay
exact. These receipts contain no source/native body execution premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedExpressionMeaning
open Core Frontend SourceInference GeneralHeap

/-- A source-visible binder changes the canonical lexical environment, unlike
hidden evaluation slots tracked solely by the expression renaming. -/
structure Binds (entry : Entry) : Prop where
  prepend : ∀ {scope mapping world before store canonical id type value},
    entry scope mapping world before store canonical →
    entry ((id, type) :: scope) mapping world before store (value :: canonical)
  restore : ∀ {scope mapping world before store canonical id type value},
    entry ((id, type) :: scope) mapping world before store (value :: canonical) →
    entry scope mapping world before store canonical

end Solcore.SourceSemantics.CoreLowering.ProtectedExpressionMeaning

namespace Solcore.SourceSemantics.CoreLowering.NamedCallExpressions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableAncestryPairedLookup
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}

/-- This is a caller lookup shift. The installed native closure environment,
body template, reads and current/snapshot histories remain unchanged. -/
def prepend_installed (functions : FunctionModel values.checked.catalog ambient)
    {body : BuiltinNamedCalls.Body prepared values ambient.definitions program}
    {registry mapping world before store canonical} (value : Value)
    (installed : BuiltinNamedCalls.Installed functions body registry mapping world before store canonical) :
    BuiltinNamedCalls.Installed functions body registry mapping world before store (value :: canonical) :=
  { installed with
    globalIndex := installed.globalIndex + 1
    globalReference := by simpa using installed.globalReference }

theorem entry_binds (functions : FunctionModel values.checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry)
    (bodies : Bodies prepared values ambient.definitions program) (administrativePrefix : Nat) :
    ProtectedExpressionMeaning.Binds (Entry functions registry bodies administrativePrefix) := by
  constructor
  · intro scope mapping world before store canonical id type value entry body member
    obtain ⟨observed, located⟩ := entry body member
    refine ⟨prepend_installed functions value observed, ?_⟩
    change observed.globalIndex + 1 = _
    rw [located]
    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  · intro scope mapping world before store canonical id type value entry body member
    obtain ⟨observed, located⟩ := entry body member
    have shifted : observed.globalIndex = (scope.length + administrativePrefix + body.slot) + 1 := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using located
    refine ⟨{ observed with
      globalIndex := scope.length + administrativePrefix + body.slot
      globalReference := by simpa only [shifted, List.getElem?_cons_succ] using observed.globalReference }, rfl⟩

/-- An actual marked allocation transports the real installed cells through
world/map growth and protected writes, then prepends only the payload reference.
Snapshot and marker references are never promoted to source binders. -/
theorem entry_after_marked (functions : FunctionModel values.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry}
    {bodies : Bodies prepared values ambient.definitions program} {administrativePrefix : Nat}
    {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {store : Store} {canonical : Environment}
    {id : Resolved.LocalId} {payloadType snapshotType markerType : Ty}
    {snapshot marker payload : Value} {sourceType : TypeSystem.Ty}
    {sourceValue : Option Dynamic.Value} {sourceLocation : Dynamic.Location}
    (entry : Entry functions registry bodies administrativePrefix scope mapping world before store canonical)
    (allocated : Dynamic.Heap.Allocates before sourceType sourceValue sourceLocation after)
    (preserved : AdministrativePreserved mapping store (mapping ++ [store.length + 2])
      (store ++ [snapshot, marker, payload])) :
    Entry functions registry bodies administrativePrefix ((id, payloadType) :: scope)
      (mapping ++ [store.length + 2]) (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType])
      after (store ++ [snapshot, marker, payload])
      (.cellRef (OptionalCell.cellType payloadType) (store.length + 2) :: canonical) :=
  (entry_binds functions registry bodies administrativePrefix).prepend
    ((entry_transport functions registry bodies administrativePrefix).extend entry ⟨_, rfl⟩ ⟨_, rfl⟩
      preserved (Dynamic.HeapMetadataExtend.of_allocation allocated))

/-- The ordinary allocation theorem supplies the protection premise from the
real allocator expression and independent source allocation. Captures are
obtained from actual lexical references and retained exactly in the marker. -/
theorem marked_bind
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {bodies : Bodies prepared values ambient.definitions program} {administrativePrefix : Nat}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : SourceCoreSourceCells.Request}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals allocate request)
    (same : annotation.original = allocation.expression)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {contextLocation : Location}
    {native : CallableIndexedHistory.NativeFrame}
    {payload : Option Value} {sourceValue : Option Dynamic.Value} {sourceLocation : Dynamic.Location}
    (entry : Entry functions registry bodies administrativePrefix request.scope mapping world before store canonical)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative request.scope environment canonical ambient.definitions)
    (agrees : EnvironmentsAgree request.references canonical actual)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (payloadAt : CallableIndexedAllocationCompletion.PayloadAt request actual payload)
    (cell : GenericHeap.CellRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world ⟨request.binder.scheme.body, sourceValue, none⟩
      (CallableIndexedAllocationCompletion.optionalValue request.payloadType payload) request.payloadType)
    (allocated : Dynamic.Heap.Allocates before request.binder.scheme.body sourceValue sourceLocation after) :
    ∃ captured,
      Evaluates actual store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload]) ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions
        (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        after (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload]) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
        (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType]) administrative
        ((request.binder.id, request.payloadType) :: request.scope) ((request.binder.id, sourceLocation) :: environment)
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2) :: canonical) ambient.definitions ∧
      Entry functions registry bodies administrativePrefix ((request.binder.id, request.payloadType) :: request.scope)
        (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        after (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload])
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2) :: canonical) := by
  obtain ⟨captured, evaluated, finalHeaps, mapped, preservation⟩ :=
    CallableIndexedOrdinaryAllocation.preserves allocation annotation same definitions registered environments agrees heaps
      reference read payloadAt cell allocated
  exact ⟨captured, evaluated, finalHeaps, CallableIndexedOrdinaryAllocation.bind_environment environments mapped,
    entry_after_marked functions entry allocated preservation⟩

end Solcore.SourceSemantics.CoreLowering.NamedCallExpressions

namespace Solcore.SourceSemantics.CoreLowering.ProtectedExpressionMeaning
open Core Frontend SourceInference GeneralHeap

/-- Actual hidden slots are typed from the original actual environment and
the newly allocated mapped payload reference. Canonical source EnvRep alone
is not used to infer their types. -/
theorem marked_actual_types {definitions : DataEnvironment} {mapping : LocationMap} {world : StoreTyping}
    {store : Store} {sourceLocation : Dynamic.Location} {snapshotType markerType payloadType : Ty}
    {actual : Environment} {actualContext : Core.Context}
    (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (reference : ReferenceRepresents (mapping ++ [store.length + 2])
      (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType])
      sourceLocation (store.length + 2) payloadType) :
    RuntimeEnvironmentHasTypes (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType])
      (.cellRef (OptionalCell.cellType payloadType) (store.length + 2) :: actual)
      (OptionalCell.referenceType payloadType :: actualContext) definitions :=
  .cons (.cellRef reference.typed) (typed.weaken ⟨_, rfl⟩)

end Solcore.SourceSemantics.CoreLowering.ProtectedExpressionMeaning
