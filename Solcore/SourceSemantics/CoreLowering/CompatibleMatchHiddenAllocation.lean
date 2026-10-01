import Solcore.SourceSemantics.CoreLowering.CompatibleMatchCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmPrefix

/-! The hidden scrutinee is an internal scope reference, never a source lexical
binder. Its independent source cell retains the complete scrutinee type even
when the real marker key uses the compiler's erased runtime binder type. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchHiddenAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedAllocationCompletion

def request (source : TypedSource) (scope : SourceCoreSourceCells.Scope)
    (binder : TypedBinder) (payload : Ty) : SourceCoreSourceCells.Request :=
  CompatibleStatementInitialized.request source scope binder payload

/-- The erased marker metadata does not retype the independent hidden heap
cell. Actual captures and payloads still come from their real typed slots. -/
theorem preserves {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {scope : SourceCoreSourceCells.Scope} {binder : TypedBinder} {payload : Ty}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (request source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (request source scope binder payload))
    (same : annotation.original = allocation.expression)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (fresh : scope.any (fun binding => decide (binding.1 = binder.id)) = false)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (definitionsEq : layouts.definitions = definitions) (registered : frame.Registered definitions)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {before after : Dynamic.Heap} {store : Store} {sourceType : TypeSystem.Ty}
    {sourceValue : Dynamic.Value} {value : Value} {location : Dynamic.Location}
    {contextLocation : Location} {native : NativeFrame}
    (represented : model.Represents mapping world sourceType sourceValue value payload)
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before sourceType (some sourceValue) location after) :
    ∃ captured,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit value]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates (value :: actual) store (annotation.expression.rename ξ.lift) nextRef nextStore ∧
      DataHeap.EnvRepresents catalog nextMap nextWorld administrative ((binder.id, payload) :: scope)
        environment (nextRef :: canonical) definitions ∧
      GenericHeap.HeapRepresents model nextMap nextWorld after nextStore ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      nextStore.read? (store.length + 2) = some (.inRight .unit value) := by
  have canonicalLayout : EnvironmentsAgree (request source scope binder payload).references canonical (value :: canonical) :=
    fun found => found
  have referenceAt : (value :: canonical)[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
      (request source scope binder payload)]? = some (.cellRef frame.type contextLocation) := by
    have kind : SourceCoreCallableIndexedAllocationFrames.isNamedInput (request source scope binder payload) = false := ordinary
    simp only [SourceCoreCallableIndexedAllocationFrames.referenceIndex, kind]
    exact canonicalLayout reference
  obtain ⟨captured, selected, typed⟩ := CallableIndexedOrdinaryAllocation.captures_typed environments canonicalLayout
  have captureType : allocation.entry.layout.captureType = SourceCoreSourceCells.captureType scope := by
    change SourceCoreSourceCells.captureType allocation.entry.key.scope = SourceCoreSourceCells.captureType scope
    rw [allocation.keyExact]
    rfl
  have markerTyped : RuntimeValueHasType world (SourceCoreHeapMarkers.markerValue allocation.entry.layout captured)
      allocation.entry.layout.type definitions :=
    .constructed (definitionsEq ▸ allocation.registered).payloadLookup (captureType.symm ▸ typed)
  obtain ⟨nextHeaps, nextReference⟩ := CallableIndexedOrdinaryAllocation.heap_allocate heaps
    (SourceCoreCallableIndexedFrames.encode_runtime_typed world registered native) markerTyped
    (GenericHeap.CellRepresents.initialized represented) allocated
  have evaluated := CallableIndexedAllocationCompletion.evaluates allocation annotation same referenceAt read
    selected (PayloadAt.initialized rfl rfl)
  refine ⟨captured, CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inr rfl)
    evaluated (agrees.lift value),
    .internal nextReference (environments.fresh_absent fresh) (environments.extend ⟨_, rfl⟩ ⟨_, rfl⟩),
    nextHeaps, allocation_frame _ _ _ _ _, ?_⟩
  simp [Store.read?]

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchHiddenAllocation
