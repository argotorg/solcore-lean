import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMarkedAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectCallerProtocol

/-! A successful child keeps its positive payload and cells at its actual post.
The original owned initialized allocator consumes that post once under the
strong model and retains every original capture, environment and reached state.
An actual mapped write separately updates positive cells with the authenticated
replacement payload. Source heap typing and all-row stability belong to those
same returned states. Neither operation infers positive cells from a frame
receipt or converts an erased general-model closure into a positive member. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOriginAllocationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory TypedLexicalControl
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedContextualCellOrigins (CellOrigins PostWithOrigins)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The bridge observes the original full owned pool without changing it. -/
def bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) (protocol headers keys) :=
  CallableIndexedOwnedIndirectCallerProtocol.of_legacy CallableIndexedOwnedCallerProtocol.base

/-- Source admission and positive cells are attached to one actual caller
witness. Its scope and canonical slots remain independent of cell payloads. -/
structure AdmissionWithOrigins (context : SourceSemantics.Context)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {index : ProtectedStateTransition.Index} (reached : State headers keys index) : Prop where
  admission : Admission bridge context reached
  cells : CellOrigins headers keys bodyRegistry registry faults profile
    index.mapping index.world index.heap index.store

section InitializedAllocation
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {globals : Nat} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {source : TypedSource} {context nextContext : SourceSemantics.Context}
  {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {payload : Ty}
  (registered : compiled.indexed.ancestry.layout.frame.Registered compiled.indexed.layouts.definitions)

include registered in
/-- Consume the actual initializer child post and run the original owned
marked allocator once. The original full tuple is retained; admission and
positive cells stay inside its same reached existential. -/
theorem allocate_initialized_from_post
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation compiled.indexed.layouts owner active
      (initializedRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated
      compiled.indexed.ancestry.layout.frame globals
      (compiled.indexed.layouts.allocatorAt owner active onError)
      (initializedRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    {sourceValue : Dynamic.Value} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (reference : canonical[scope.length + 1 + globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body (some sourceValue) location after)
    (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (ready : CallableIndexedOwnedAllocationProducer.Ready initial contextLocation native)
    (post : PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry)
      (faults := faults) bridge context profile binder.scheme.body payload
      (.value sourceValue) (.inRight .word value) initial) :
    ∃ captured,
      CallableIndexedAllocationCompletion.Captures (value :: canonical)
        (initializedRequest source scope binder payload).references scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType scope)
        compiled.indexed.layouts.definitions ∧
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit value]
      let nextWorld := world ++ [compiled.indexed.ancestry.layout.frame.type,
        allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates (value :: actual) store (annotation.expression.rename ξ.lift) nextRef nextStore ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
        nextMap nextWorld administrative ((binder.id, payload) :: scope)
        ((binder.id, location) :: environment) (nextRef :: canonical) compiled.indexed.layouts.definitions ∧
      CellOrigins headers keys bodyRegistry registry faults profile nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift
        (nextRef :: canonical) (nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: value :: actual)
        (OptionalCell.referenceType payload :: payload :: actualContext) compiled.indexed.layouts.definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type contextLocation) ∧
      nextStore.read? contextLocation =
        some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      ∃ reached : State headers keys
          ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
        Relates initial reached ∧
        AdmissionWithOrigins (bodyRegistry := bodyRegistry) (registry := registry)
          (faults := faults) nextContext profile reached := by
  obtain ⟨admitted, valueTyped, represented⟩ := post.at_value
  let producer := (CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))).toOrdinary
  obtain ⟨captured, captures, capturedTyped, evaluated, nextEnvironments, nextCells, nextLocals,
      nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, related, nextAdmission⟩ :=
    CallableIndexedOwnedAdmittedLexicalAllocation.allocate_initialized bridge
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
      rfl registered producer mono extended ordinary allocation annotation same
      valueTyped represented environments post.cells locals agrees actualTyped reference read
      allocated initial ready admitted
  exact ⟨captured, captures, capturedTyped, evaluated, nextEnvironments, nextCells, nextLocals,
    nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, related,
    ⟨nextAdmission, nextCells⟩⟩

end InitializedAllocation

section WrittenAllocationCell
variable {context : SourceSemantics.Context}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before after : Dynamic.Heap} {store : Store} {canonical : Environment}
  {location : Dynamic.Location} {target : Location} {cell : Dynamic.Cell}
  {payload : Ty} {sourceValue : Dynamic.Value} {value : Value}

/-- A true assignment replacement updates the jointly indexed cells. Raw
typing comes from the actual successful RHS post at the retained cell type;
the real write preserves deep heap typing. The owned pool is extended only
after those independent write facts are available, retaining all records. -/
theorem write_initialized_from_post
    (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (post : PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry)
      (faults := faults) bridge context profile cell.type payload
      (.value sourceValue) (.inRight .word value) initial)
    (reference : ReferenceRepresents mapping world location target payload)
    (read : Dynamic.Heap.Reads before location cell)
    (written : Dynamic.Heap.Writes before location (some sourceValue) after) :
    ∃ updated,
      store.write? target (.inRight .unit value) = some updated ∧
      AdministrativePreserved mapping store mapping updated ∧
      ∃ reached : State headers keys ⟨scope, mapping, world, after, updated, canonical⟩,
        Relates initial reached ∧ records reached = records initial ∧
        AdmissionWithOrigins (bodyRegistry := bodyRegistry) (registry := registry)
          (faults := faults) context profile reached := by
  obtain ⟨admitted, valueTyped, represented⟩ := post.at_value
  obtain ⟨updated, nativeWrite, nextCells, preservation⟩ :=
    CallableIndexedOwnedContextualCellOrigins.CellOrigins.write_initialized profile
      post.cells reference read represented written
  have heapTyped := Dynamic.HeapWellTyped.write admitted.heap read (.some valueTyped) written
  have metadata := Dynamic.HeapMetadataExtend.of_write written
  let transport := administrativeTransport headers keys
  let reached := transport.extend initial (LocationMap.Extends.refl mapping)
    (WorldExtends.refl world) preservation metadata
  have nextAdmission : Admission bridge context reached :=
    ⟨heapTyped, StableRows.after_administrative initial reached admitted.rows preservation⟩
  exact ⟨updated, nativeWrite, preservation, reached,
    transport.related initial (LocationMap.Extends.refl mapping) (WorldExtends.refl world)
      preservation metadata,
    transport.records_eq initial (LocationMap.Extends.refl mapping) (WorldExtends.refl world)
      preservation metadata,
    ⟨nextAdmission, nextCells⟩⟩

end WrittenAllocationCell
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOriginAllocationReceipts
