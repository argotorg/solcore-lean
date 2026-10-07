import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission
import Solcore.SourceSemantics.CoreLowering.TypedLexicalControlAllocation

/-! Real Source allocation and the actual marked allocator post provide the
next lexical admission. The original raw value typing is independent of native
ValueRep. Every captured value, environment, heap, effect and state relation
comes from the existing producer unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion TypedLexicalControl
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

/-- Only the genuine Source allocation and raw optional value type establish
deep typing of the new heap. Actual administrative effects retain all rows. -/
theorem after_allocation {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    {source : TypedSource} {context nextContext : SourceSemantics.Context} {binder : TypedBinder}
    {location : Dynamic.Location} {value : Option Dynamic.Value}
    (admitted : Admission bridge context first)
    (extended : BinderExtends source.owner context binder nextContext)
    (valueTyped : Dynamic.OptionalValueHasType context initial.heap value binder.scheme.body)
    (allocated : Dynamic.Heap.Allocates initial.heap binder.scheme.body value location reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    Admission bridge nextContext last :=
  ⟨(Dynamic.HeapWellTyped.iff_of_binderExtends extended).mp
      (Dynamic.HeapWellTyped.allocate admitted.heap valueTyped allocated),
    StableRows.after_administrative (bridge.pool first) (bridge.pool last) admitted.rows frame⟩

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {source : TypedSource}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (definitions : layouts.definitions = (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (registered : frame.Registered (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (producer : ProtectedStateTransition.OrdinaryAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))

include definitions registered in
/-- The absent binder retains the actual producer state and complete capture,
then establishes admission for that same post in its genuine next Source context. -/
theorem allocate_absent {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projection : compiled.compatible.checked.catalog.project binder.scheme.body = .ok payload)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location after)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (ready : producer.Ready initial contextLocation native)
    (admitted : Admission bridge context initial) :
    ∃ captured,
      Captures canonical (absentRequest source scope binder payload).references scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType scope) (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inLeft payload .unit]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates actual store (annotation.expression.rename ξ) nextRef nextStore ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree ξ.lift (nextRef :: canonical) (nextRef :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: actual) (OptionalCell.referenceType payload :: actualContext) (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      ∃ reached : callerProtocol.State
          ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge nextContext reached := by
  obtain ⟨captured, captures, capturedTyped, evaluated, nextEnvironments, nextHeaps, nextLocals,
      nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, related⟩ :=
    TypedLexicalControl.Stateful.allocate_absent (values := .initial compiled.compatible.checked)
      functions definitions registered callerProtocol producer mono extended ordinary projection allocation annotation same
      environments heaps locals agrees actualTyped reference read allocated initial ready
  exact ⟨captured, captures, capturedTyped, evaluated, nextEnvironments, nextHeaps, nextLocals,
    nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, related,
    after_allocation bridge initial reached admitted extended (.none _) allocated preservation⟩

include definitions registered in
/-- The actual successful initializer post supplies genuine raw value typing.
The existing initialized allocator produces the next state verbatim. -/
theorem allocate_initialized {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (initializedRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    {sourceValue : Dynamic.Value} {value : Value}
    (valueTyped : Dynamic.ValueHasType context before sourceValue binder.scheme.body)
    (represented : ValueRep compiled.compatible.checked registry functions mapping world binder.scheme.body sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body (some sourceValue) location after)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (ready : producer.Ready initial contextLocation native)
    (admitted : Admission bridge context initial) :
    ∃ captured,
      Captures (value :: canonical) (initializedRequest source scope binder payload).references scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType scope) (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit value]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates (value :: actual) store (annotation.expression.rename ξ.lift) nextRef nextStore ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift (nextRef :: canonical) (nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: value :: actual)
        (OptionalCell.referenceType payload :: payload :: actualContext) (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      ∃ reached : callerProtocol.State
          ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge nextContext reached := by
  obtain ⟨captured, captures, capturedTyped, evaluated, nextEnvironments, nextHeaps, nextLocals,
      nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, related⟩ :=
    TypedLexicalControl.Stateful.allocate_initialized (values := .initial compiled.compatible.checked)
      functions definitions registered callerProtocol producer mono extended ordinary allocation annotation same represented
      environments heaps locals agrees actualTyped reference read allocated initial ready
  exact ⟨captured, captures, capturedTyped, evaluated, nextEnvironments, nextHeaps, nextLocals,
    nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, related,
    after_allocation bridge initial reached admitted extended (.some valueTyped) allocated preservation⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation
