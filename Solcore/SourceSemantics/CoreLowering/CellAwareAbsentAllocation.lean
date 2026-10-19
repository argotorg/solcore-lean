import Solcore.SourceSemantics.CoreLowering.ProtectedStateCellAllocation
import Solcore.SourceSemantics.CoreLowering.GenericCellHeapOperations
import Solcore.SourceSemantics.CoreLowering.TypedLexicalControlAllocation

/-! A real uninitialized declaration allocates an absent ordinary cell in the
mixed heap. Earlier generalized descriptors retain their exact stored rows. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareAbsentAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedAllocationCompletion TypedLexicalControl

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {cells : GenericHeap.CellModel definitions}
  (ordinaryCells : GenericHeap.OrdinaryCells model cells)
  {layouts : SourceCoreAllocationLayouts.Prepared}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {source : TypedSource}
  {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol layouts frame
    cells)
  (sameDefinitions : layouts.definitions = definitions)
  (registered : frame.Registered definitions)
  {context nextContext : SourceSemantics.Context}

include ordinaryCells sameDefinitions registered in
theorem allocate_absent {context nextContext : SourceSemantics.Context} {scope : Scope} {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projection : projects binder.scheme.body payload)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    (environments : DataHeap.EnvRepresents (catalog)
      mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location after)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (ready : producer.Ready initial contextLocation native) :
    ∃ captured,
      Captures canonical (absentRequest source scope binder payload).references scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType scope) definitions ∧
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inLeft payload .unit]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates actual store (annotation.expression.rename ξ) nextRef nextStore ∧
      DataHeap.EnvRepresents (catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) definitions ∧
      GenericHeap.CellHeapRepresents cells nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree ξ.lift (nextRef :: canonical) (nextRef :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: actual) (OptionalCell.referenceType payload :: actualContext) definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩ := by
  have referenceAt : canonical[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
      (absentRequest source scope binder payload)]? = some (.cellRef frame.type contextLocation) := by
    have named : SourceCoreCallableIndexedAllocationFrames.isNamedInput (absentRequest source scope binder payload) = false := ordinary
    change canonical[scope.length + (if SourceCoreCallableIndexedAllocationFrames.isNamedInput
      (absentRequest source scope binder payload) then 0 else 1) + globals]? = _
    rw [named]
    exact reference
  obtain ⟨captured, captures, capturedTyped, evaluated, nextHeaps, nextReference, preservation, transition⟩ :=
    producer.complete allocation annotation same sameDefinitions registered environments
      (show EnvironmentsAgree Renaming.id canonical canonical from fun found => found) heaps referenceAt read
      (.absent rfl) (ordinaryCells.inject (.uninitialized projection)) (.ordinary allocated) initial ready
  refine ⟨captured, captures, capturedTyped, CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inl rfl) evaluated agrees,
    CallableIndexedOrdinaryAllocation.bind_environment environments nextReference,
    nextHeaps, (by cases extended; exact .cons allocated.reads_new rfl (.ordinary mono rfl) (locals.mono (.of_allocation allocated))), agrees.lift _,
    .cons (.cellRef nextReference.typed) (actualTyped.weaken ⟨_, rfl⟩), ?_, ?_, preservation, transition⟩
  · have index : ((binder.id, payload) :: scope).length + 1 + globals = (scope.length + 1 + globals) + 1 := by simp; omega
    rw [index]
    exact reference
  · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1).trans read


end Solcore.SourceSemantics.CoreLowering.CellAwareAbsentAllocation
