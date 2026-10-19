import Solcore.SourceSemantics.CoreLowering.ProtectedStateCellAllocation
import Solcore.SourceSemantics.CoreLowering.GenericCellHeapOperations
import Solcore.SourceSemantics.CoreLowering.TypedLexicalControlAllocation

/-! Ordinary initialized declarations use the actual marked allocation producer
in a mixed heap. The successful initializer value is allocated at its reached
state, preserving every existing descriptor and the real caller transition. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryAllocation
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
theorem allocate_initialized {scope : Scope} {binder : TypedBinder} {payload : Ty}
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
    (represented : model.Represents mapping world binder.scheme.body sourceValue value payload)
    (environments : DataHeap.EnvRepresents catalog
      mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body (some sourceValue) location after)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (ready : producer.Ready initial contextLocation native) :
    ∃ captured,
      Captures (value :: canonical) (initializedRequest source scope binder payload).references scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType scope) definitions ∧
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit value]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates (value :: actual) store (annotation.expression.rename ξ.lift) nextRef nextStore ∧
      DataHeap.EnvRepresents catalog nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) definitions ∧
      GenericHeap.CellHeapRepresents cells nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift (nextRef :: canonical) (nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: value :: actual)
        (OptionalCell.referenceType payload :: payload :: actualContext) definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩ := by
  have canonicalLayout : EnvironmentsAgree (initializedRequest source scope binder payload).references canonical (value :: canonical) := fun found => found
  have referenceAt : (value :: canonical)[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
      (initializedRequest source scope binder payload)]? = some (.cellRef frame.type contextLocation) := by
    have named : SourceCoreCallableIndexedAllocationFrames.isNamedInput (initializedRequest source scope binder payload) = false := ordinary
    change (value :: canonical)[Renaming.comp (Renaming.insertion 0) Renaming.id
      (scope.length + (if SourceCoreCallableIndexedAllocationFrames.isNamedInput (initializedRequest source scope binder payload) then 0 else 1) + globals)]? = _
    rw [named]
    exact reference
  obtain ⟨captured, captures, capturedTyped, evaluated, nextHeaps, nextReference, preservation, transition⟩ :=
    producer.complete allocation annotation same sameDefinitions registered environments
      canonicalLayout heaps referenceAt read (.initialized rfl rfl) (ordinaryCells.inject (.initialized represented)) (.ordinary allocated) initial ready
  have nextLocals : Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) := by
    cases extended
    exact .cons allocated.reads_new rfl (.ordinary mono rfl) (locals.mono (.of_allocation allocated))
  have inserted : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical (value :: actual) := fun found => agrees found
  refine ⟨captured, captures, capturedTyped, CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inr rfl) evaluated (agrees.lift value),
    CallableIndexedOrdinaryAllocation.bind_environment environments nextReference, nextHeaps, nextLocals, inserted.lift _,
    .cons (.cellRef nextReference.typed) (.cons ((model.runtime_hasType represented).weaken ⟨_, rfl⟩) (actualTyped.weaken ⟨_, rfl⟩)), ?_, ?_, preservation, transition⟩
  · have index : ((binder.id, payload) :: scope).length + 1 + globals = (scope.length + 1 + globals) + 1 := by simp; omega
    rw [index]
    exact reference
  · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1).trans read

end Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryAllocation
