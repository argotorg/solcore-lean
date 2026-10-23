import Solcore.SourceSemantics.CoreLowering.ProtectedStateCellAllocation
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDescriptorHeap
import Solcore.SourceSemantics.CoreLowering.TypedLexicalControlAllocation

/-! Generalized declarations use the actual marked allocation producer. Their
principal Source descriptor, independent lexical context and real authority
transition are retained together with the native bundle and hidden temporary. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedAllocationCompletion TypedLexicalControl

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel definitions}
  {layouts : SourceCoreAllocationLayouts.Prepared}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {source : TypedSource}
  {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol layouts frame
    (GeneralizedLocalDescriptorHeap.cellModel model instances))
  (sameDefinitions : layouts.definitions = definitions)
  (registered : frame.Registered definitions)
  {context nextContext : SourceSemantics.Context}

include sameDefinitions registered in
theorem allocate_initialized_at_source {allocationSource : TypedSource} {scope : Scope} {binder : TypedBinder} {payload : Ty}
    (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : allocationSource.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest allocationSource scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (initializedRequest allocationSource scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    {function : Dynamic.GeneralizedClosure} {initializer : ExpressionId} {value : Value}
    (sourceCaptures : Dynamic.GeneralizedClosureCaptures context source environment binder initializer function)
    (represented : GeneralizedLocalDescriptorHeap.Stored instances mapping world function value payload)
    (environments : DataHeap.EnvRepresents catalog
      mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model instances) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.AllocatesGeneralized before function location after)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (ready : producer.Ready initial contextLocation native) :
    ∃ captured,
      Captures (value :: canonical) (initializedRequest allocationSource scope binder payload).references scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType scope) definitions ∧
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit value]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates (value :: actual) store (annotation.expression.rename ξ.lift) nextRef nextStore ∧
      DataHeap.EnvRepresents catalog nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) definitions ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model instances) nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift (nextRef :: canonical) (nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: value :: actual)
        (OptionalCell.referenceType payload :: payload :: actualContext) definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩ := by
  have canonicalLayout : EnvironmentsAgree (initializedRequest allocationSource scope binder payload).references canonical (value :: canonical) := fun found => found
  have referenceAt : (value :: canonical)[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
      (initializedRequest allocationSource scope binder payload)]? = some (.cellRef frame.type contextLocation) := by
    have named : SourceCoreCallableIndexedAllocationFrames.isNamedInput (initializedRequest allocationSource scope binder payload) = false := ordinary
    change (value :: canonical)[Renaming.comp (Renaming.insertion 0) Renaming.id
      (scope.length + (if SourceCoreCallableIndexedAllocationFrames.isNamedInput (initializedRequest allocationSource scope binder payload) then 0 else 1) + globals)]? = _
    rw [named]
    exact reference
  obtain ⟨captured, captures, capturedTyped, evaluated, nextHeaps, nextReference, preservation, transition⟩ :=
    producer.complete allocation annotation same sameDefinitions registered environments
      canonicalLayout heaps referenceAt read (.initialized rfl rfl) (.generalized represented) (.generalized allocated) initial ready
  have nextLocals : Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) := by
    cases extended
    exact .cons allocated.reads_new
      (congrArg (fun retained : TypedBinder => retained.scheme.body) sourceCaptures.binder_eq)
      (.generalized rfl (congrArg TypedBinder.id sourceCaptures.binder_eq)
        (congrArg TypedBinder.scheme sourceCaptures.binder_eq))
      (locals.mono (.of_generalized_allocation allocated))
  have inserted : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical (value :: actual) := fun found => agrees found
  refine ⟨captured, captures, capturedTyped, CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inr rfl) evaluated (agrees.lift value),
    CallableIndexedOrdinaryAllocation.bind_environment environments nextReference, nextHeaps, nextLocals, inserted.lift _,
    .cons (.cellRef nextReference.typed) (.cons (represented.runtime_hasType.weaken ⟨_, rfl⟩) (actualTyped.weaken ⟨_, rfl⟩)), ?_, ?_, preservation, transition⟩
  · have index : ((binder.id, payload) :: scope).length + 1 + globals = (scope.length + 1 + globals) + 1 := by simp; omega
    rw [index]
    exact reference
  · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1).trans read

/- Compatibility wrapper using the semantic source for the allocation request. -/
include sameDefinitions registered in
theorem allocate_initialized {scope : Scope} {binder : TypedBinder} {payload : Ty}
    (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (initializedRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    {function : Dynamic.GeneralizedClosure} {initializer : ExpressionId} {value : Value}
    (sourceCaptures : Dynamic.GeneralizedClosureCaptures context source environment binder initializer function)
    (represented : GeneralizedLocalDescriptorHeap.Stored instances mapping world function value payload)
    (environments : DataHeap.EnvRepresents catalog
      mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model instances) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.AllocatesGeneralized before function location after)
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
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model instances) nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift (nextRef :: canonical) (nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: value :: actual)
        (OptionalCell.referenceType payload :: payload :: actualContext) definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩ := by
  exact allocate_initialized_at_source (allocationSource := source) producer sameDefinitions registered extended ordinary
    allocation annotation same sourceCaptures represented environments heaps locals agrees actualTyped reference read allocated initial ready

end Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedAllocation
