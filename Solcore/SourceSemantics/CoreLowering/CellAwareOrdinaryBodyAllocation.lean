import Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryAllocation
import Solcore.SourceSemantics.CoreLowering.CellAwareAbsentAllocation
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeAuthority

/-! Ordinary materialized bodies use the real marked allocator in a mixed heap.
Its constant administrative witness is constructed here; callers supply no
allocation readiness law or body execution premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodyAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedAllocationCompletion
open ProtectedStateTransition

private def protocol : Protocol Unit where
  State _ := Unit
  records _ := ()
  Relates _ _ := True
  refl _ := trivial
  trans _ _ := trivial

private def transport : AdministrativeTransport protocol where
  extend := fun {_} _ {_ _ _ _} _ _ _ _ => ()
  related := by intros; trivial
  records_eq := by intros; rfl

private def bindings : Bindings protocol where
  prepend _ _ _ _ := ()
  prepend_related _ _ _ _ := trivial
  prepend_records _ _ _ _ := rfl
  restore _ := ()
  restore_related _ := trivial
  restore_records _ := rfl

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel definitions}
  (ordinaryCells : GenericHeap.OrdinaryCells model (GeneralizedLocalDescriptorHeap.cellModel model instances))
  {layouts : SourceCoreAllocationLayouts.Prepared}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {source : TypedSource}
  (sameDefinitions : layouts.definitions = definitions) (registered : frame.Registered definitions)

local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances

include ordinaryCells sameDefinitions registered in
theorem initialized {context nextContext : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active
      (TypedLexicalControl.initializedRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (TypedLexicalControl.initializedRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {embedding : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : model.Represents mapping world binder.scheme.body sourceValue value payload)
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body (some sourceValue) location after) :
    ∃ captured,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit value]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates (value :: actual) store (annotation.expression.rename embedding.lift) nextRef nextStore ∧
      DataHeap.EnvRepresents catalog nextMap nextWorld administrative ((binder.id, payload) :: scope)
        ((binder.id, location) :: environment) (nextRef :: canonical) definitions ∧
      GenericHeap.CellHeapRepresents cells nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) embedding).lift
        (nextRef :: canonical) (nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: value :: actual)
        (OptionalCell.referenceType payload :: payload :: actualContext) definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      CellAwareScopeAuthority.Effect instances mapping world before store nextMap nextWorld after nextStore := by
  let producer := CellAllocation.of_administrative (catalog := catalog) protocol transport bindings layouts frame cells
  obtain ⟨captured, _, _, evaluated, envs, heap, localAgreement, agreement, typed, ref, read, preserved, _⟩ :=
    CellAwareOrdinaryAllocation.allocate_initialized ordinaryCells producer sameDefinitions registered
      mono extended ordinary allocation annotation same represented environments heaps locals agrees actualTyped reference read allocated () trivial
  exact ⟨captured, evaluated, envs, heap, localAgreement, agreement, typed, ref, read, preserved,
    CellAwareScopeAuthority.Effect.append _ _ (.of_allocation allocated) ⟨_,rfl⟩ ⟨_,rfl⟩⟩

include ordinaryCells sameDefinitions registered in
theorem absent {context nextContext : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projection : projects binder.scheme.body payload)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active
      (TypedLexicalControl.absentRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (TypedLexicalControl.absentRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {embedding : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location after) :
    ∃ captured,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inLeft payload .unit]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates actual store (annotation.expression.rename embedding) nextRef nextStore ∧
      DataHeap.EnvRepresents catalog nextMap nextWorld administrative ((binder.id, payload) :: scope)
        ((binder.id, location) :: environment) (nextRef :: canonical) definitions ∧
      GenericHeap.CellHeapRepresents cells nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree embedding.lift (nextRef :: canonical) (nextRef :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: actual)
        (OptionalCell.referenceType payload :: actualContext) definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      CellAwareScopeAuthority.Effect instances mapping world before store nextMap nextWorld after nextStore := by
  let producer := CellAllocation.of_administrative (catalog := catalog) protocol transport bindings layouts frame cells
  obtain ⟨captured, _, _, evaluated, envs, heap, localAgreement, agreement, typed, ref, read, preserved, _⟩ :=
    CellAwareAbsentAllocation.allocate_absent ordinaryCells producer sameDefinitions registered
      mono extended ordinary projection allocation annotation same environments heaps locals agrees actualTyped reference read allocated () trivial
  exact ⟨captured, evaluated, envs, heap, localAgreement, agreement, typed, ref, read, preserved,
    CellAwareScopeAuthority.Effect.append _ _ (.of_allocation allocated) ⟨_,rfl⟩ ⟨_,rfl⟩⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodyAllocation
