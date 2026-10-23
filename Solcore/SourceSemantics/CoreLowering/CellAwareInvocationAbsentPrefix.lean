import Solcore.SourceSemantics.CoreLowering.CellAwareAbsentAllocation
import Solcore.SourceSemantics.CoreLowering.CoreHelperInversion
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationPhysicalExtension
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmScopes

/-! The actual absent-cell allocation extends the mixed lexical state without
evaluating an initializer. Its continuation preserves all prior generalized
descriptors, source bindings and the original physical frame. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAbsentPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open TypedLexicalControl (absentRequest)
open GeneralizedLocalDescriptorHeap

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index whole bodyRelation}

theorem complete_at_source {allocationSource : TypedSource} {scope : SourceCoreLocalCell.Scope} {context nextContext : SourceSemantics.Context}
    {binder : TypedBinder} {payload : Ty} {administrative actualContext : Core.Context}
    (mono : binder.scheme.quantified = [])
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders index.source)
    (extended : BinderExtends index.source.owner context binder nextContext)
    (ordinary : allocationSource.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts index.owner index.active
      (absentRequest allocationSource scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))
      (absentRequest allocationSource scope binder payload))
    (same : annotation.original = allocation.expression)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
      whole.indexed.ancestry.layout.frame (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
    (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Core.Environment} {embedding : Renaming} {before after : Dynamic.Heap}
    {store : Store} {location : Dynamic.Location}
    (projection : projects binder.scheme.body payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
      mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
      index.owner index.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole index context scope canonical mapping world before store environment)
    (ready : producer.Ready initial physical.location physical.native)
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location after)
    (body : Expr) :
    ∃ marker,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame physical.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inLeft payload .unit]
      let nextWorld := world ++ [whole.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      ContinuationAgreement actual store
        ((Expr.letE annotation.expression body).rename embedding)
        (nextRef :: actual) nextStore
        (body.rename embedding.lift) ∧
      (∀ {size result finalStore}, EvaluationSize size actual store
        ((Expr.letE annotation.expression body).rename embedding) result finalStore →
        ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (nextRef :: actual) nextStore
          (body.rename embedding.lift) result finalStore) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) whole.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree embedding.lift
        (nextRef :: canonical) (nextRef :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: actual)
        (OptionalCell.referenceType payload :: actualContext) whole.indexed.layouts.definitions ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        mapping world before store nextMap nextWorld after nextStore ∧
      CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        index.owner index.active nextMap nextWorld after nextStore ((binder.id, location) :: environment) ∧
      ∃ reached : protocol.State ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
        protocol.Relates initial reached ∧ Admission bridge nextContext reached ∧
      ∃ nextPhysical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole index nextContext ((binder.id, payload) :: scope)
          (nextRef :: canonical) nextMap nextWorld after nextStore ((binder.id, location) :: environment),
        nextPhysical.location = physical.location ∧ nextPhysical.native = physical.native := by
  obtain ⟨marker, _captures, _markerTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
      nextAgrees, nextTyped, _nextReference, _nextRead, preserved, reached, related⟩ :=
    CellAwareAbsentAllocation.allocate_absent_at_source (ordinary_cells (ordinary := model) (instances := GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
      producer rfl registered mono extended ordinary projection allocation annotation same environments heaps locals agrees actualTyped
      physical.reference physical.read allocated initial ready
  have metadata := Dynamic.HeapMetadataExtend.of_allocation allocated
  have effect := CellAwareScopeAuthority.Effect.append
    (instances := GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment) store
    [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame physical.native,
      SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inLeft payload .unit] metadata
    (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
    (show WorldExtends world (world ++ [whole.indexed.ancestry.layout.frame.type,
      allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩)
  have nextAuthority := CellAwareScopeAuthority.At.cons (id := binder.id)
    (.ordinary allocated.reads_new rfl) (authority.transport effect)
  have nextAdmitted := CallableIndexedOwnedAdmittedLexicalAllocation.after_allocation bridge initial reached admitted
    extended (.none _) allocated preserved
  have head : CellAwareInvocationPhysical.Entry (attachment := attachment) whole index nextContext physical.location binder.id location
      (mapping ++ [store.length + 2])
      (world ++ [whole.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType payload]) after
      (store ++ [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame physical.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inLeft payload .unit]) :=
    .ordinary allocated.reads_new rfl
  let nextPhysical := (physical.transport effect preserved).cons extended
    (CompatibleMatchArmScopes.scope_bind payload physical.declarations member extended) member
    (.cellRef (OptionalCell.cellType payload) (store.length + 2)) head
  exact ⟨marker, (by simpa only [Expr.rename] using ContinuationAgreement.letE (body := body.rename embedding.lift) allocationEval),
    (fun completed => by simpa only [Expr.rename] using completed.let_body allocationEval),
    nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, preserved, effect,
    nextAuthority, reached, related, nextAdmitted, nextPhysical, rfl, rfl⟩

theorem complete {scope : SourceCoreLocalCell.Scope} {context nextContext : SourceSemantics.Context}
    {binder : TypedBinder} {payload : Ty} {administrative actualContext : Core.Context}
    (mono : binder.scheme.quantified = [])
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders index.source)
    (extended : BinderExtends index.source.owner context binder nextContext)
    (ordinary : index.source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts index.owner index.active
      (absentRequest index.source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))
      (absentRequest index.source scope binder payload))
    (same : annotation.original = allocation.expression)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
      whole.indexed.ancestry.layout.frame (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
    (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Core.Environment} {embedding : Renaming} {before after : Dynamic.Heap}
    {store : Store} {location : Dynamic.Location}
    (projection : projects binder.scheme.body payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
      mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
      index.owner index.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole index context scope canonical mapping world before store environment)
    (ready : producer.Ready initial physical.location physical.native)
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location after)
    (body : Expr) :
    ∃ marker,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame physical.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inLeft payload .unit]
      let nextWorld := world ++ [whole.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      ContinuationAgreement actual store
        ((Expr.letE annotation.expression body).rename embedding)
        (nextRef :: actual) nextStore
        (body.rename embedding.lift) ∧
      (∀ {size result finalStore}, EvaluationSize size actual store
        ((Expr.letE annotation.expression body).rename embedding) result finalStore →
        ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (nextRef :: actual) nextStore
          (body.rename embedding.lift) result finalStore) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) whole.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree embedding.lift
        (nextRef :: canonical) (nextRef :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: actual)
        (OptionalCell.referenceType payload :: actualContext) whole.indexed.layouts.definitions ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        mapping world before store nextMap nextWorld after nextStore ∧
      CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        index.owner index.active nextMap nextWorld after nextStore ((binder.id, location) :: environment) ∧
      ∃ reached : protocol.State ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
        protocol.Relates initial reached ∧ Admission bridge nextContext reached ∧
      ∃ nextPhysical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole index nextContext ((binder.id, payload) :: scope)
          (nextRef :: canonical) nextMap nextWorld after nextStore ((binder.id, location) :: environment),
        nextPhysical.location = physical.location ∧ nextPhysical.native = physical.native := by
  apply complete_at_source (allocationSource := index.source) bridge <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAbsentPrefix
