import Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryAllocation
import Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryContinuation
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationPhysicalExtension
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmScopes

/-! An ordinary initialized declaration allocates from the successful child's
actual post. Every earlier generalized descriptor, frame and lexical authority
survives, and the real continuation receives the newly bound Source cell. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationOrdinaryPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open TypedLexicalWhile (initializedRequest sequence)
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
    {binder : TypedBinder} {lowered : SourceCoreBasic.LoweredExpr} {administrative actualContext : Core.Context}
    (mono : binder.scheme.quantified = [])
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders index.source)
    (extended : BinderExtends index.source.owner context binder nextContext)
    (ordinary : allocationSource.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts index.owner index.active
      (initializedRequest allocationSource scope binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))
      (initializedRequest allocationSource scope binder lowered.type))
    (same : annotation.original = allocation.expression)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
      whole.indexed.ancestry.layout.frame (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
    (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Core.Environment} {embedding : Renaming} {before after : Dynamic.Heap}
    {startStore store : Store} {sourceValue : Dynamic.Value} {value : Value} {location : Dynamic.Location}
    (initialized : Evaluates actual startStore (lowered.expression.rename embedding) (.inRight .word value) store)
    (represented : model.Represents mapping world binder.scheme.body sourceValue value lowered.type)
    (valueTyped : Dynamic.ValueHasType context before sourceValue binder.scheme.body)
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
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body (some sourceValue) location after)
    (output : Ty) (body : Expr) :
    ∃ marker,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame physical.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit value]
      let nextWorld := world ++ [whole.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType lowered.type) (store.length + 2)
      ContinuationAgreement actual startStore
        ((sequence output lowered.expression annotation.expression body).rename embedding)
        (nextRef :: value :: actual) nextStore
        (body.rename (Renaming.comp (Renaming.insertion 0) embedding).lift) ∧
      (∀ {size result finalStore}, EvaluationSize size actual startStore
        ((sequence output lowered.expression annotation.expression body).rename embedding) result finalStore →
        ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (nextRef :: value :: actual) nextStore
          (body.rename (Renaming.comp (Renaming.insertion 0) embedding).lift) result finalStore) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog) nextMap nextWorld administrative
        ((binder.id, lowered.type) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) whole.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) embedding).lift
        (nextRef :: canonical) (nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: value :: actual)
        (OptionalCell.referenceType lowered.type :: lowered.type :: actualContext) whole.indexed.layouts.definitions ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        mapping world before store nextMap nextWorld after nextStore ∧
      CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        index.owner index.active nextMap nextWorld after nextStore ((binder.id, location) :: environment) ∧
      ∃ reached : protocol.State ⟨(binder.id, lowered.type) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
        protocol.Relates initial reached ∧ Admission bridge nextContext reached ∧
      ∃ nextPhysical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole index nextContext ((binder.id, lowered.type) :: scope)
          (nextRef :: canonical) nextMap nextWorld after nextStore ((binder.id, location) :: environment),
        nextPhysical.location = physical.location ∧ nextPhysical.native = physical.native := by
  obtain ⟨marker, _captures, _markerTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
      nextAgrees, nextTyped, _nextReference, _nextRead, preserved, reached, related⟩ :=
    CellAwareOrdinaryAllocation.allocate_initialized_at_source (ordinary_cells (ordinary := model) (instances := GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
      producer rfl registered mono extended ordinary allocation annotation same represented environments heaps locals agrees actualTyped
      physical.reference physical.read allocated initial ready
  have metadata := Dynamic.HeapMetadataExtend.of_allocation allocated
  have effect := CellAwareScopeAuthority.Effect.append
    (instances := GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment) store
    [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame physical.native,
      SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit value] metadata
    (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
    (show WorldExtends world (world ++ [whole.indexed.ancestry.layout.frame.type,
      allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩)
  have nextAuthority := CellAwareScopeAuthority.At.cons (id := binder.id)
    (.ordinary allocated.reads_new rfl) (authority.transport effect)
  have nextAdmitted := CallableIndexedOwnedAdmittedLexicalAllocation.after_allocation bridge initial reached admitted
    extended (.some valueTyped) allocated preserved
  have head : CellAwareInvocationPhysical.Entry (attachment := attachment) whole index nextContext physical.location binder.id location
      (mapping ++ [store.length + 2])
      (world ++ [whole.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]) after
      (store ++ [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame physical.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit value]) :=
    .ordinary allocated.reads_new rfl
  let nextPhysical := (physical.transport effect preserved).cons extended
    (CompatibleMatchArmScopes.scope_bind lowered.type physical.declarations member extended) member
    (.cellRef (OptionalCell.cellType lowered.type) (store.length + 2)) head
  exact ⟨marker, CellAwareOrdinaryContinuation.agreement initialized allocationEval,
    fun completed => CellAwareOrdinaryContinuation.smaller initialized allocationEval completed,
    nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, preserved, effect,
    nextAuthority, reached, related, nextAdmitted, nextPhysical, rfl, rfl⟩

theorem complete {scope : SourceCoreLocalCell.Scope} {context nextContext : SourceSemantics.Context}
    {binder : TypedBinder} {lowered : SourceCoreBasic.LoweredExpr} {administrative actualContext : Core.Context}
    (mono : binder.scheme.quantified = [])
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders index.source)
    (extended : BinderExtends index.source.owner context binder nextContext)
    (ordinary : index.source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts index.owner index.active
      (initializedRequest index.source scope binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))
      (initializedRequest index.source scope binder lowered.type))
    (same : annotation.original = allocation.expression)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
      whole.indexed.ancestry.layout.frame (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
    (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Core.Environment} {embedding : Renaming} {before after : Dynamic.Heap}
    {startStore store : Store} {sourceValue : Dynamic.Value} {value : Value} {location : Dynamic.Location}
    (initialized : Evaluates actual startStore (lowered.expression.rename embedding) (.inRight .word value) store)
    (represented : model.Represents mapping world binder.scheme.body sourceValue value lowered.type)
    (valueTyped : Dynamic.ValueHasType context before sourceValue binder.scheme.body)
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
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body (some sourceValue) location after)
    (output : Ty) (body : Expr) :
    ∃ marker,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame physical.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit value]
      let nextWorld := world ++ [whole.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType lowered.type) (store.length + 2)
      ContinuationAgreement actual startStore
        ((sequence output lowered.expression annotation.expression body).rename embedding)
        (nextRef :: value :: actual) nextStore
        (body.rename (Renaming.comp (Renaming.insertion 0) embedding).lift) ∧
      (∀ {size result finalStore}, EvaluationSize size actual startStore
        ((sequence output lowered.expression annotation.expression body).rename embedding) result finalStore →
        ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (nextRef :: value :: actual) nextStore
          (body.rename (Renaming.comp (Renaming.insertion 0) embedding).lift) result finalStore) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog) nextMap nextWorld administrative
        ((binder.id, lowered.type) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) whole.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) embedding).lift
        (nextRef :: canonical) (nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: value :: actual)
        (OptionalCell.referenceType lowered.type :: lowered.type :: actualContext) whole.indexed.layouts.definitions ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        mapping world before store nextMap nextWorld after nextStore ∧
      CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        index.owner index.active nextMap nextWorld after nextStore ((binder.id, location) :: environment) ∧
      ∃ reached : protocol.State ⟨(binder.id, lowered.type) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
        protocol.Relates initial reached ∧ Admission bridge nextContext reached ∧
      ∃ nextPhysical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole index nextContext ((binder.id, lowered.type) :: scope)
          (nextRef :: canonical) nextMap nextWorld after nextStore ((binder.id, location) :: environment),
        nextPhysical.location = physical.location ∧ nextPhysical.native = physical.native := by
  apply complete_at_source (allocationSource := index.source) bridge <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationOrdinaryPrefix
