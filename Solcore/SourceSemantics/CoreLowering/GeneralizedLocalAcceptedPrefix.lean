import Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedDeclaration
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedInitializer
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedLocatedRows
import Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedContinuation

/-! Actual generalized declarations reach their emitted continuation for any
accepted candidate body. Ordered stored rows, the creation frame, and the real
marked allocator survive in both execution directions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open TypedLexicalWhile (initializedRequest sequence)
open GeneralizedLocalDescriptorHeap GeneralizedLocalLocatedRows
open GeneralizedLocalInstanceCompilation (Inputs)

private theorem framed_after_allocation {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {ordinary : GenericHeap.PayloadModel catalog projects prepared.layouts.definitions}
    {sourceAttachment : Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request}
    (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts owner active request)
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : TypeSystem.Substitution} {values : List Value}
    (payload : request.payloadType = binding.bundleType lexical)
    (attachment : Attachment (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment) function binding lexical)
    {mapping : LocationMap} {world : StoreTyping} {heap after : Dynamic.Heap} {store : Store}
    (heaps : GenericHeap.CellHeapRepresents
      (cellModel ordinary (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment)) mapping world heap store)
    (rows : SourceCoreLocalPolymorphism.ProductBundle.Pointwise
      (GeneralizedLocalAcceptedInstances.RepresentsWith prepared mapping world function binding lexical (sourceAttachment function binding lexical))
      (binding.atContext lexical) values)
    {frameLocation : Core.Location}
    (frames : SourceCoreLocalPolymorphism.ProductBundle.Pointwise
      (GeneralizedLocalAcceptedInstances.Snapshot prepared mapping world function binding lexical frameLocation (sourceAttachment function binding lexical))
      (binding.atContext lexical) values)
    {native : NativeFrame} {captured : Value} {location : Dynamic.Location}
    (registered : prepared.ancestry.layout.frame.Registered prepared.layouts.definitions)
    (capturedTyped : RuntimeValueHasType world captured (SourceCoreSourceCells.captureType request.scope)
      prepared.layouts.definitions)
    (allocated : Dynamic.Heap.AllocatesGeneralized heap function location after) :
    ∃ located : Located (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment) function binding lexical location
      (mapping ++ [store.length + 2])
      (world ++ [prepared.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType request.payloadType]) after
      (store ++ [SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
        .inRight .unit (SourceCoreLocalPolymorphism.ProductBundle.value values)]), GeneralizedLocalAcceptedLocatedRows.Located.FramesWith sourceAttachment located frameLocation := by
  have captureType : allocation.entry.layout.captureType = SourceCoreSourceCells.captureType request.scope := by
    change SourceCoreSourceCells.captureType allocation.entry.key.scope = _
    rw [allocation.keyExact]
    rfl
  have markerTyped : RuntimeValueHasType world (SourceCoreHeapMarkers.markerValue allocation.entry.layout captured)
      allocation.entry.layout.type prepared.layouts.definitions :=
    .constructed allocation.registered.payloadLookup (captureType.symm ▸ capturedTyped)
  obtain ⟨located, sameValues⟩ := (GeneralizedLocalLocatedRows.of_marked_allocation_values heaps attachment rows
    (SourceCoreCallableIndexedFrames.encode_runtime_typed world registered native) markerTyped allocated).2
  have finalFrames : GeneralizedLocalAcceptedLocatedRows.Located.FramesWith sourceAttachment located frameLocation := by
    change SourceCoreLocalPolymorphism.ProductBundle.Pointwise _ _ _
    rw [sameValues]
    clear sameValues located rows
    generalize binding.atContext lexical = candidates at frames ⊢
    induction frames with
    | nil => exact .nil
    | cons head _ ih => exact .cons (head.extend ⟨_, rfl⟩ ⟨_, rfl⟩) ih
  rw [payload]
  exact ⟨located, finalFrames⟩


theorem complete_with_at_source {allocationSource : TypedSource} {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog checked.catalog) projects prepared.layouts.definitions}
    {inputs : Inputs} {function : Dynamic.GeneralizedClosure}
    {binding : SourceCoreLocalPolymorphism.Binding} {lexical : TypeSystem.Substitution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalAcceptedInitializer.Receipt prepared inputs binding lexical lowered)
    (sourceAttachment : Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (attached : sourceAttachment function binding lexical)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : GeneralizedLocalDescriptorOrigin.Origin prepared function binding lexical)
    (attachment : Attachment (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment) function binding lexical)
    {context : SourceSemantics.Context}
    (extended : BinderExtends function.source.owner function.definitionContext function.binder context)
    (ordinary : allocationSource.inputs.any (fun input => decide (input.id = function.binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts inputs.current.owner lexical
      (initializedRequest allocationSource inputs.scope function.binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated prepared.ancestry.layout.frame
      prepared.base.globals.length
      (prepared.layouts.allocatorAt inputs.current.owner lexical (fun error => .sourceAllocation (reprStr error)))
      (initializedRequest allocationSource inputs.scope function.binder lowered.type))
    (same : annotation.original = allocation.expression)
    {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog checked.catalog) protocol prepared.layouts
      prepared.ancestry.layout.frame (cellModel model (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment)))
    (registered : prepared.ancestry.layout.frame.Registered prepared.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
    {before after : Dynamic.Heap} {store : Store} {sourceLocation : Dynamic.Location} {frameLocation : Core.Location}
    (heaps : GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment))
      mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.definitionContext.locals function.captured)
    (reference : captured.canonical[inputs.scope.length + 1 + prepared.base.globals.length]? =
      some (.cellRef prepared.ancestry.layout.frame.type frameLocation))
    (index : SourceCoreCallableIndexedAncestry.creationReferenceIndex inputs.current inputs.scope =
      inputs.scope.length + 1 + prepared.base.globals.length)
    (read : store.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native))
    (allocated : Dynamic.Heap.AllocatesGeneralized before function sourceLocation after)
    (initial : protocol.State ⟨inputs.scope, mapping, world, before, store, captured.canonical⟩)
    (ready : producer.Ready initial frameLocation origin.native)
    (output : Ty) (body : Expr) :
    ∃ values marker,
      let bundle := SourceCoreLocalPolymorphism.ProductBundle.value values
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit bundle]
      let nextWorld := world ++ [prepared.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType lowered.type) (store.length + 2)
      ContinuationAgreement actual store
        ((sequence output lowered.expression annotation.expression body).rename captured.embedding)
        (nextRef :: bundle :: actual) nextStore
        (body.rename (Renaming.comp (Renaming.insertion 0) captured.embedding).lift) ∧
      (∀ {size value finalStore},
        EvaluationSize size actual store
          ((sequence output lowered.expression annotation.expression body).rename captured.embedding) value finalStore →
        ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (nextRef :: bundle :: actual) nextStore
          (body.rename (Renaming.comp (Renaming.insertion 0) captured.embedding).lift) value finalStore) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) nextMap nextWorld captured.administrative
        ((function.binder.id, lowered.type) :: inputs.scope)
        ((function.binder.id, sourceLocation) :: function.captured) (nextRef :: captured.canonical) prepared.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after context.locals ((function.binder.id, sourceLocation) :: function.captured) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) captured.embedding).lift
        (nextRef :: captured.canonical) (nextRef :: bundle :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: bundle :: actual)
        (OptionalCell.referenceType lowered.type :: lowered.type :: captured.actualContext) prepared.layouts.definitions ∧
      (nextRef :: captured.canonical)[((function.binder.id, lowered.type) :: inputs.scope).length + 1 + prepared.base.globals.length]? =
        some (.cellRef prepared.ancestry.layout.frame.type frameLocation) ∧
      nextStore.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      (∃ located : Located (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment) function binding lexical sourceLocation
        nextMap nextWorld after nextStore, GeneralizedLocalAcceptedLocatedRows.Located.FramesWith sourceAttachment located frameLocation) ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨(function.binder.id, lowered.type) :: inputs.scope, nextMap, nextWorld, after, nextStore, nextRef :: captured.canonical⟩ := by
  obtain ⟨values, initialized, rows, frames, stored⟩ := GeneralizedLocalAcceptedInitializer.formation_with
    receipt sourceAttachment attached owner initializer origin attachment captured declarations ownership issuer nativeTyped heaps.runtime_hasTypes
    (index ▸ reference) read
  obtain ⟨marker, _markerCaptures, markerTyped, allocatedNative, environments, finalHeaps, finalLocals,
      agrees, typed, finalReference, finalRead, preserved, transition⟩ :=
    CellAwareGeneralizedAllocation.allocate_initialized_at_source producer rfl registered extended ordinary
      allocation annotation same attachment.captures stored captured.represented heaps locals
      captured.agrees captured.typed reference read allocated initial ready
  have located := framed_after_allocation allocation
    (congrArg SourceCoreBasic.LoweredExpr.type receipt.original.emitted)
    attachment heaps rows frames registered markerTyped (native := origin.native) allocated
  exact ⟨values, marker, CellAwareGeneralizedDeclaration.sequence_agreement initialized allocatedNative,
    fun completed => CellAwareGeneralizedContinuation.smaller initialized allocatedNative completed,
    environments, finalHeaps, finalLocals, agrees, typed, finalReference, finalRead, preserved, located, transition⟩

/- Compatibility wrapper using the semantic source for the allocation request. -/
theorem complete_with {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog checked.catalog) projects prepared.layouts.definitions}
    {inputs : Inputs} {function : Dynamic.GeneralizedClosure}
    {binding : SourceCoreLocalPolymorphism.Binding} {lexical : TypeSystem.Substitution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalAcceptedInitializer.Receipt prepared inputs binding lexical lowered)
    (sourceAttachment : Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (attached : sourceAttachment function binding lexical)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : GeneralizedLocalDescriptorOrigin.Origin prepared function binding lexical)
    (attachment : Attachment (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment) function binding lexical)
    {context : SourceSemantics.Context}
    (extended : BinderExtends function.source.owner function.definitionContext function.binder context)
    (ordinary : function.source.inputs.any (fun input => decide (input.id = function.binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts inputs.current.owner lexical
      (initializedRequest function.source inputs.scope function.binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated prepared.ancestry.layout.frame
      prepared.base.globals.length
      (prepared.layouts.allocatorAt inputs.current.owner lexical (fun error => .sourceAllocation (reprStr error)))
      (initializedRequest function.source inputs.scope function.binder lowered.type))
    (same : annotation.original = allocation.expression)
    {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog checked.catalog) protocol prepared.layouts
      prepared.ancestry.layout.frame (cellModel model (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment)))
    (registered : prepared.ancestry.layout.frame.Registered prepared.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
    {before after : Dynamic.Heap} {store : Store} {sourceLocation : Dynamic.Location} {frameLocation : Core.Location}
    (heaps : GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment))
      mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.definitionContext.locals function.captured)
    (reference : captured.canonical[inputs.scope.length + 1 + prepared.base.globals.length]? =
      some (.cellRef prepared.ancestry.layout.frame.type frameLocation))
    (index : SourceCoreCallableIndexedAncestry.creationReferenceIndex inputs.current inputs.scope =
      inputs.scope.length + 1 + prepared.base.globals.length)
    (read : store.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native))
    (allocated : Dynamic.Heap.AllocatesGeneralized before function sourceLocation after)
    (initial : protocol.State ⟨inputs.scope, mapping, world, before, store, captured.canonical⟩)
    (ready : producer.Ready initial frameLocation origin.native)
    (output : Ty) (body : Expr) :
    ∃ values marker,
      let bundle := SourceCoreLocalPolymorphism.ProductBundle.value values
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit bundle]
      let nextWorld := world ++ [prepared.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType lowered.type) (store.length + 2)
      ContinuationAgreement actual store
        ((sequence output lowered.expression annotation.expression body).rename captured.embedding)
        (nextRef :: bundle :: actual) nextStore
        (body.rename (Renaming.comp (Renaming.insertion 0) captured.embedding).lift) ∧
      (∀ {size value finalStore},
        EvaluationSize size actual store
          ((sequence output lowered.expression annotation.expression body).rename captured.embedding) value finalStore →
        ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (nextRef :: bundle :: actual) nextStore
          (body.rename (Renaming.comp (Renaming.insertion 0) captured.embedding).lift) value finalStore) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) nextMap nextWorld captured.administrative
        ((function.binder.id, lowered.type) :: inputs.scope)
        ((function.binder.id, sourceLocation) :: function.captured) (nextRef :: captured.canonical) prepared.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after context.locals ((function.binder.id, sourceLocation) :: function.captured) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) captured.embedding).lift
        (nextRef :: captured.canonical) (nextRef :: bundle :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: bundle :: actual)
        (OptionalCell.referenceType lowered.type :: lowered.type :: captured.actualContext) prepared.layouts.definitions ∧
      (nextRef :: captured.canonical)[((function.binder.id, lowered.type) :: inputs.scope).length + 1 + prepared.base.globals.length]? =
        some (.cellRef prepared.ancestry.layout.frame.type frameLocation) ∧
      nextStore.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      (∃ located : Located (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment) function binding lexical sourceLocation
        nextMap nextWorld after nextStore, GeneralizedLocalAcceptedLocatedRows.Located.FramesWith sourceAttachment located frameLocation) ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨(function.binder.id, lowered.type) :: inputs.scope, nextMap, nextWorld, after, nextStore, nextRef :: captured.canonical⟩ := by
  exact complete_with_at_source (allocationSource := function.source) receipt sourceAttachment attached owner initializer origin attachment
    extended ordinary allocation annotation same producer registered captured declarations ownership issuer nativeTyped
    heaps locals reference index read allocated initial ready output body

theorem complete {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog checked.catalog) projects prepared.layouts.definitions}
    {inputs : Inputs} {function : Dynamic.GeneralizedClosure}
    {binding : SourceCoreLocalPolymorphism.Binding} {lexical : TypeSystem.Substitution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalAcceptedInitializer.Receipt prepared inputs binding lexical lowered)
    (descriptorSource : function.source = binding.source)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : GeneralizedLocalDescriptorOrigin.Origin prepared function binding lexical)
    (attachment : Attachment (GeneralizedLocalAcceptedInstances.model prepared) function binding lexical)
    {context : SourceSemantics.Context}
    (extended : BinderExtends function.source.owner function.definitionContext function.binder context)
    (ordinary : function.source.inputs.any (fun input => decide (input.id = function.binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts inputs.current.owner lexical
      (initializedRequest function.source inputs.scope function.binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated prepared.ancestry.layout.frame
      prepared.base.globals.length
      (prepared.layouts.allocatorAt inputs.current.owner lexical (fun error => .sourceAllocation (reprStr error)))
      (initializedRequest function.source inputs.scope function.binder lowered.type))
    (same : annotation.original = allocation.expression)
    {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog checked.catalog) protocol prepared.layouts
      prepared.ancestry.layout.frame (cellModel model (GeneralizedLocalAcceptedInstances.model prepared)))
    (registered : prepared.ancestry.layout.frame.Registered prepared.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
    {before after : Dynamic.Heap} {store : Store} {sourceLocation : Dynamic.Location} {frameLocation : Core.Location}
    (heaps : GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.model prepared))
      mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.definitionContext.locals function.captured)
    (reference : captured.canonical[inputs.scope.length + 1 + prepared.base.globals.length]? =
      some (.cellRef prepared.ancestry.layout.frame.type frameLocation))
    (index : SourceCoreCallableIndexedAncestry.creationReferenceIndex inputs.current inputs.scope =
      inputs.scope.length + 1 + prepared.base.globals.length)
    (read : store.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native))
    (allocated : Dynamic.Heap.AllocatesGeneralized before function sourceLocation after)
    (initial : protocol.State ⟨inputs.scope, mapping, world, before, store, captured.canonical⟩)
    (ready : producer.Ready initial frameLocation origin.native)
    (output : Ty) (body : Expr) :
    ∃ values marker,
      let bundle := SourceCoreLocalPolymorphism.ProductBundle.value values
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit bundle]
      let nextWorld := world ++ [prepared.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType lowered.type) (store.length + 2)
      ContinuationAgreement actual store
        ((sequence output lowered.expression annotation.expression body).rename captured.embedding)
        (nextRef :: bundle :: actual) nextStore
        (body.rename (Renaming.comp (Renaming.insertion 0) captured.embedding).lift) ∧
      (∀ {size value finalStore},
        EvaluationSize size actual store
          ((sequence output lowered.expression annotation.expression body).rename captured.embedding) value finalStore →
        ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (nextRef :: bundle :: actual) nextStore
          (body.rename (Renaming.comp (Renaming.insertion 0) captured.embedding).lift) value finalStore) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) nextMap nextWorld captured.administrative
        ((function.binder.id, lowered.type) :: inputs.scope)
        ((function.binder.id, sourceLocation) :: function.captured) (nextRef :: captured.canonical) prepared.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.model prepared))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after context.locals ((function.binder.id, sourceLocation) :: function.captured) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) captured.embedding).lift
        (nextRef :: captured.canonical) (nextRef :: bundle :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: bundle :: actual)
        (OptionalCell.referenceType lowered.type :: lowered.type :: captured.actualContext) prepared.layouts.definitions ∧
      (nextRef :: captured.canonical)[((function.binder.id, lowered.type) :: inputs.scope).length + 1 + prepared.base.globals.length]? =
        some (.cellRef prepared.ancestry.layout.frame.type frameLocation) ∧
      nextStore.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      (∃ located : Located (GeneralizedLocalAcceptedInstances.model prepared) function binding lexical sourceLocation
        nextMap nextWorld after nextStore, GeneralizedLocalAcceptedLocatedRows.Located.Frames located frameLocation) ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨(function.binder.id, lowered.type) :: inputs.scope, nextMap, nextWorld, after, nextStore, nextRef :: captured.canonical⟩ := by
  exact complete_with receipt (fun function binding _ => function.source = binding.source) descriptorSource
    owner initializer origin attachment extended ordinary allocation annotation same producer registered captured
    declarations ownership issuer nativeTyped heaps locals reference index read allocated initial ready output body

/-- The actual paired Source reaches the emitted body continuation without a canonical Source equality. -/
theorem complete_tracked {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog checked.catalog) projects prepared.layouts.definitions}
    {inputs : Inputs} {function : Dynamic.GeneralizedClosure}
    {binding : SourceCoreLocalPolymorphism.Binding} {lexical : TypeSystem.Substitution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalAcceptedInitializer.Receipt prepared inputs binding lexical lowered)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : GeneralizedLocalDescriptorOrigin.Origin prepared function binding lexical)
    (attachment : Attachment (GeneralizedLocalAcceptedInstances.trackedModel prepared) function binding lexical)
    {context : SourceSemantics.Context}
    (extended : BinderExtends function.source.owner function.definitionContext function.binder context)
    (ordinary : function.source.inputs.any (fun input => decide (input.id = function.binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts inputs.current.owner lexical
      (initializedRequest function.source inputs.scope function.binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated prepared.ancestry.layout.frame
      prepared.base.globals.length
      (prepared.layouts.allocatorAt inputs.current.owner lexical (fun error => .sourceAllocation (reprStr error)))
      (initializedRequest function.source inputs.scope function.binder lowered.type))
    (same : annotation.original = allocation.expression)
    {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog checked.catalog) protocol prepared.layouts
      prepared.ancestry.layout.frame (cellModel model (GeneralizedLocalAcceptedInstances.trackedModel prepared)))
    (registered : prepared.ancestry.layout.frame.Registered prepared.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
    {before after : Dynamic.Heap} {store : Store} {sourceLocation : Dynamic.Location} {frameLocation : Core.Location}
    (heaps : GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.trackedModel prepared))
      mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.definitionContext.locals function.captured)
    (reference : captured.canonical[inputs.scope.length + 1 + prepared.base.globals.length]? =
      some (.cellRef prepared.ancestry.layout.frame.type frameLocation))
    (index : SourceCoreCallableIndexedAncestry.creationReferenceIndex inputs.current inputs.scope =
      inputs.scope.length + 1 + prepared.base.globals.length)
    (read : store.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native))
    (allocated : Dynamic.Heap.AllocatesGeneralized before function sourceLocation after)
    (initial : protocol.State ⟨inputs.scope, mapping, world, before, store, captured.canonical⟩)
    (ready : producer.Ready initial frameLocation origin.native)
    (output : Ty) (body : Expr) :
    ∃ values marker,
      let bundle := SourceCoreLocalPolymorphism.ProductBundle.value values
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit bundle]
      let nextWorld := world ++ [prepared.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType lowered.type) (store.length + 2)
      ContinuationAgreement actual store
        ((sequence output lowered.expression annotation.expression body).rename captured.embedding)
        (nextRef :: bundle :: actual) nextStore
        (body.rename (Renaming.comp (Renaming.insertion 0) captured.embedding).lift) ∧
      (∀ {size value finalStore},
        EvaluationSize size actual store
          ((sequence output lowered.expression annotation.expression body).rename captured.embedding) value finalStore →
        ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (nextRef :: bundle :: actual) nextStore
          (body.rename (Renaming.comp (Renaming.insertion 0) captured.embedding).lift) value finalStore) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) nextMap nextWorld captured.administrative
        ((function.binder.id, lowered.type) :: inputs.scope)
        ((function.binder.id, sourceLocation) :: function.captured) (nextRef :: captured.canonical) prepared.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.trackedModel prepared))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after context.locals ((function.binder.id, sourceLocation) :: function.captured) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) captured.embedding).lift
        (nextRef :: captured.canonical) (nextRef :: bundle :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: bundle :: actual)
        (OptionalCell.referenceType lowered.type :: lowered.type :: captured.actualContext) prepared.layouts.definitions ∧
      (nextRef :: captured.canonical)[((function.binder.id, lowered.type) :: inputs.scope).length + 1 + prepared.base.globals.length]? =
        some (.cellRef prepared.ancestry.layout.frame.type frameLocation) ∧
      nextStore.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      (∃ located : Located (GeneralizedLocalAcceptedInstances.trackedModel prepared) function binding lexical sourceLocation
        nextMap nextWorld after nextStore, GeneralizedLocalAcceptedLocatedRows.Located.FramesWith (fun _ _ _ => True) located frameLocation) ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨(function.binder.id, lowered.type) :: inputs.scope, nextMap, nextWorld, after, nextStore, nextRef :: captured.canonical⟩ := by
  exact complete_with receipt (fun _ _ _ => True) True.intro owner initializer origin attachment
    extended ordinary allocation annotation same producer registered captured declarations ownership issuer nativeTyped
    heaps locals reference index read allocated initial ready output body

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedPrefix
