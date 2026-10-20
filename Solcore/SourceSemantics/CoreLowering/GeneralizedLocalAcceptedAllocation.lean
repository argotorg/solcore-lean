import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedInitializer
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedLocatedRows

/-! The real generalized initializer and marked cell allocation share the
same ordered row values. Each row keeps its creation frame after allocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedAllocation
open Core Frontend SourceInference TypeSystem GeneralHeap
open SourceCoreLocalPolymorphism DataPatternValues
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalDescriptorOrigin (Origin)

theorem formation_allocates_with {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {function : Dynamic.GeneralizedClosure} {binding : Binding} {lexical : Substitution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalAcceptedInitializer.Receipt prepared inputs binding lexical lowered)
    (sourceAttachment : Dynamic.GeneralizedClosure → Binding → Substitution → Prop)
    (attached : sourceAttachment function binding lexical)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : Origin prepared function binding lexical)
    (attachment : GeneralizedLocalLocatedRows.Attachment
      (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment) function binding lexical)
    {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
    {store : Store} {location : Core.Location}
    (reference : captured.canonical[SourceCoreCallableIndexedAncestry.creationReferenceIndex
      inputs.current inputs.scope]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some
      (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native))
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {ordinary : GenericHeap.PayloadModel catalog projects prepared.layouts.definitions}
    {before after : Dynamic.Heap} {sourceLocation : Dynamic.Location}
    {snapshot marker : Core.Value} {snapshotType markerType : Core.Ty}
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel ordinary (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment))
      mapping world before store)
    (snapshotTyped : RuntimeValueHasType world snapshot snapshotType prepared.layouts.definitions)
    (markerTyped : RuntimeValueHasType world marker markerType prepared.layouts.definitions)
    (allocated : Dynamic.Heap.AllocatesGeneralized before function sourceLocation after) :
    ∃ values,
      Evaluates actual store (lowered.expression.rename captured.embedding)
        (.inRight .word (ProductBundle.value values)) store ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel ordinary (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment))
        (mapping ++ [store.length + 2])
        (world ++ [snapshotType, markerType, OptionalCell.cellType (binding.bundleType lexical)]) after
        (store ++ [snapshot, marker, .inRight .unit (ProductBundle.value values)]) ∧
      ∃ located : GeneralizedLocalLocatedRows.Located (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment)
          function binding lexical sourceLocation (mapping ++ [store.length + 2])
          (world ++ [snapshotType, markerType, OptionalCell.cellType (binding.bundleType lexical)]) after
          (store ++ [snapshot, marker, .inRight .unit (ProductBundle.value values)]),
        located.values = values ∧
        GeneralizedLocalAcceptedLocatedRows.Located.FramesWith sourceAttachment located location := by
  obtain ⟨values, evaluated, rows, frames, _stored⟩ :=
    GeneralizedLocalAcceptedInitializer.formation_with receipt sourceAttachment attached owner initializer origin attachment
      captured declarations ownership issuer typed heaps.runtime_hasTypes reference read
  obtain ⟨afterHeaps, located, sameValues⟩ := GeneralizedLocalLocatedRows.of_marked_allocation_values
    heaps attachment rows snapshotTyped markerTyped allocated
  refine ⟨values, evaluated, afterHeaps, located, sameValues, ?_⟩
  change ProductBundle.Pointwise _ _ _
  rw [sameValues]
  clear evaluated rows _stored afterHeaps located sameValues
  generalize binding.atContext lexical = candidates at frames ⊢
  induction frames with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.extend ⟨_, rfl⟩ ⟨_, rfl⟩) ih

theorem formation_allocates {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {function : Dynamic.GeneralizedClosure} {binding : Binding} {lexical : Substitution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalAcceptedInitializer.Receipt prepared inputs binding lexical lowered)
    (descriptorSource : function.source = binding.source)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : Origin prepared function binding lexical)
    (attachment : GeneralizedLocalLocatedRows.Attachment
      (GeneralizedLocalAcceptedInstances.model prepared) function binding lexical)
    {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
    {store : Store} {location : Core.Location}
    (reference : captured.canonical[SourceCoreCallableIndexedAncestry.creationReferenceIndex
      inputs.current inputs.scope]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some
      (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native))
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {ordinary : GenericHeap.PayloadModel catalog projects prepared.layouts.definitions}
    {before after : Dynamic.Heap} {sourceLocation : Dynamic.Location}
    {snapshot marker : Core.Value} {snapshotType markerType : Core.Ty}
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel ordinary (GeneralizedLocalAcceptedInstances.model prepared))
      mapping world before store)
    (snapshotTyped : RuntimeValueHasType world snapshot snapshotType prepared.layouts.definitions)
    (markerTyped : RuntimeValueHasType world marker markerType prepared.layouts.definitions)
    (allocated : Dynamic.Heap.AllocatesGeneralized before function sourceLocation after) :
    ∃ values,
      Evaluates actual store (lowered.expression.rename captured.embedding)
        (.inRight .word (ProductBundle.value values)) store ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel ordinary (GeneralizedLocalAcceptedInstances.model prepared))
        (mapping ++ [store.length + 2])
        (world ++ [snapshotType, markerType, OptionalCell.cellType (binding.bundleType lexical)]) after
        (store ++ [snapshot, marker, .inRight .unit (ProductBundle.value values)]) ∧
      ∃ located : GeneralizedLocalLocatedRows.Located (GeneralizedLocalAcceptedInstances.model prepared)
          function binding lexical sourceLocation (mapping ++ [store.length + 2])
          (world ++ [snapshotType, markerType, OptionalCell.cellType (binding.bundleType lexical)]) after
          (store ++ [snapshot, marker, .inRight .unit (ProductBundle.value values)]),
        located.values = values ∧
        GeneralizedLocalAcceptedLocatedRows.Located.Frames located location := by
  exact formation_allocates_with receipt (fun function binding _ => function.source = binding.source)
    descriptorSource owner initializer origin attachment captured declarations ownership issuer typed reference read
    heaps snapshotTyped markerTyped allocated

/-- Storage retains the actual independently tracked Source and capture frame. -/
theorem formation_allocates_tracked {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {function : Dynamic.GeneralizedClosure} {binding : Binding} {lexical : Substitution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalAcceptedInitializer.Receipt prepared inputs binding lexical lowered)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : Origin prepared function binding lexical)
    (attachment : GeneralizedLocalLocatedRows.Attachment
      (GeneralizedLocalAcceptedInstances.trackedModel prepared) function binding lexical)
    {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
    {store : Store} {location : Core.Location}
    (reference : captured.canonical[SourceCoreCallableIndexedAncestry.creationReferenceIndex
      inputs.current inputs.scope]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some
      (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native))
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {ordinary : GenericHeap.PayloadModel catalog projects prepared.layouts.definitions}
    {before after : Dynamic.Heap} {sourceLocation : Dynamic.Location}
    {snapshot marker : Core.Value} {snapshotType markerType : Core.Ty}
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel ordinary (GeneralizedLocalAcceptedInstances.trackedModel prepared))
      mapping world before store)
    (snapshotTyped : RuntimeValueHasType world snapshot snapshotType prepared.layouts.definitions)
    (markerTyped : RuntimeValueHasType world marker markerType prepared.layouts.definitions)
    (allocated : Dynamic.Heap.AllocatesGeneralized before function sourceLocation after) :
    ∃ values,
      Evaluates actual store (lowered.expression.rename captured.embedding)
        (.inRight .word (ProductBundle.value values)) store ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel ordinary (GeneralizedLocalAcceptedInstances.trackedModel prepared))
        (mapping ++ [store.length + 2])
        (world ++ [snapshotType, markerType, OptionalCell.cellType (binding.bundleType lexical)]) after
        (store ++ [snapshot, marker, .inRight .unit (ProductBundle.value values)]) ∧
      ∃ located : GeneralizedLocalLocatedRows.Located (GeneralizedLocalAcceptedInstances.trackedModel prepared)
          function binding lexical sourceLocation (mapping ++ [store.length + 2])
          (world ++ [snapshotType, markerType, OptionalCell.cellType (binding.bundleType lexical)]) after
          (store ++ [snapshot, marker, .inRight .unit (ProductBundle.value values)]),
        located.values = values ∧
        GeneralizedLocalAcceptedLocatedRows.Located.FramesWith (fun _ _ _ => True) located location := by
  exact formation_allocates_with receipt (fun _ _ _ => True) True.intro owner initializer origin attachment
    captured declarations ownership issuer typed reference read heaps snapshotTyped markerTyped allocated

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedAllocation
