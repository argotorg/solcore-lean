import Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedDeclaration
import Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedContinuation

/-! The production bundle initializer and marked descriptor allocation form
one two-way continuation boundary. The reached environment is suitable for
the next lexical statement and retains an exact located descriptor row. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open TypedLexicalWhile (initializedRequest sequence)
open GeneralizedLocalDescriptorHeap GeneralizedLocalLocatedRows
open GeneralizedLocalInstanceCompilation (Inputs)

theorem complete {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog checked.catalog) projects prepared.layouts.definitions}
    {inputs : Inputs} {function : Dynamic.GeneralizedClosure}
    {binding : SourceCoreLocalPolymorphism.Binding} {lexical : TypeSystem.Substitution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalInitializerPackets.Receipt prepared inputs binding lexical lowered)
    (descriptorSource : function.source = binding.source)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : GeneralizedLocalDescriptorOrigin.Origin prepared function binding lexical)
    (namedLexical : lexical = [])
    (namedMetadata : origin.metadata = ⟨⟨binding.caller, [], binding.source⟩, []⟩)
    (attachment : Attachment (GeneralizedLocalInstanceValues.model prepared) function binding lexical)
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
      prepared.ancestry.layout.frame (cellModel model (GeneralizedLocalInstanceValues.model prepared)))
    (registered : prepared.ancestry.layout.frame.Registered prepared.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
    {before after : Dynamic.Heap} {store : Store} {sourceLocation : Dynamic.Location} {frameLocation : Core.Location}
    (heaps : GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalInstanceValues.model prepared))
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
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalInstanceValues.model prepared))
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
      (∃ located : Located (GeneralizedLocalInstanceValues.model prepared) function binding lexical sourceLocation
        nextMap nextWorld after nextStore, located.Frames frameLocation) ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨(function.binder.id, lowered.type) :: inputs.scope, nextMap, nextWorld, after, nextStore, nextRef :: captured.canonical⟩ := by
  obtain ⟨values, initialized, rows, frames, stored⟩ := GeneralizedLocalInitializerMeaning.formation
    receipt descriptorSource owner initializer origin namedLexical namedMetadata attachment captured declarations ownership issuer nativeTyped heaps.runtime_hasTypes
    (index ▸ reference) read
  obtain ⟨marker, _markerCaptures, markerTyped, allocatedNative, environments, finalHeaps, finalLocals,
      agrees, typed, finalReference, finalRead, preserved, transition⟩ :=
    CellAwareGeneralizedAllocation.allocate_initialized producer rfl registered extended ordinary
      allocation annotation same attachment.captures stored captured.represented heaps locals
      captured.agrees captured.typed reference read allocated initial ready
  have located := CellAwareGeneralizedDeclaration.framed_after_allocation allocation
    (congrArg SourceCoreBasic.LoweredExpr.type receipt.original.emitted)
    attachment heaps rows frames registered markerTyped (native := origin.native) allocated
  exact ⟨values, marker, CellAwareGeneralizedDeclaration.sequence_agreement initialized allocatedNative,
    fun completed => CellAwareGeneralizedContinuation.smaller initialized allocatedNative completed,
    environments, finalHeaps, finalLocals, agrees, typed, finalReference, finalRead, preserved, located, transition⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedPrefix
