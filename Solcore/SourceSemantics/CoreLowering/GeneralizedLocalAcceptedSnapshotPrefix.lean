import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedPrefix
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.StagedProjected

/-! An accepted generalized declaration snapshots its scope. The compiler's
request Source copies the same identifiers as the runtime Source; the marked
copies wrap the bundle initializer and the marked descriptor allocation, so the
principal and its marker capture the copies, while the continuation keeps the
original cells. The copies, the bundle and the allocation form one two-way
continuation boundary for any accepted candidate body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedSnapshotPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open TypedLexicalWhile (initializedRequest)
open GeneralizedLocalDescriptorHeap GeneralizedLocalLocatedRows
open GeneralizedLocalInstanceCompilation (Inputs)
open CellAwareGeneralizedSnapshotCode (snapshotInner snapshotSequence)
open SourceSemantics.CaptureBinders (copiedBinder?)

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
    {captured : Expr}
    (copied : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.ancestry.layout.frame
        prepared.base.globals.length
        (prepared.layouts.allocatorAt inputs.current.owner lexical (fun error => .sourceAllocation (reprStr error)))))
      allocationSource inputs.scope (fun index => index)
      (snapshotInner lowered.type lowered.expression annotation.expression) = .ok captured)
    (copiedIds : ∀ id, (copiedBinder? allocationSource id).isSome = (copiedBinder? function.source id).isSome)
    {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog checked.catalog) protocol prepared.layouts
      prepared.ancestry.layout.frame (cellModel model (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment)))
    (transitions : ProtectedStateTransition.AdministrativeTransitions protocol)
    (bindings : ProtectedStateTransition.Bindings protocol)
    (registered : prepared.ancestry.layout.frame.Registered prepared.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {actual : Core.Environment}
    (current : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope environment actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ current.administrative)
      lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
    {before snapshotHeap after : Dynamic.Heap} {store : Store} {sourceLocation : Dynamic.Location}
    {frameLocation : Core.Location}
    (heaps : GenericHeap.CellHeapRepresents
      (cellModel model (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.definitionContext.locals environment)
    (reference : current.canonical[inputs.scope.length + 1 + prepared.base.globals.length]? =
      some (.cellRef prepared.ancestry.layout.frame.type frameLocation))
    (index : SourceCoreCallableIndexedAncestry.creationReferenceIndex inputs.current inputs.scope =
      inputs.scope.length + 1 + prepared.base.globals.length)
    (read : store.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native))
    (snapshot : Dynamic.EnvironmentCopies function.source environment before function.captured snapshotHeap)
    (allocated : Dynamic.Heap.AllocatesGeneralized snapshotHeap function sourceLocation after)
    (initial : protocol.State ⟨inputs.scope, mapping, world, before, store, current.canonical⟩)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer frameLocation origin.native)
    (output : Ty) (body : Expr) :
    ∃ values marker, ∃ (copiedStore : Store) (copiedMap : LocationMap) (copiedWorld : StoreTyping),
      let bundle := SourceCoreLocalPolymorphism.ProductBundle.value values
      let nextStore := copiedStore ++ [SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit bundle]
      let nextWorld := copiedWorld ++ [prepared.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]
      let nextMap := copiedMap ++ [copiedStore.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)
      ContinuationAgreement actual store ((snapshotSequence output captured body).rename current.embedding)
        (nextRef :: actual) nextStore (body.rename current.embedding.lift) ∧
      (∀ {size value finalStore},
        EvaluationSize size actual store ((snapshotSequence output captured body).rename current.embedding)
          value finalStore →
        ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (nextRef :: actual) nextStore
          (body.rename current.embedding.lift) value finalStore) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) nextMap nextWorld current.administrative
        ((function.binder.id, lowered.type) :: inputs.scope)
        ((function.binder.id, sourceLocation) :: environment) (nextRef :: current.canonical) prepared.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after context.locals ((function.binder.id, sourceLocation) :: environment) ∧
      EnvironmentsAgree current.embedding.lift (nextRef :: current.canonical) (nextRef :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: actual)
        (OptionalCell.referenceType lowered.type :: current.actualContext) prepared.layouts.definitions ∧
      (nextRef :: current.canonical)[((function.binder.id, lowered.type) :: inputs.scope).length + 1 + prepared.base.globals.length]? =
        some (.cellRef prepared.ancestry.layout.frame.type frameLocation) ∧
      nextStore.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      LocationMap.Extends mapping nextMap ∧ WorldExtends world nextWorld ∧ (∃ suffix, nextStore = store ++ suffix) ∧
      (∃ located : Located (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment) function binding lexical
        sourceLocation nextMap nextWorld after nextStore,
        GeneralizedLocalAcceptedLocatedRows.Located.FramesWith sourceAttachment located frameLocation) ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨(function.binder.id, lowered.type) :: inputs.scope, nextMap, nextWorld, after, nextStore,
          nextRef :: current.canonical⟩ := by
  have base : (fun index : Nat => index) = (· + ([] : Environment).length) := by
    funext index
    simp
  rw [base] at copied
  obtain ⟨copies, copiedHeap, copiedCanonical, copiedActual, copiedContext, copiedStore, copiedMap, copiedWorld,
      copiedEmbedding, copy, copiedEnvironments, slots, copiedHeaps, copiedMaps, copiedWorlds, copiedFrame,
      ⟨copiedSuffix, copiedStoreEq⟩, copiedRead, copiedLookups, copiedTypes, copiedTyped, copyAgreement⟩ :=
    CaptureCopies.marked_copies_prefix_cells (pre := []) (preContext := []) copied rfl registered
      current.represented heaps current.agrees rfl current.respects current.typed reference read
  obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional (copy.of_copiedIds copiedIds) snapshot
  let captures : CallableIndexedLambdaValues.Captures prepared copiedMap copiedWorld inputs.scope function.captured
      copiedActual :=
    ⟨current.administrative, copiedCanonical, copiedContext, copiedEmbedding, copiedEnvironments, copiedLookups,
      copiedTypes, copiedTyped⟩
  have copiedReference : copiedCanonical[inputs.scope.length + 1 + prepared.base.globals.length]? =
      some (.cellRef prepared.ancestry.layout.frame.type frameLocation) := by
    rw [slots _ (by omega)]
    exact reference
  obtain ⟨values, initialized, rows, frames, stored⟩ := GeneralizedLocalAcceptedInitializer.formation_with
    receipt sourceAttachment attached owner initializer origin attachment captures declarations ownership issuer
    nativeTyped copiedHeaps.runtime_hasTypes (index ▸ copiedReference) copiedRead
  let bundle := SourceCoreLocalPolymorphism.ProductBundle.value values
  have canonicalBound : inputs.scope.length < current.canonical.length :=
    Nat.lt_of_le_of_lt (by omega) (List.getElem?_eq_some_iff.mp reference).1
  have copiedBound : inputs.scope.length < copiedCanonical.length :=
    Nat.lt_of_le_of_lt (by omega) (List.getElem?_eq_some_iff.mp copiedReference).1
  obtain ⟨extendedState, extendedRelated⟩ :=
    transitions initial copiedMaps copiedWorlds copiedFrame snapshot.metadata_extends
  obtain ⟨copiedState, copiedRelated⟩ := bindings.rebind extendedState copiedCanonical
    (Nat.le_of_lt canonicalBound) (Nat.le_of_lt copiedBound) slots
  have canonicalLayout : EnvironmentsAgree
      (initializedRequest allocationSource inputs.scope function.binder lowered.type).references copiedCanonical
      (bundle :: copiedCanonical) := fun found => found
  have referenceAt : (bundle :: copiedCanonical)[SourceCoreCallableIndexedAllocationFrames.referenceIndex
      prepared.base.globals.length (initializedRequest allocationSource inputs.scope function.binder lowered.type)]? =
      some (.cellRef prepared.ancestry.layout.frame.type frameLocation) := by
    have named : SourceCoreCallableIndexedAllocationFrames.isNamedInput
        (initializedRequest allocationSource inputs.scope function.binder lowered.type) = false := ordinary
    change (bundle :: copiedCanonical)[Renaming.comp (Renaming.insertion 0) Renaming.id
      (inputs.scope.length + (if SourceCoreCallableIndexedAllocationFrames.isNamedInput
        (initializedRequest allocationSource inputs.scope function.binder lowered.type) then 0 else 1) +
          prepared.base.globals.length)]? = _
    rw [named]
    exact copiedReference
  obtain ⟨marker, _markerCaptures, markerTyped, evaluated, nextHeaps, nextReference, preservation, transition⟩ :=
    producer.complete allocation annotation same rfl registered copiedEnvironments canonicalLayout copiedHeaps
      referenceAt copiedRead (.initialized rfl rfl) (.generalized stored) (.generalized allocated) copiedState
      (ready copiedState copiedRead)
  have allocatedNative : Evaluates (bundle :: copiedActual) copiedStore
      (annotation.expression.rename copiedEmbedding.lift)
      (.cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2))
      (copiedStore ++ [SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit bundle]) :=
    CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inr rfl) evaluated
      (copiedLookups.lift bundle)
  have located := GeneralizedLocalAcceptedPrefix.framed_after_allocation allocation
    (congrArg SourceCoreBasic.LoweredExpr.type receipt.original.emitted)
    attachment copiedHeaps rows frames registered markerTyped (native := origin.native) allocated
  have innerShape : (snapshotInner lowered.type lowered.expression annotation.expression).rename copiedEmbedding =
      LanguageResult.bind (OptionalCell.referenceType lowered.type) (lowered.expression.rename copiedEmbedding)
        (LanguageResult.success (annotation.expression.rename copiedEmbedding.lift)) := rfl
  have innerEvaluated : Evaluates copiedActual copiedStore
      ((snapshotInner lowered.type lowered.expression annotation.expression).rename copiedEmbedding)
      (.inRight .word (.cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)))
      (copiedStore ++ [SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit bundle]) := by
    rw [innerShape]
    exact LanguageResult.bind_success _ initialized (LanguageResult.success_evaluates allocatedNative)
  have capturedEvaluated := copyAgreement.wrap innerEvaluated
  have outerShape : (snapshotSequence output captured body).rename current.embedding =
      LanguageResult.bind (LocalLoop.controlType output) (captured.rename current.embedding)
        (body.rename current.embedding.lift) := rfl
  have nextLocals : Dynamic.EnvironmentAgrees after context.locals ((function.binder.id, sourceLocation) :: environment) := by
    cases extended
    exact .cons allocated.reads_new
      (congrArg (fun retained : TypedBinder => retained.scheme.body) attachment.captures.binder_eq)
      (.generalized rfl (congrArg TypedBinder.id attachment.captures.binder_eq)
        (congrArg TypedBinder.scheme attachment.captures.binder_eq))
      (locals.mono (snapshot.metadata_extends.trans (.of_generalized_allocation allocated)))
  have finalSlots : ∀ slot, ((function.binder.id, lowered.type) :: inputs.scope).length ≤ slot →
      (Value.cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2) :: current.canonical)[slot]? =
        (Value.cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2) :: copiedCanonical)[slot]? := by
    intro slot above
    cases slot with
    | zero => simp at above
    | succ slot =>
      simp only [List.getElem?_cons_succ]
      exact (slots slot (by simpa using above)).symm
  obtain ⟨allocatedState, allocatedRelated⟩ := transition
  have requestScope : (initializedRequest allocationSource inputs.scope function.binder lowered.type).scope =
      inputs.scope := rfl
  obtain ⟨finalState, finalRelated⟩ := bindings.rebind allocatedState
    (Value.cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2) :: current.canonical)
    (by simp only [List.length_cons, requestScope]; omega) (by simp only [List.length_cons, requestScope]; omega)
    finalSlots
  refine ⟨values, marker, copiedStore, copiedMap, copiedWorld, ?_, ?_,
    CallableIndexedOrdinaryAllocation.bind_environment (current.represented.extend copiedMaps copiedWorlds)
      nextReference,
    nextHeaps, nextLocals, ReadOnly.EnvironmentsAgree.lift current.agrees _,
    .cons (.cellRef nextReference.typed) (current.typed.weaken (copiedWorlds.trans ⟨_, rfl⟩)), ?_, ?_,
    copiedFrame.trans preservation, copiedMaps.trans ⟨_, rfl⟩, copiedWorlds.trans ⟨_, rfl⟩,
    ⟨copiedSuffix ++ _, by rw [copiedStoreEq, List.append_assoc]⟩, located,
    ⟨finalState, protocol.trans extendedRelated (protocol.trans copiedRelated
      (protocol.trans allocatedRelated finalRelated))⟩⟩
  · rw [outerShape]
    exact ContinuationAgreement.bind capturedEvaluated
  · intro size value finalStore completed
    rw [outerShape] at completed
    exact completed.bind_success capturedEvaluated
  · have shifted : ((function.binder.id, lowered.type) :: inputs.scope).length + 1 + prepared.base.globals.length =
        (inputs.scope.length + 1 + prepared.base.globals.length) + 1 := by simp; omega
    rw [shifted]
    exact reference
  · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp copiedRead).1).trans copiedRead

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedSnapshotPrefix
