import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerMeaning
import Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation

/-! A generalized declaration joins the actual ordered bundle initializer to
marked cell allocation. Its continuation retains the new lexical reference,
the native bundle temporary and the exact Source descriptor. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedDeclaration
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open TypedLexicalWhile (initializedRequest sequence)
open GeneralizedLocalDescriptorHeap GeneralizedLocalLocatedRows

/-- Source typing of a captured principal descriptor and its actual allocation
provide the next lexical admission. No initializer execution is postulated. -/
theorem admitted_after_allocation
    {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
    {caller : ProtectedStateTransition.Protocol (CallableIndexedOwnedFunctionState.Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) caller)
    {initial reached : ProtectedStateTransition.Index}
    (first : caller.State initial) (last : caller.State reached)
    {source : TypedSource} {context nextContext : SourceSemantics.Context} {binder : TypedBinder}
    {function : Dynamic.GeneralizedClosure} {location : Dynamic.Location}
    (admitted : CallableIndexedOwnedSourceAdmission.Admission bridge context first)
    (extended : BinderExtends source.owner context binder nextContext)
    (typed : Dynamic.GeneralizedClosureWellTyped context initial.heap function)
    (allocated : Dynamic.Heap.AllocatesGeneralized initial.heap function location reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    CallableIndexedOwnedSourceAdmission.Admission bridge nextContext last :=
  ⟨(Dynamic.HeapWellTyped.iff_of_binderExtends extended).mp
      (admitted.heap.allocateGeneralized typed allocated),
    CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
      (bridge.pool first) (bridge.pool last) admitted.rows frame⟩

/-- The two original emitted actions reach the real body continuation in both
directions. The hidden initializer value remains below the lexical reference. -/
theorem sequence_agreement {actual : Environment} {store nextStore : Store}
    {embedding : Renaming} {initializer allocation body : Expr} {output : Ty}
    {value reference : Value}
    (initialized : Evaluates actual store (initializer.rename embedding) (.inRight .word value) store)
    (allocated : Evaluates (value :: actual) store (allocation.rename embedding.lift) reference nextStore) :
    ContinuationAgreement actual store ((sequence output initializer allocation body).rename embedding)
      (reference :: value :: actual) nextStore
      (body.rename (Renaming.comp (Renaming.insertion 0) embedding).lift) := by
  have bodyEq : (body.weakenAt 1).rename embedding.lift.lift =
      body.rename (Renaming.comp (Renaming.insertion 0) embedding).lift := by
    rw [← Expr.rename_insertion, Expr.rename_comp]
    congr 1
    funext index
    cases index <;> rfl
  have combined : ContinuationAgreement actual store
      (LanguageResult.bind (LocalLoop.controlType output) (initializer.rename embedding)
        (.letE (allocation.rename embedding.lift) ((body.weakenAt 1).rename embedding.lift.lift)))
      (reference :: value :: actual) nextStore ((body.weakenAt 1).rename embedding.lift.lift) :=
    (ContinuationAgreement.bind initialized).trans (ContinuationAgreement.letE allocated)
  simpa only [sequence, CompatibleStatementInitialized.sequence, LanguageResult.bind, Expr.rename,
    bodyEq, Renaming.lift] using combined

/-- Genuine marked allocation exposes its newly installed ordered row. The
snapshot and marker types come from the same allocator receipt and captures. -/
theorem located_after_allocation {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {ordinary : GenericHeap.PayloadModel catalog projects prepared.layouts.definitions}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request}
    (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts owner active request)
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : TypeSystem.Substitution} {values : List Value}
    (payload : request.payloadType = binding.bundleType lexical)
    (attachment : Attachment (GeneralizedLocalInstanceValues.model prepared) function binding lexical)
    {mapping : LocationMap} {world : StoreTyping} {heap after : Dynamic.Heap} {store : Store}
    (heaps : GenericHeap.CellHeapRepresents
      (cellModel ordinary (GeneralizedLocalInstanceValues.model prepared)) mapping world heap store)
    (rows : SourceCoreLocalPolymorphism.ProductBundle.Pointwise
      (GeneralizedLocalInstanceValues.Represents prepared mapping world function binding lexical)
      (binding.atContext lexical) values)
    {native : NativeFrame} {captured : Value} {location : Dynamic.Location}
    (registered : prepared.ancestry.layout.frame.Registered prepared.layouts.definitions)
    (capturedTyped : RuntimeValueHasType world captured (SourceCoreSourceCells.captureType request.scope)
      prepared.layouts.definitions)
    (allocated : Dynamic.Heap.AllocatesGeneralized heap function location after) :
    Nonempty (Located (GeneralizedLocalInstanceValues.model prepared) function binding lexical location
      (mapping ++ [store.length + 2])
      (world ++ [prepared.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType request.payloadType]) after
      (store ++ [SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
        .inRight .unit (SourceCoreLocalPolymorphism.ProductBundle.value values)])) := by
  have captureType : allocation.entry.layout.captureType = SourceCoreSourceCells.captureType request.scope := by
    change SourceCoreSourceCells.captureType allocation.entry.key.scope = _
    rw [allocation.keyExact]
    rfl
  have markerTyped : RuntimeValueHasType world (SourceCoreHeapMarkers.markerValue allocation.entry.layout captured)
      allocation.entry.layout.type prepared.layouts.definitions :=
    .constructed allocation.registered.payloadLookup (captureType.symm ▸ capturedTyped)
  have result := (GeneralizedLocalLocatedRows.of_marked_allocation heaps attachment rows
    (SourceCoreCallableIndexedFrames.encode_runtime_typed world registered native) markerTyped allocated).2
  simpa only [payload] using result

theorem framed_after_allocation {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {ordinary : GenericHeap.PayloadModel catalog projects prepared.layouts.definitions}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request}
    (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts owner active request)
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : TypeSystem.Substitution} {values : List Value}
    (payload : request.payloadType = binding.bundleType lexical)
    (attachment : Attachment (GeneralizedLocalInstanceValues.model prepared) function binding lexical)
    {mapping : LocationMap} {world : StoreTyping} {heap after : Dynamic.Heap} {store : Store}
    (heaps : GenericHeap.CellHeapRepresents
      (cellModel ordinary (GeneralizedLocalInstanceValues.model prepared)) mapping world heap store)
    (rows : SourceCoreLocalPolymorphism.ProductBundle.Pointwise
      (GeneralizedLocalInstanceValues.Represents prepared mapping world function binding lexical)
      (binding.atContext lexical) values)
    {frameLocation : Core.Location}
    (frames : SourceCoreLocalPolymorphism.ProductBundle.Pointwise
      (GeneralizedLocalInstanceValues.Framed prepared mapping world function binding lexical frameLocation)
      (binding.atContext lexical) values)
    {native : NativeFrame} {captured : Value} {location : Dynamic.Location}
    (registered : prepared.ancestry.layout.frame.Registered prepared.layouts.definitions)
    (capturedTyped : RuntimeValueHasType world captured (SourceCoreSourceCells.captureType request.scope)
      prepared.layouts.definitions)
    (allocated : Dynamic.Heap.AllocatesGeneralized heap function location after) :
    ∃ located : Located (GeneralizedLocalInstanceValues.model prepared) function binding lexical location
      (mapping ++ [store.length + 2])
      (world ++ [prepared.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType request.payloadType]) after
      (store ++ [SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
        .inRight .unit (SourceCoreLocalPolymorphism.ProductBundle.value values)]), located.Frames frameLocation := by
  have captureType : allocation.entry.layout.captureType = SourceCoreSourceCells.captureType request.scope := by
    change SourceCoreSourceCells.captureType allocation.entry.key.scope = _
    rw [allocation.keyExact]
    rfl
  have markerTyped : RuntimeValueHasType world (SourceCoreHeapMarkers.markerValue allocation.entry.layout captured)
      allocation.entry.layout.type prepared.layouts.definitions :=
    .constructed allocation.registered.payloadLookup (captureType.symm ▸ capturedTyped)
  obtain ⟨located, sameValues⟩ := (GeneralizedLocalLocatedRows.of_marked_allocation_values heaps attachment rows
    (SourceCoreCallableIndexedFrames.encode_runtime_typed world registered native) markerTyped allocated).2
  have finalFrames : located.Frames frameLocation := by
    change SourceCoreLocalPolymorphism.ProductBundle.Pointwise _ _ _
    rw [sameValues]
    clear sameValues located rows
    generalize binding.atContext lexical = candidates at frames ⊢
    induction frames with
    | nil => exact .nil
    | cons head _ ih => exact .cons (head.extend ⟨_, rfl⟩ ⟨_, rfl⟩) ih
  rw [payload]
  exact ⟨located, finalFrames⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedDeclaration
