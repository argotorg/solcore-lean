import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.ReadBundles
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedLexicalControl
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.BodyReads
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Statements
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.CoreEvaluation
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LambdaViewsAndMarkedCaptures
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicStatements
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.OrdinaryBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateExpressions
import Solcore.SourceSemantics.Staging.Internal.TraceSize
import Solcore.SourceSemantics.Staging.Internal.SelectedPreservation
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StagedProjected
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.CellPlaces
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.PlaceAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.AssignmentHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceBitNot
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.RenamedPlaces
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceWriteback

/-!
# Cell-aware staged writes and generalized declarations

Staged projected assignments and bit-not updates in their prefix, resolution, commit and tail phases, and the allocation and continuation of generalized declarations.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedAllocation
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedDeclaration
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedContinuation
/-! The real emitted initializer and allocation expose a strictly smaller
native continuation, independently of the later Source grade. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedContinuation
open Core Frontend SourceInference ReadOnly CoreProof
open CompatibleStatementInitialized (sequence)

theorem smaller {actual : Environment} {store nextStore : Store}
    {embedding : Renaming} {initializer allocation body : Expr} {output : Ty}
    {value reference : Value}
    (initialized : Evaluates actual store (initializer.rename embedding) (.inRight .word value) store)
    (allocated : Evaluates (value :: actual) store (allocation.rename embedding.lift) reference nextStore)
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((sequence output initializer allocation body).rename embedding) result finalStore) :
    ∃ tailSize, tailSize < size ∧
      EvaluationSize tailSize (reference :: value :: actual) nextStore
        (body.rename (Renaming.comp (Renaming.insertion 0) embedding).lift) result finalStore := by
  have bodyEq : (body.weakenAt 1).rename embedding.lift.lift =
      body.rename (Renaming.comp (Renaming.insertion 0) embedding).lift := by
    rw [← Expr.rename_insertion, Expr.rename_comp]
    congr 1
    funext index
    cases index <;> rfl
  have combined : EvaluationSize size actual store
      (LanguageResult.bind (LocalLoop.controlType output) (initializer.rename embedding)
        (.letE (allocation.rename embedding.lift) ((body.weakenAt 1).rename embedding.lift.lift)))
      result finalStore := by
    simpa only [sequence, LanguageResult.bind,
      Expr.rename, Renaming.lift] using completed
  obtain ⟨branchSize, branchSmaller, branch⟩ := combined.bind_success initialized
  obtain ⟨tailSize, tailSmaller, tail⟩ := branch.let_body allocated
  exact ⟨tailSize, Nat.lt_trans tailSmaller branchSmaller, bodyEq ▸ tail⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedContinuation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedPrefix
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedSnapshotPrefix
/-! A generalized declaration snapshots its scope. The marked copies of the
captured cells wrap the bundle initializer and the marked descriptor
allocation, so the principal and its marker capture the copies, while the
continuation keeps the original cells. The copies, the bundle and the
allocation form one two-way continuation boundary. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedSnapshotPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open TypedLexicalWhile (initializedRequest)
open GeneralizedLocalDescriptorHeap GeneralizedLocalLocatedRows
open GeneralizedLocalInstanceCompilation (Inputs)
open CellAwareGeneralizedSnapshotCode (snapshotInner snapshotSequence)

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
    {captured : Expr}
    (copied : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.ancestry.layout.frame
        prepared.base.globals.length
        (prepared.layouts.allocatorAt inputs.current.owner lexical (fun error => .sourceAllocation (reprStr error)))))
      function.source inputs.scope (fun index => index)
      (snapshotInner lowered.type lowered.expression annotation.expression) = .ok captured)
    {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog checked.catalog) protocol prepared.layouts
      prepared.ancestry.layout.frame (cellModel model (GeneralizedLocalInstanceValues.model prepared)))
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
    (heaps : GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalInstanceValues.model prepared))
      mapping world before store)
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
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalInstanceValues.model prepared))
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
      (∃ located : Located (GeneralizedLocalInstanceValues.model prepared) function binding lexical sourceLocation
        nextMap nextWorld after nextStore, located.Frames frameLocation) ∧
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
  obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy snapshot
  let captures : CallableIndexedLambdaValues.Captures prepared copiedMap copiedWorld inputs.scope function.captured
      copiedActual :=
    ⟨current.administrative, copiedCanonical, copiedContext, copiedEmbedding, copiedEnvironments, copiedLookups,
      copiedTypes, copiedTyped⟩
  have copiedReference : copiedCanonical[inputs.scope.length + 1 + prepared.base.globals.length]? =
      some (.cellRef prepared.ancestry.layout.frame.type frameLocation) := by
    rw [slots _ (by omega)]
    exact reference
  obtain ⟨values, initialized, rows, frames, stored⟩ := GeneralizedLocalInitializerMeaning.formation
    receipt descriptorSource owner initializer origin namedLexical namedMetadata attachment captures declarations
    ownership issuer nativeTyped copiedHeaps.runtime_hasTypes (index ▸ copiedReference) copiedRead
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
      (initializedRequest function.source inputs.scope function.binder lowered.type).references copiedCanonical
      (bundle :: copiedCanonical) := fun found => found
  have referenceAt : (bundle :: copiedCanonical)[SourceCoreCallableIndexedAllocationFrames.referenceIndex
      prepared.base.globals.length (initializedRequest function.source inputs.scope function.binder lowered.type)]? =
      some (.cellRef prepared.ancestry.layout.frame.type frameLocation) := by
    have named : SourceCoreCallableIndexedAllocationFrames.isNamedInput
        (initializedRequest function.source inputs.scope function.binder lowered.type) = false := ordinary
    change (bundle :: copiedCanonical)[Renaming.comp (Renaming.insertion 0) Renaming.id
      (inputs.scope.length + (if SourceCoreCallableIndexedAllocationFrames.isNamedInput
        (initializedRequest function.source inputs.scope function.binder lowered.type) then 0 else 1) +
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
  have located := CellAwareGeneralizedDeclaration.framed_after_allocation allocation
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
  have requestScope : (initializedRequest function.source inputs.scope function.binder lowered.type).scope =
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

end Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedSnapshotPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedSourceInversion
/-! A genuine generalized Source declaration exposes the copies of its
environment, its retained descriptor over the copies and its allocation
directly. Its graded tail starts at the extended lexical context, over the
original environment, without executing the principal initializer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedSourceInversion
open Frontend SourceInference Staging.Recursive

private theorem statement_shape {source : TypedSource} {id : StatementId}
    {node : StatementNode} {form : StatementForm}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (same : node.form = form) :
    ∀ {other}, ContainsStatement source id other → other.form = form := by
  intro other present
  have nodeEq : other = node := Option.some.inj ((lookupStatement?_complete unique present).symm.trans found)
  cases nodeEq
  exact same

private theorem extension_unique {owner : Resolved.DeclarationId}
    {context first second : SourceSemantics.Context} {binder : TypedBinder}
    (left : BinderExtends owner context binder first)
    (right : BinderExtends owner context binder second) : first = second := by
  cases left
  cases right
  rfl

theorem generalized {program : Program} {registry : Registry} {mode : Bool} {invocation : Scope}
    {context nextContext finalContext : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {binder : TypedBinder} {initializer : ExpressionId} {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder (some initializer))
    (polymorphic : binder.scheme.quantified ≠ [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : Size.StatementsIn program registry mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    ∃ tailSize captured snapshotHeap function location bound,
      size = Size.stepSize [tailSize] ∧
      Dynamic.EnvironmentCopies invocation.source environment before captured snapshotHeap ∧
      Dynamic.GeneralizedClosureCaptures context invocation.source captured binder initializer function ∧
      Dynamic.Heap.AllocatesGeneralized snapshotHeap function location bound ∧
      Size.StatementsIn program registry mode tailSize invocation nextContext
        ((binder.id, location) :: environment) bound rest finalContext outcome after := by
  have shape := @statement_shape _ _ _ _ unique found form
  cases trace with
  | letGeneralized actual same snapshot captures _ actualExtended allocated remaining =>
      have equal := (shape actual).symm.trans same
      cases equal
      have contexts := extension_unique extended actualExtended
      cases contexts
      exact ⟨_, _, _, _, _, _, rfl, snapshot, captures, allocated, remaining⟩
  | letInitialized actual same _ mono _ _ _ | letFault actual same mono _ =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact False.elim (polymorphic mono)
  | breaking actual same | continuing actual same =>
      cases (shape actual).symm.trans same
  | bitNotProjected actual same _ _ _ _ _
  | bitNotProjectedRootFault actual same _ _
  | bitNotProjectedKeysFault actual same _ _ _
  | bitNotProjectedGetterFault actual same _ _ _
  | bitNotBare actual same _ _ _ | bitNotBareFault actual same _ _
  | assignProjected actual same _ _ _ _ _ _
  | assignProjectedRootFault actual same _ _
  | assignProjectedKeysFault actual same _ _ _
  | assignProjectedGetterFault actual same _ _ _
  | assignProjectedRhsFault actual same _ _ _ _
  | assignProjectedWriteFault actual same _ _ _ _ _
  | assignBare actual same _ _ _ _ | assignBareOperands actual same _ _ _ _ _ _ _ | assignBareFault actual same _ _
  | assignBareUnbound actual same _ _ | assignBareDangling actual same _ _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | returnUnit actual same | returnValue actual same _ | returnFault actual same _
  | tail actual same _ | discard actual same _ _ | discardValue actual same _ _ | expressionFault actual same _
  | forInitializerFault actual same _ | forReturned actual same _ _ | forFault actual same _ _
  | forFallthrough actual same _ _ _
  | matchBreaking actual same _ | matchContinuing actual same _
  | matchReturned actual same _ | matchFault actual same _ | matchFallthrough actual same _ _
  | blockBreaking actual same _ | blockContinuing actual same _
  | blockReturned actual same _ | blockFault actual same _ | blockFallthrough actual same _ _
  | whileReturned actual same _ | whileFault actual same _ | whileFallthrough actual same _ _
  | ifConditionFault actual same _ | ifBreaking actual same _ _ | ifContinuing actual same _ _
  | ifReturned actual same _ _ | ifFault actual same _ _
  | ifFallthrough actual same _ _ _
  | letUninitialized actual same _ _ _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible

/-- The actual checked statement supplies principal closure typing at the
current heap. It is obtained before any native instance body is called. -/
theorem captured_wellTyped {program : Program} {source : TypedSource}
    {context finalContext : SourceSemantics.Context} {control : ControlContext}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {binder : TypedBinder} {initializer : ExpressionId}
    {function : Dynamic.GeneralizedClosure} {facts : StatementFacts}
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (typed : StatementHasType source control context id finalContext facts)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder (some initializer))
    (polymorphic : binder.scheme.quantified ≠ [])
    (captures : Dynamic.GeneralizedClosureCaptures context source environment binder initializer function) :
    Dynamic.GeneralizedClosureWellTyped context heap function := by
  have shape := SelectedPreservation.statement_form runtime.graph.nodeOccurrencesUnique typed
    (lookupStatement?_sound found) form
  cases shape with
  | letInitialized _ mono _ => exact False.elim (polymorphic mono)
  | letInitializedGeneralized poly requirements generalizes value extension =>
    exact captures.wellTyped runtime locals poly requirements generalizes value extension

/-- Every lexical cell of an agreeing environment can be copied: a declaration
snapshot exists before its actual copies are fixed. -/
theorem copies_exist (source : TypedSource) {environment : Dynamic.Environment} :
    ∀ {scope : Resolved.LocalScope TypeSystem.Scheme} {heap : Dynamic.Heap},
      Dynamic.EnvironmentAgrees heap scope environment →
      ∃ copies after, Dynamic.EnvironmentCopies source environment heap copies after := by
  induction environment with
  | nil => intro _ heap _; exact ⟨[], heap, .nil heap⟩
  | cons entry rest ih =>
    intro scope heap agrees
    cases agrees with
    | @cons scope environment id scheme location cell read _ _ tail =>
      cases copied : CaptureBinders.copiedBinder? source id with
      | none =>
        obtain ⟨copies, after, copy⟩ := ih tail
        exact ⟨_, after, .shared copied copy⟩
      | some binder =>
        have allocate : Dynamic.Heap.AllocatesCopy heap cell ⟨heap.cells.length⟩ ⟨heap.cells ++ [cell]⟩ := .append
        obtain ⟨copies, after, copy⟩ := ih (tail.mono (Dynamic.HeapTypesExtend.of_copy allocate))
        exact ⟨_, after, .copied copied read allocate copy⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedSourceInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedResolution
/-! A successful staged key row supplies the actual native key execution.
The pure getter uses the reached live root and the same saved projection keys. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedResolution
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceLiveRoot
open CompatiblePlaceResolution CompatibleRenamedPlace
open CompatibleCellPlaceResolution
universe u v

private theorem path_length {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf) : steps.length = projections.length := by
  induction path with
  | nil => rfl
  | member _ _ _ _ ih | index _ _ _ ih => exact congrArg Nat.succ ih

private theorem shape_length {projections : List PlaceProjection} {sources : List Dynamic.Value}
    {resolved : List Dynamic.EvaluatedProjection} (shape : DataPlaceKeyOrder.Values projections sources resolved) :
    resolved.length = projections.length := by
  induction shape with
  | nil => rfl
  | member _ ih | index _ ih => exact congrArg Nat.succ ih

private theorem read_present {root : Dynamic.Value} {projections : List Dynamic.EvaluatedProjection}
    {selected : Option Dynamic.Value} (read : Dynamic.ProjectionsRead (some root) projections selected) :
    ∃ value, selected = some value := by
  generalize initialEq : some root = initial at read
  induction read generalizing root with
  | nil => exact ⟨root, initialEq.symm⟩
  | indexFound _ _ ih | indexDefault _ _ _ ih | member _ _ ih => exact ih rfl

theorem preserves {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {context : SourceSemantics.Context}
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (path : PreparedPath compilation.checked source site prepared.route.rootSourceType place.projections
      0 prepared.steps prepared.keys leaf)
    (views : KeyViews path sourceTypes)
    (keyTypes : prepared.keyTypes = codes.map (·.type))
    (leafProjected : compilation.checked.catalog.project leaf = .ok prepared.route.leafType)
    (virtual : ∀ key value, prepared.route.rootSourceType = .mapping key value →
      CompatibleMapping.VirtualRoot.Generated compilation prepared.route key value)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (nonempty : prepared.steps ≠ [])
    (getterTyped : HasType ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
        actualContext)
      (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
      (LanguageResult.resultType prepared.optionalLeaf) ambient.definitions)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {sourceTarget : Dynamic.ResolvedPlace} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    {sources : List Dynamic.Value}
    (keysMeaning : ∀ target,
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target) →
      RuntimeEnvironmentHasTypes world
        (.cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (OptionalCell.referenceType prepared.route.rootType :: actualContext) ambient.definitions →
      ∃ values keyStore keyMap keyWorld,
        Evaluates (.cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment) store
          ((SourceCoreCalls.packArguments codes).expression.rename (DataPlaceChildExpressions.prefixRenaming 1 ξ))
          (.inRight .word (packValues values)) keyStore ∧
        DataExpressionSequence.Values (payloadModel compilation.checked registry functions) keyMap keyWorld
          sourceTypes (codes.map (·.type)) sources values ∧
        GenericHeap.CellHeapRepresents cells keyMap keyWorld after keyStore ∧
        LocationMap.Extends mapping keyMap ∧ WorldExtends world keyWorld ∧
        AdministrativePreserved mapping store keyMap keyStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Dynamic.ValuesHaveTypes context after sources sourceTypes ∧ Dynamic.HeapWellTyped context after ∧
        CellAwareScopeAuthority.Effect instances mapping world before store keyMap keyWorld after keyStore ∧
        ProtectedStateTransition.Transition protocol initialState ⟨scope, keyMap, keyWorld, after, keyStore, canonical⟩)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before after place sources sourceTarget) :
    ∃ execution : CompatibleCellPlaceResolution.Execution compilation.checked registry functions cells instances prepared (renamedCodes codes ξ) sourceTypes place leaf sourceTarget
      coreEnvironment store mapping world before after,
      execution.sources = sources ∧
      Dynamic.ValuesHaveTypes context after sources sourceTypes ∧ Dynamic.HeapWellTyped context after ∧
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) execution.target) ∧
      ProtectedStateTransition.Transition protocol initialState ⟨scope, execution.mapping, execution.world, after, execution.store, canonical⟩ := by
  cases snapshot with
  | @intro sourceLocation initialCell currentCell projections initial selected lookup initialRead ordered currentRead initialValue selection =>
    have shaped := ordered.to_data
    obtain ⟨target, coreLookup, reference⟩ := environments.lookup_visible lookup slot
    obtain ⟨values, keyStore, keyMap, keyWorld, keyEvaluated, keysRelated,
      keyHeaps, keyMaps, keyWorlds, keyFrame, metadata, sourceValues, sourceHeap, keyEffect, keyPost⟩ :=
      keysMeaning target (agrees coreLookup) (.cons (.cellRef reference.typed) actualTyped)
    have keyEvaluation : Evaluates (referenceEnvironment prepared.route.rootType target coreEnvironment) store
        (shift 1 (SourceCoreCalls.packArguments (renamedCodes codes ξ)).expression) (.inRight .word (packValues values)) keyStore := by
      simpa only [DataPlaceChildExpressions.rename_prefix, packed_renamed_expression, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using keyEvaluated
    obtain ⟨scheme, staticLookup, _, monomorphic, bodyEq⟩ := rootTyped.scheme
    obtain ⟨staticLocation, staticCell, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
    have locationEq := lookup.functional staticLookupRuntime
    subst staticLocation
    have cellEq := initialRead.functional staticRead
    subst staticCell
    obtain ⟨updated, updatedRead, updatedType, _⟩ := metadata _ _ initialRead
    have currentEq := currentRead.functional updatedRead
    subst updated
    have rootType : currentCell.type = prepared.route.rootSourceType := updatedType.trans (staticCellType.trans bodyEq)
    have currentOrdinary := (locals.mono metadata).descriptor_empty_of_monomorphic
      sourceHeap staticLookup lookup currentRead monomorphic
    have currentReference := reference.extend keyMaps keyWorlds
    have arguments := views.arguments shaped keysRelated (fun _ _ found => by simpa only [Nat.zero_add] using found)
    have keyLength : prepared.keyTypes.length = values.length := keyTypes ▸ keysRelated.length.2
    have typedEnvironment : RuntimeEnvironmentHasTypes keyWorld
        (keysEnvironment prepared.route.rootType target (packValues values) coreEnvironment)
        ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
          actualContext) ambient.definitions :=
      .cons (values_typed keysRelated)
        (.cons (.cellRef currentReference.typed) (actualTyped.weaken keyWorlds))
    have resolvedNonempty : projections ≠ [] := by
      intro empty
      have length := (path_length path).trans (shape_length shaped).symm
      rw [empty, List.length_nil] at length
      exact nonempty (List.eq_nil_of_length_eq_zero length)
    have present : ∃ sourceRoot, initial = some sourceRoot := by
      cases initial with
      | some value => exact ⟨value, rfl⟩
      | none => cases selection with | nil => exact (resolvedNonempty rfl).elim
    obtain ⟨sourceRoot, rfl⟩ := present
    obtain ⟨selectedValue, rfl⟩ := read_present selection
    have rootExists : ∃ optional rootValue,
        RootRead compilation.checked registry functions keyMap keyWorld prepared after keyStore sourceLocation target
          currentCell optional sourceRoot rootValue := by
      cases currentCell with
      | mk cellType cellValue descriptor =>
       cases currentOrdinary
       cases initialValue with
       | initialized =>
        obtain ⟨value, root⟩ := CompatibleCellPlaceRoot.initialized_root ordinaryCells keyHeaps currentReference currentRead
        exact ⟨_, value, root⟩
       | emptyMapping key value =>
        obtain ⟨native, root⟩ := CompatibleCellPlaceRoot.virtual_root ordinaryCells keyHeaps currentReference currentRead (virtual key value rootType.symm) registryExtension
        exact ⟨_, native, root⟩
    obtain ⟨optional, rootValue, root⟩ := rootExists
    have represented : ValueRep compilation.checked registry functions keyMap keyWorld
        prepared.route.rootSourceType sourceRoot rootValue prepared.route.rootType := by
      simpa only [← rootType] using root.payload
    have tree := arguments.readTree represented leafProjected selection prepared
    have tree : CompatibleMapping.MixedPaths.ReadTree compilation.checked registry functions keyMap keyWorld prepared values
        leaf prepared.route.leafType currentCell.type sourceRoot rootValue prepared.steps projections selectedValue
        (readCost compilation.checked prepared.steps) := by simpa only [rootType] using tree
    obtain ⟨snapshot, finalStore, administrative, _, _, related, evaluated, appended, _⟩ :=
      readTree_at root tree nonempty faithful observations keyLength
        (keysEnvironment prepared.route.rootType target (packValues values) coreEnvironment)
        (SourceCoreCalls.packArguments codes).type (.var 1) (.var 0) (.var rfl) (.var rfl)
    obtain ⟨finalWorld, extension, finalHeaps, _, frame⟩ :=
      CellMappingHeap.evaluation_preserves_frame keyHeaps typedEnvironment getterTyped evaluated appended
    obtain ⟨keyState, keyRelated⟩ := keyPost
    refine ⟨{ target := target
              sources := sources
              values := values
              selected := selectedValue
              snapshot := snapshot
              keyStore := keyStore
              store := finalStore
              mapping := keyMap
              world := finalWorld
              selectedEq := rfl
              currentCell := currentCell
              currentRead := currentRead
              ordinary := currentOrdinary
              currentType := rootType
              reference := currentReference.extend (.refl _) extension
              shaped := shaped
              keysEvaluated := keyEvaluation
              snapshotEvaluated := by simpa only [packed_renamed_type] using evaluated
              keysRelated := by simpa only [renamedCodes_types] using keysRelated.extend (.refl _) extension
              snapshotRelated := related.extend (.refl _) (.refl _) extension
              heaps := finalHeaps
              maps := keyMaps
              worlds := keyWorlds.trans extension
              frame := keyFrame.trans frame
              metadata := metadata
              effect := keyEffect.trans (appended.symm ▸ CellAwareScopeAuthority.Effect.append
                keyStore administrative (.refl after) (.refl keyMap) extension) }, rfl, sourceValues, sourceHeap, agrees coreLookup,
      transport.extend keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after),
      protocol.trans keyRelated (transport.related keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after))⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedResolution
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedTail
/-! Native writeback reflection keeps the already established staged keys and
RHS outside its pure suffix. Its result is the real latest-root write or the
structural fault at that RHS heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedTail
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces DataPlaceExecution
open CompatiblePlaceTailReflection CompatibleRenamedPlace
universe u v

inductive ResultAt {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records) (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (cells : GenericHeap.CellModel ambient.definitions)
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions) (faults : FaultRep)
    (prepared : Prepared) (keyType : Ty) (actualContext : Core.Context)
    (operator : Syntax.ValueAssignOp) (target : Dynamic.ResolvedPlace) (right : Dynamic.Value) (rhsHeap : Dynamic.Heap)
    (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (scope : SourceCoreLocalCell.Scope) (canonical : Environment)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (next : Expr) (outputType : Ty) (result : Value) (finalStore : Store) : Prop where
  | fault {reason : Dynamic.SemanticFault} {token : Word}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : Staging.Recursive.ProjectedTarget.WriteFault operator target right rhsHeap reason)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : GenericHeap.CellHeapRepresents cells finalMap finalWorld rhsHeap finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before rhsHeap)
      (effect : CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld rhsHeap finalStore)
      (post : ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, rhsHeap, finalStore, canonical⟩) :
      ResultAt protocol size checked registry functions cells instances faults prepared keyType actualContext operator target right rhsHeap coreEnvironment
        before store mapping world scope canonical initialState next outputType result finalStore
  | committed {remainingSize : Nat} {updated : Dynamic.Value} {after : Dynamic.Heap} {written : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (trace : Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement) rhsHeap target updated after)
      (heaps : GenericHeap.CellHeapRepresents cells finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after written)
      (length : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ coreEnvironment)
        (CompatibleRenamedPlaceSuccess.writtenContext prepared keyType actualContext) ambient.definitions)
      (post : ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, written, canonical⟩)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize (slots ++ coreEnvironment) written (shift 7 next) result finalStore) :
      ResultAt protocol size checked registry functions cells instances faults prepared keyType actualContext operator target right rhsHeap coreEnvironment
        before store mapping world scope canonical initialState next outputType result finalStore
private theorem resolved_type {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before targetHeap : Dynamic.Heap} {place : PlaceResolution} {target : Dynamic.ResolvedPlace}
    (trace : Dynamic.SourcePlaceResolves program context evidence source environment before place target targetHeap)
    {cell : Dynamic.Cell} (read : Dynamic.Heap.Reads targetHeap target.location cell) : target.rootType = cell.type := by
  cases trace with
  | intro _ _ _ currentRead _ _ => exact congrArg Dynamic.Cell.type (currentRead.functional read)

private theorem absent_initial {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions} {mapping : LocationMap} {world : StoreTyping}
    {cell : Dynamic.Cell} {optional : Value} {type : Ty}
    (related : GenericHeap.CellRepresents model mapping world cell optional type)
    (empty : cell.value = none) (notMapping : ¬ ∃ k v, cell.type = .mapping k v) :
    Dynamic.RootInitialValue cell none := by
  cases related with
  | initialized => cases empty
  | uninitialized => exact .uninitialized notMapping

theorem reflects {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (functionTypes : FunctionRuntimeViews functions)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before targetHeap : Dynamic.Heap} {store finalStore : Store}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    {target : Dynamic.ResolvedPlace}
    {sourceSize rhsSize size : Nat}
    (sourceTrace : SourceExecutionSize.SourcePlaceResolves program sourceSize context evidence source environment before place target targetHeap)
    (resolution : CompatibleCellPlaceResolution.Execution compilation.checked registry functions cells instances prepared (renamedCodes codes ξ) sourceTypes place leaf target
      coreEnvironment store mapping world before targetHeap)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (right : CompatibleCellPlaceRhsReflection.Execution compilation.checked registry functions cells instances program context evidence source faults environment
      prepared (renamedCodes codes ξ) sourceTypes place leaf target coreEnvironment store mapping world before targetHeap resolution rhs node lowered)
    (rhsTrace : SourceExecutionSize.ExpressionEvaluates program rhsSize context evidence source environment targetHeap rhs right.right right.heap)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (rhsState : protocol.State ⟨scope, right.mapping, right.world, right.heap, right.store, canonical⟩)
    (rhsRelated : protocol.Relates initialState rhsState)
    (missingFor : ProtectedPlaceReachedDiagnostics.MissingFor compilation.checked registry functions protocol
      source site place prepared leaf initialState faults)
    {next : Expr} {outputType : Ty} {invalid : Word} {result : Value}
    (completed : CoreProof.EvaluationSize size (rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
      (.inRight .unit resolution.snapshot) right.value coreEnvironment) right.store
      (CompatiblePlaceRhsReflection.remainder prepared (SourceCoreCalls.packArguments codes).type next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) invalid) result finalStore) :
    ResultAt protocol size compilation.checked registry functions cells instances faults
      prepared (SourceCoreCalls.packArguments codes).type actualContext operator target right.right right.heap coreEnvironment
      before store mapping world scope canonical initialState next outputType result finalStore := by
  have closed := virtual_closed layout ordinary
  have setterTyped := setter_typed layout closed (environment_respects environments.runtime_hasTypes actualTyped agrees)
  have snapshotRep := right.meaning.saved_snapshot
  have keyRep : DataExpressionSequence.Values (payloadModel compilation.checked registry functions) right.mapping right.world sourceTypes (codes.map (·.type)) resolution.sources resolution.values := by
    simpa only [renamedCodes_types] using resolution.keysRelated.extend right.meaning.maps right.meaning.worlds
  have reference := resolution.reference.extend right.meaning.maps right.meaning.worlds
  have arguments := layout.views.arguments resolution.shaped keyRep (fun _ _ found => by simpa only [Nat.zero_add] using found)
  have targetType := (resolved_type sourceTrace.sound resolution.currentRead).trans resolution.currentType
  obtain ⟨latest⟩ := right.meaning.latest
  have cellOrdinary : latest.cell.generalized = none := by
    obtain ⟨current, read, _, descriptor⟩ := right.meaning.metadata _ _ resolution.currentRead
    have same := latest.read.functional read
    exact same.symm ▸ descriptor.trans resolution.ordinary
  have cellType : latest.cell.type = target.rootType := latest.type.trans targetType.symm
  obtain ⟨replacement, replacementValue, replacementRep, applied, modified, _⟩ :=
    CompatiblePlaceModifier.initialized_success observations profile snapshotRep right.related
      (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
        (.inRight .unit resolution.snapshot) right.value coreEnvironment)
      (.var (index := 1) rfl) (.var (index := 0) rfl) right.store invalid
  cases completed with
  | caseLeft modifiedEvaluated failed =>
    obtain ⟨impossible, _⟩ := evaluation_deterministic modifiedEvaluated.sound modified
    cases impossible
  | caseRight modifiedEvaluated remaining =>
    obtain ⟨same, storeEq⟩ := evaluation_deterministic modifiedEvaluated.sound modified
    cases same
    subst_vars
    have typedEnvironment : RuntimeEnvironmentHasTypes right.world
        (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) right.value replacementValue coreEnvironment)
        (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
          OptionalCell.referenceType prepared.route.rootType :: actualContext)
        ambient.definitions :=
      .cons replacementRep.runtime_hasType (.cons right.related.runtime_hasType (.cons (.inRight snapshotRep.runtime_hasType)
        (.cons (CompatiblePlaceResolution.values_typed keyRep) (.cons (.cellRef reference.typed)
          (actualTyped.weaken (resolution.worlds.trans right.meaning.worlds))))))
    have currentPath : PreparedPath compilation.checked source site latest.cell.type place.projections 0 prepared.steps prepared.keys leaf :=
      latest.type ▸ layout.path
    have currentArguments : Arguments compilation.checked registry functions right.mapping right.world source site resolution.values
        currentPath target.projections := by simpa only [latest.type] using arguments
    have reflectSetter := fun {actual : Value} {after : Store}
        (ran : Evaluates (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
            (.inRight .unit resolution.snapshot) right.value replacementValue coreEnvironment) right.store
          (.apply (setter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0)))) actual after) =>
      CompatibleCellPlaceSetterReflection.reflects ordinaryCells cellOrdinary currentArguments replacementRep
        (fun k v same => layout.virtual k v (latest.type.symm.trans same))
        (fun nonmapping => ordinary (fun k v same => nonmapping k v (latest.type.trans same))) registryExtension layout.nonempty
        functionTypes faithful observations (layout.keyTypes ▸ keyRep.length.2) right.meaning.heaps reference latest.read
        typedEnvironment setterTyped (.var rfl) (.var rfl) (.var rfl) ran
    cases remaining with
    | caseLeft setterEvaluated failed =>
      obtain ⟨futureWorld, administrative, represented, finalHeaps, extension, frame, appended⟩ := reflectSetter setterEvaluated.sound
      have helperEffect := appended.symm ▸ CellAwareScopeAuthority.Effect.append
        (instances := instances) right.store administrative (.refl right.heap) (.refl right.mapping) extension
      cases represented with
      | @missing sourceRoot reason token count root fault receipt =>
        cases failed with
        | inLeft valueEvaluated =>
          cases valueEvaluated with
          | var found =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst_vars
            obtain ⟨optional, rootValue, live⟩ := CompatibleCellPlaceRoot.root_of_initial ordinaryCells
              right.meaning.heaps reference latest.read cellOrdinary root
              (fun k v same => layout.virtual k v (latest.type.symm.trans same)) registryExtension
            obtain ⟨otherToken, otherCount, otherReceipt, tree⟩ := currentArguments.faultTree live.payload fault prepared
            obtain ⟨rfl, rfl⟩ := receipt.functional otherReceipt
            let reached := transport.extend rhsState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl right.heap)
            have phaseRelated := transport.related rhsState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl right.heap)
            have witness : ProtectedPlaceReachedDiagnostics.MissingWitness compilation.checked registry functions protocol
                source site place prepared leaf initialState reached reason token :=
              ⟨⟨scope, right.mapping, right.world, right.heap, right.store, canonical⟩, rhsState,
                target.location, resolution.target, latest.cell, optional, sourceRoot, rootValue,
                resolution.values, target.projections, count, currentPath, rhsRelated, phaseRelated,
                rfl, rfl, rfl, extension, frame, live, latest.type, currentArguments, fault, receipt, tree⟩
            exact .fault (.structural latest.read cellType root fault) rfl
              (missingFor reached (protocol.trans rhsRelated phaseRelated) witness)
              finalHeaps (resolution.maps.trans right.meaning.maps) ((resolution.worlds.trans right.meaning.worlds).trans extension)
              ((resolution.frame.trans right.meaning.frame).trans frame) (resolution.metadata.trans right.meaning.metadata)
              ((resolution.effect.trans right.meaning.effect).trans helperEffect)
              ⟨reached, protocol.trans rhsRelated phaseRelated⟩
      | uninitialized empty notMapping nonempty =>
        have absent := absent_initial latest.related empty notMapping
        exact (DataPlaceSourceOrder.latest_uninitialized_impossible sourceTrace.sound rhsTrace.sound latest.read cellType absent nonempty).elim
    | caseRight setterEvaluated remaining =>
      rename_i helperStore helperType updatedValue
      obtain ⟨futureWorld, administrative, represented, helperHeaps, extension, helperFrame, appended⟩ := reflectSetter setterEvaluated.sound
      have helperEffect := appended.symm ▸ CellAwareScopeAuthority.Effect.append
        (instances := instances) right.store administrative (.refl right.heap) (.refl right.mapping) extension
      cases represented with
      | updated root changed updatedRep =>
        cases remaining with
        | letE writeEvaluated continuation =>
          obtain ⟨after, resultEq, sourceWritten, finalHeaps, writeFrame, metadata, _, writeEffect⟩ :=
            CompatibleCellPlaceCommitReflection.reflects_storeCell ordinaryCells helperHeaps (reference.extend (.refl _) extension) latest.read cellOrdinary
              updatedRep (.var (index := 5) rfl) (.var (index := 0) rfl) writeEvaluated.sound
          subst_vars
          have changed := DataPlaceCommitReflection.update_of_replacement changed (fun _ => resolution.selectedEq.symm ▸ applied)
          let helperState := transport.extend rhsState (.refl _) extension helperFrame (Dynamic.HeapMetadataExtend.refl right.heap)
          exact .committed (.intro latest.read cellType root changed sourceWritten)
            finalHeaps (resolution.maps.trans right.meaning.maps) ((resolution.worlds.trans right.meaning.worlds).trans extension)
            (((resolution.frame.trans right.meaning.frame).trans helperFrame).trans writeFrame)
            ((resolution.metadata.trans right.meaning.metadata).trans metadata)
            (((resolution.effect.trans right.meaning.effect).trans helperEffect).trans writeEffect) (slots :=
              [.unit, updatedValue, replacementValue, right.value, .inRight .unit resolution.snapshot, packValues resolution.values,
                .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target]) rfl
              (by
                change RuntimeEnvironmentHasTypes futureWorld
                  (.unit :: updatedValue :: _) _ _
                exact .cons .unit (.cons updatedRep.runtime_hasType (typedEnvironment.weaken extension)))
              ⟨transport.extend helperState (.refl _) (.refl _) writeFrame metadata,
                protocol.trans (protocol.trans rhsRelated
                  (transport.related rhsState (.refl _) extension helperFrame (Dynamic.HeapMetadataExtend.refl right.heap)))
                  (transport.related helperState (.refl _) (.refl _) writeFrame metadata)⟩
              (by omega) continuation

end Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedTail
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedCommit
/-! The write phase consumes the genuine staged RHS output after successful
value erasure. It uses the saved leaf and rebuilds the current mapping root,
retaining all seven compiler-generated temporary slots. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedCommit
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceLiveRoot
open CompatiblePlaceAssignmentSuccess CompatibleRenamedPlace
open ProtectedPlaceAssignmentSuccess (writtenContext)
universe u v

private theorem resolved_nonempty {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf)
    {sources : List Dynamic.Value} {resolved : List Dynamic.EvaluatedProjection}
    (shaped : DataPlaceKeyOrder.Values projections sources resolved) (nonempty : steps ≠ []) : resolved ≠ [] := by
  have lengths : steps.length = resolved.length := by
    clear nonempty
    induction path generalizing sources resolved with
    | nil => cases shaped; rfl
    | member _ _ _ _ ih => cases shaped with | member tail => exact congrArg Nat.succ (ih tail)
    | index _ _ _ ih => cases shaped with | index tail => exact congrArg Nat.succ (ih tail)
  intro empty
  rw [empty, List.length_nil] at lengths
  exact nonempty (List.eq_nil_of_length_eq_zero lengths)

private theorem none_update {modify : Option Dynamic.Value → Dynamic.Value → Prop}
    {projections : List Dynamic.EvaluatedProjection} {updated : Dynamic.Value}
    (changed : Dynamic.ProjectionsUpdate modify none projections updated) : projections = [] := by
  cases changed
  rfl

/- An independent successful transaction constructs every native phase.
Raw metadata and duplicate entries are retained by the full payload relation;
the native store additionally contains tracked administrative helper cells. -/
theorem preserves {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (_rhsGenerated : certificate scope rhs lowered) (_found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before targetHeap rhsHeap after : Dynamic.Heap} {store : Store} {index : Nat}
    {sourceTarget : Dynamic.ResolvedPlace} {right updatedRoot : Dynamic.Value}
    {rhsStore : Store} {rhsMap : LocationMap} {rhsWorld : StoreTyping} {rightValue : Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (_heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (resolution : CompatibleCellPlaceResolution.Execution compilation.checked registry functions cells instances prepared (renamedCodes codes ξ)
      sourceTypes place leaf sourceTarget coreEnvironment store mapping world before targetHeap)
    (coreLookup : coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target))
    (resolutionState : protocol.State ⟨scope, resolution.mapping, resolution.world, targetHeap, resolution.store, canonical⟩)
    (resolutionRelated : protocol.Relates initialState resolutionState)
    (rhsResult : CompatibleCellPlaceRhs.Result (program := program) (context := context) (evidence := evidence) (source := source)
      (faults := faults) resolution rhs node (renamed lowered ξ) environment (.value right) rhsHeap
      (.inRight .word rightValue) rhsStore rhsMap rhsWorld)
    (rhsPost : ProtectedStateTransition.Transition protocol resolutionState ⟨scope, rhsMap, rhsWorld, rhsHeap, rhsStore, canonical⟩)
    (written : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.AssignmentValueApplies operator sourceTarget.selected right replacement)
      rhsHeap sourceTarget updatedRoot after)
    (invalidOperand : Word) :
    ∃ updatedValue finalStore finalMap finalWorld,
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updatedRoot updatedValue prepared.route.rootType ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore ∧
      ∃ slots : Environment, slots.length = 7 ∧
        RuntimeEnvironmentHasTypes finalWorld (slots ++ coreEnvironment)
          (writtenContext prepared (SourceCoreCalls.packArguments codes).type
            actualContext) ambient.definitions ∧
        (∀ next outputType, ContinuationAgreement coreEnvironment store
          ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
            (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand).rename ξ)
          (slots ++ coreEnvironment) finalStore (shift 7 (next.rename ξ))) ∧
        ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have closed := virtual_closed layout ordinary
  have respects := environment_respects environments.runtime_hasTypes actualTyped agrees
  have setterTyped := setter_typed layout closed respects
  cases represented : rhsResult.represented with
  | @value _ rightValue rightRep =>
    have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld leaf right rightValue prepared.route.leafType :=
      .compatible rhsView (by simpa only [payloadModel, renamed, rhsCoreType] using rightRep)
    obtain ⟨rhsState, rhsRelated⟩ := rhsPost
    have snapshotRep := rhsResult.saved_snapshot
    have keyRep : DataExpressionSequence.Values (payloadModel compilation.checked registry functions) rhsMap rhsWorld sourceTypes (codes.map (·.type)) resolution.sources resolution.values := by
      simpa only [renamedCodes_types] using resolution.keysRelated.extend rhsResult.maps rhsResult.worlds
    have reference := resolution.reference.extend rhsResult.maps rhsResult.worlds
    have arguments := layout.views.arguments resolution.shaped keyRep (fun _ _ _found => by simpa only [Nat.zero_add] using _found)
    obtain ⟨latest⟩ := rhsResult.latest
    cases written with
    | @intro _ _ cell initial _ sourceRead _ initialValue update sourceWrite =>
      have cellEq := sourceRead.functional latest.read
      have cellOrdinary : cell.generalized = none := by
        obtain ⟨current, read, _, descriptor⟩ := rhsResult.metadata _ _ resolution.currentRead
        have same := sourceRead.functional read
        exact same.symm ▸ descriptor.trans resolution.ordinary
      have cellType : cell.type = prepared.route.rootSourceType := cellEq ▸ latest.type
      obtain ⟨replacement, applies, changed⟩ := DataPlaceAssignmentWriteBack.replacement_of_update update
      rw [resolution.selectedEq] at applies
      obtain ⟨replacementValue, replacementRep, modifiedEvaluated, _⟩ :=
        CompatiblePlaceModifier.preserves observations operatorProfile snapshotRep rightRep applies
          (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
            (.inRight .unit resolution.snapshot) rightValue coreEnvironment)
          (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalidOperand
      have present : ∃ sourceRoot, initial = some sourceRoot := by
        cases initial with
        | some value => exact ⟨value, rfl⟩
        | none => exact (resolved_nonempty layout.path resolution.shaped layout.nonempty (none_update changed)).elim
      obtain ⟨sourceRoot, rfl⟩ := present
      have rootExists : ∃ optional rootValue,
          RootRead compilation.checked registry functions rhsMap rhsWorld prepared rhsHeap rhsStore sourceTarget.location resolution.target
            cell optional sourceRoot rootValue := by
        cases cell with
        | mk sourceType value descriptor =>
         cases cellOrdinary
         cases initialValue with
         | initialized =>
          obtain ⟨value, root⟩ := CompatibleCellPlaceRoot.initialized_root ordinaryCells rhsResult.heaps reference sourceRead
          exact ⟨_, value, root⟩
         | emptyMapping key value =>
          obtain ⟨native, root⟩ := CompatibleCellPlaceRoot.virtual_root ordinaryCells rhsResult.heaps reference sourceRead
            (layout.virtual key value cellType.symm) registryExtension
          exact ⟨_, native, root⟩
      obtain ⟨optional, rootValue, root⟩ := rootExists
      have keyLength : prepared.keyTypes.length = resolution.values.length := layout.keyTypes ▸ keyRep.length.2
      have typedEnvironment : RuntimeEnvironmentHasTypes rhsWorld
          (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
            (.inRight .unit resolution.snapshot) rightValue replacementValue coreEnvironment)
          (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
            OptionalCell.referenceType prepared.route.rootType :: actualContext)
          ambient.definitions :=
        .cons replacementRep.runtime_hasType (.cons rightRep.runtime_hasType (.cons (.inRight snapshotRep.runtime_hasType)
          (.cons (CompatiblePlaceResolution.values_typed keyRep) (.cons (.cellRef reference.typed)
            (actualTyped.weaken (resolution.worlds.trans rhsResult.worlds))))))
      have currentPath : PreparedPath compilation.checked source site cell.type place.projections
          0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
      have currentArguments : Arguments compilation.checked registry functions rhsMap rhsWorld source site resolution.values
          currentPath sourceTarget.projections := by simpa only [cellType] using arguments
      obtain ⟨updatedValue, helperStore, finalStore, finalWorld, updatedRep, setterEvaluated,
        helperRead, coreWritten, finalHeaps, extension, frame, metadata, effect⟩ :=
        CompatibleCellPlaceWriteback.preserves ordinaryCells root rhsResult.heaps cellOrdinary currentArguments replacementRep changed sourceWrite layout.nonempty
          faithful observations keyLength typedEnvironment setterTyped (.var rfl) (.var rfl) (.var rfl)
      refine ⟨updatedValue, finalStore, rhsMap, finalWorld,
        by simpa only [cellType] using updatedRep, finalHeaps, resolution.maps.trans rhsResult.maps,
        (resolution.worlds.trans rhsResult.worlds).trans extension, (resolution.frame.trans rhsResult.frame).trans frame,
        (resolution.metadata.trans rhsResult.metadata).trans metadata,
        (resolution.effect.trans rhsResult.effect).trans effect,
        [.unit, updatedValue, replacementValue, rightValue, .inRight .unit resolution.snapshot,
          packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target], rfl, ?_, ?_,
        transport.extend rhsState (.refl _) extension frame metadata,
        protocol.trans (protocol.trans resolutionRelated rhsRelated)
          (transport.related rhsState (.refl _) extension frame metadata)⟩
      · exact .cons .unit (.cons updatedRep.runtime_hasType (typedEnvironment.weaken extension))
      · intro next outputType
        rw [execute_rename layout.path closed]
        simp only [renamed_packed, Expr.rename]
        unfold execute
        simp only [packed_renamed_type]
        have snapshotEvaluated := resolution.snapshotEvaluated
        simp only [packed_renamed_type] at snapshotEvaluated
        exact (ContinuationAgreement.letE (.var coreLookup)).trans
          ((ContinuationAgreement.bind resolution.keysEvaluated).trans
            ((ContinuationAgreement.bind snapshotEvaluated).trans
              ((ContinuationAgreement.bind rhsResult.evaluated).trans
                ((ContinuationAgreement.bind modifiedEvaluated).trans
                  ((ContinuationAgreement.bind setterEvaluated).trans
                    (ContinuationAgreement.letE (.storeCell (.var rfl) helperRead (.inRight (.var rfl)) coreWritten)))))))

end Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedCommit
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedFaults
/-! Pure failure phases consume the actual completed key or RHS execution.
The live root, fault token, reached diagnostic receipt, and caller transition
remain tied to that execution; no child-meaning callback is introduced. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedFaults
open CompatibleRenamedPlace
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces DataPlaceExecution
universe u v

variable {compilation : SourceCoreCompatibleDataPlaces.Context}
  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
  {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
  {administrativeContext actualContext : Core.Context} {ξ : Renaming}
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
  {before after : Dynamic.Heap} {store : Store} {index : Nat}
  {location : Dynamic.Location} {initialCell currentCell : Dynamic.Cell}
  {resolved : List Dynamic.EvaluatedProjection}

include ordinaryCells in
theorem preserves_projection
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (keys : CompatibleCellPlaceTargetKeys.Execution compilation.checked registry functions cells instances prepared place
      (renamedCodes codes ξ) sourceTypes location resolved coreEnvironment before after store mapping world (ξ index))
    (keyPost : ProtectedStateTransition.Transition protocol initialState
      ⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before place.projections resolved after)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {initial : Option Dynamic.Value} {reason : Dynamic.SemanticFault}
    (initialValue : Dynamic.RootInitialValue currentCell initial)
    (fault : Dynamic.ProjectionsFaults initial resolved reason)
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId reason after ∧
      Dynamic.RootInitialValue currentCell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps resolved reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore ∧
      ProtectedPlaceReachedDiagnostics.MissingPost compilation.checked registry functions protocol source site place prepared leaf initialState
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ reason token := by
  have getterTyped := getter_typed layout (virtual_closed layout ordinary) (environment_respects environments.runtime_hasTypes actualTyped agrees)
  obtain ⟨keyState, keyStateRelated⟩ := keyPost
  have cellEq := currentRead.functional keys.read
  have cellOrdinary : currentCell.generalized = none := cellEq ▸ keys.ordinary
  have cellType : currentCell.type = prepared.route.rootSourceType := cellEq ▸ keys.type
  have present : ∃ sourceRoot, initial = some sourceRoot := by
    cases initial with
    | some value => exact ⟨value, rfl⟩
    | none => cases fault
  obtain ⟨sourceRoot, rfl⟩ := present
  have rootExists := CompatibleCellPlaceRoot.root_of_initial ordinaryCells keys.heaps keys.reference
    currentRead cellOrdinary initialValue (fun k v same => layout.virtual k v (cellType.symm.trans same)) registryExtension
  obtain ⟨optional, rootValue, root⟩ := rootExists
  have keyRelated : DataExpressionSequence.Values (payloadModel compilation.checked registry functions) keys.keyMap keys.keyWorld sourceTypes (codes.map (·.type)) keys.sources keys.values := by
    simpa only [renamedCodes_types] using keys.related
  have arguments := layout.views.arguments keys.shaped keyRelated (fun _ _ found => by simpa only [Nat.zero_add] using found)
  have currentPath : PreparedPath compilation.checked source site currentCell.type place.projections
      0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
  have currentArguments : Arguments compilation.checked registry functions keys.keyMap keys.keyWorld source site keys.values
      currentPath resolved := by simpa only [cellType] using arguments
  obtain ⟨token, count, receipt, tree⟩ := currentArguments.faultTree root.payload fault prepared
  have keyLength : prepared.keyTypes.length = keys.values.length := layout.keyTypes ▸ keyRelated.length.2
  obtain ⟨finalStore, administrative, _, _, evaluated, appended, _⟩ :=
    faultTree_at root tree layout.nonempty faithful observations keyLength
      (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
      (SourceCoreCalls.packArguments codes).type (.var 1) (.var 0) (.var rfl) (.var rfl)
  have typedEnvironment : RuntimeEnvironmentHasTypes keys.keyWorld
      (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
      ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
        actualContext) ambient.definitions :=
    .cons (CompatiblePlaceResolution.values_typed keyRelated)
      (.cons (.cellRef keys.reference.typed) (actualTyped.weaken keys.worlds))
  obtain ⟨finalWorld, extension, finalHeaps, _, frame⟩ :=
    CellMappingHeap.evaluation_preserves_frame keys.heaps typedEnvironment getterTyped evaluated appended
  let reached := transport.extend keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after)
  have phaseRelated := transport.related keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after)
  refine ⟨token, count, sourceRoot, finalStore, keys.keyMap, finalWorld,
    .target (.projectionRead lookup initialRead trace currentRead initialValue fault), initialValue, receipt, ?_,
    finalHeaps,
    keys.maps, keys.worlds.trans extension, keys.frame.trans frame, keys.metadata,
    keys.effect.trans (appended.symm ▸ CellAwareScopeAuthority.Effect.append keys.keyStore administrative
      (.refl after) (.refl keys.keyMap) extension),
    reached, protocol.trans keyStateRelated phaseRelated,
    ⟨⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩, keyState, location, keys.target,
      currentCell, optional, sourceRoot, rootValue, keys.values, resolved, count, currentPath,
      keyStateRelated, phaseRelated, rfl, rfl, rfl, extension, frame, root, cellType, currentArguments, fault, receipt, tree⟩⟩
  unfold execute
  simp only [packed_renamed_type]
  exact .letE (.var keys.selected)
    (LanguageResult.bind_success _ keys.evaluated (LanguageResult.bind_failure _ evaluated))

include ordinaryCells in
theorem preserves_uninitialized
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (keys : CompatibleCellPlaceTargetKeys.Execution compilation.checked registry functions cells instances prepared place
      (renamedCodes codes ξ) sourceTypes location resolved coreEnvironment before after store mapping world (ξ index))
    (keyPost : ProtectedStateTransition.Transition protocol initialState
      ⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before place.projections resolved after)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (empty : currentCell.value = none)
    (notMapping : ¬ ∃ key value, currentCell.type = .mapping key value)
    (hasProjection : resolved ≠ [])
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId
        (.uninitializedLocation location) after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word prepared.invalidProjection)) finalStore ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore ∧
      ProtectedPlaceReachedDiagnostics.UninitializedPost compilation.checked registry functions protocol environment place prepared initialState
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ location := by
  have cellEq := currentRead.functional keys.read
  have cellOrdinary : currentCell.generalized = none := cellEq ▸ keys.ordinary
  have cellType : currentCell.type = prepared.route.rootSourceType := cellEq ▸ keys.type
  have noVirtual : prepared.route.rootMapping = none := ordinary (fun key value same => notMapping ⟨key, value, cellType.trans same⟩)
  obtain ⟨optional, native, represented⟩ := CompatibleCellPlaceRoot.read_at ordinaryCells keys.heaps keys.reference currentRead cellOrdinary
  have absent : optional = .inLeft prepared.route.rootType .unit := by
    cases represented with
    | uninitialized => rfl
    | initialized => cases empty
  rw [absent] at native
  have evaluated : Evaluates (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
      keys.keyStore (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
      (.inLeft prepared.optionalLeaf (.word prepared.invalidProjection)) keys.keyStore := by
    apply Evaluates.apply .lambda (.pair (.loadCell (.var rfl) native) (.var rfl))
    cases steps : prepared.steps with
    | nil => exact (layout.nonempty steps).elim
    | cons head tail =>
      simp only [normalizeRoot, noVirtual, LanguageResult.failure]
      exact .caseLeft (.first (.var rfl)) (.inLeft .word)
  obtain ⟨keyState, keyRelated⟩ := keyPost
  refine ⟨keys.keyStore, keys.keyMap, keys.keyWorld,
    .target (.uninitialized lookup initialRead trace currentRead empty notMapping hasProjection), ?_,
    keys.heaps, keys.maps, keys.worlds, keys.frame, keys.metadata, keys.effect,
    keyState, keyRelated,
    ⟨⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩, keyState, keys.target, currentCell,
      .inLeft prepared.route.rootType .unit, keys.sources, resolved, keyRelated, protocol.refl keyState, rfl, rfl, rfl,
      .refl _, .refl _ _, lookup, currentRead, keys.reference, native, absent ▸ represented, cellType, empty, notMapping, layout.nonempty, keys.shaped, hasProjection⟩⟩
  unfold execute
  simp only [packed_renamed_type]
  exact .letE (.var keys.selected)
    (LanguageResult.bind_success _ keys.evaluated (LanguageResult.bind_failure _ evaluated))

theorem preserves_structural {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (_rhsGenerated : certificate scope rhs lowered) (_found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before targetHeap rhsHeap : Dynamic.Heap} {store : Store} {index : Nat}
    {sourceTarget : Dynamic.ResolvedPlace} {right : Dynamic.Value} {cell : Dynamic.Cell} {initial : Option Dynamic.Value} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (resolution : CompatibleCellPlaceResolution.Execution compilation.checked registry functions cells instances prepared (renamedCodes codes ξ)
      sourceTypes place leaf sourceTarget coreEnvironment store mapping world before targetHeap)
    (coreLookup : coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target))
    (resolutionState : protocol.State ⟨scope, resolution.mapping, resolution.world, targetHeap, resolution.store, canonical⟩)
    (resolutionRelated : protocol.Relates initialState resolutionState)
    {rhsStore : Store} {rhsMap : LocationMap} {rhsWorld : StoreTyping} {rightValue : Value}
    (rhsResult : CompatibleCellPlaceRhs.Result (program := program) (context := context) (evidence := evidence) (source := source)
      (faults := faults) resolution rhs node (renamed lowered ξ) environment (.value right) rhsHeap
      (.inRight .word rightValue) rhsStore rhsMap rhsWorld)
    (rhsPost : ProtectedStateTransition.Transition protocol resolutionState ⟨scope, rhsMap, rhsWorld, rhsHeap, rhsStore, canonical⟩)
    (resolve : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap)
    (evaluate : Dynamic.ExpressionEvaluates program context evidence source environment targetHeap rhs right rhsHeap)
    (sourceRead : Dynamic.Heap.Reads rhsHeap sourceTarget.location cell)
    (rootType : cell.type = sourceTarget.rootType)
    (initialValue : Dynamic.RootInitialValue cell initial)
    (fault : Dynamic.ProjectionsFaults initial sourceTarget.projections reason)
    (next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason rhsHeap ∧
      Dynamic.RootInitialValue cell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps sourceTarget.projections reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) (lowered.expression.rename ξ) next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld rhsHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before rhsHeap ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld rhsHeap finalStore ∧
      ProtectedPlaceReachedDiagnostics.MissingPost compilation.checked registry functions protocol source site place prepared leaf initialState
        ⟨scope, finalMap, finalWorld, rhsHeap, finalStore, canonical⟩ reason token := by
  have closed := virtual_closed layout ordinary
  have respects := environment_respects environments.runtime_hasTypes actualTyped agrees
  have setterTyped := setter_typed layout closed respects
  have sourceFault := Dynamic.SourcePlaceAssignmentFaults.structuralUpdate (operator := operator) resolve evaluate sourceRead rootType initialValue fault
  cases represented : rhsResult.represented with
  | @value _ rightValue rightRep =>
    obtain ⟨rhsState, rhsRelated⟩ := rhsPost
    have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld leaf right rightValue prepared.route.leafType :=
      .compatible rhsView (by simpa only [payloadModel, renamed, rhsCoreType] using rightRep)
    have snapshotRep := rhsResult.saved_snapshot
    have keyRep : DataExpressionSequence.Values (payloadModel compilation.checked registry functions) rhsMap rhsWorld sourceTypes (codes.map (·.type)) resolution.sources resolution.values := by
      simpa only [renamedCodes_types] using resolution.keysRelated.extend rhsResult.maps rhsResult.worlds
    have reference := resolution.reference.extend rhsResult.maps rhsResult.worlds
    have arguments := layout.views.arguments resolution.shaped keyRep (fun _ _ _found => by simpa only [Nat.zero_add] using _found)
    obtain ⟨latest⟩ := rhsResult.latest
    have cellEq := sourceRead.functional latest.read
    have cellOrdinary : cell.generalized = none := by
      obtain ⟨current, read, _, descriptor⟩ := rhsResult.metadata _ _ resolution.currentRead
      have same := sourceRead.functional read
      exact same.symm ▸ descriptor.trans resolution.ordinary
    have cellType : cell.type = prepared.route.rootSourceType := cellEq ▸ latest.type
    obtain ⟨replacement, replacementValue, replacementRep, _, modifiedEvaluated, valid⟩ :=
      CompatiblePlaceModifier.initialized_success observations operatorProfile snapshotRep rightRep
        (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) rightValue coreEnvironment)
        (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalidOperand
    have present : ∃ sourceRoot, initial = some sourceRoot := by
      cases initial with
      | some value => exact ⟨value, rfl⟩
      | none => cases fault
    obtain ⟨sourceRoot, rfl⟩ := present
    have rootExists := CompatibleCellPlaceRoot.root_of_initial ordinaryCells rhsResult.heaps reference
      sourceRead cellOrdinary initialValue (fun k v same => layout.virtual k v (cellType.symm.trans same)) registryExtension
    obtain ⟨optional, rootValue, root⟩ := rootExists
    have keyLength : prepared.keyTypes.length = resolution.values.length := layout.keyTypes ▸ keyRep.length.2
    have typedEnvironment : RuntimeEnvironmentHasTypes rhsWorld
        (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) rightValue replacementValue coreEnvironment)
        (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
          OptionalCell.referenceType prepared.route.rootType :: actualContext)
        ambient.definitions :=
      .cons replacementRep.runtime_hasType (.cons rightRep.runtime_hasType (.cons (.inRight snapshotRep.runtime_hasType)
        (.cons (CompatiblePlaceResolution.values_typed keyRep) (.cons (.cellRef reference.typed)
          (actualTyped.weaken (resolution.worlds.trans rhsResult.worlds))))))
    have currentPath : PreparedPath compilation.checked source site cell.type place.projections
        0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
    have currentArguments : Arguments compilation.checked registry functions rhsMap rhsWorld source site resolution.values
        currentPath sourceTarget.projections := by simpa only [cellType] using arguments
    obtain ⟨token, count, finalStore, administrative, finalWorld, receipt, setterEvaluated,
      finalHeaps, extension, frame, _, appended, _⟩ :=
      CompatibleCellPlaceSetterFault.preserves root rhsResult.heaps currentArguments fault layout.nonempty
        faithful observations keyLength typedEnvironment setterTyped (.var rfl) (.var rfl) (.var rfl)
    obtain ⟨otherToken, otherCount, otherReceipt, tree⟩ := currentArguments.faultTree root.payload fault prepared
    obtain ⟨rfl, rfl⟩ := receipt.functional otherReceipt
    let reached := transport.extend rhsState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl rhsHeap)
    have phaseRelated := transport.related rhsState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl rhsHeap)
    refine ⟨token, count, sourceRoot, finalStore, rhsMap, finalWorld, sourceFault, initialValue, receipt, ?_, finalHeaps,
      resolution.maps.trans rhsResult.maps, (resolution.worlds.trans rhsResult.worlds).trans extension,
      (resolution.frame.trans rhsResult.frame).trans frame, resolution.metadata.trans rhsResult.metadata,
      (resolution.effect.trans rhsResult.effect).trans (appended.symm ▸ CellAwareScopeAuthority.Effect.append rhsStore administrative
        (.refl rhsHeap) (.refl rhsMap) extension),
      reached, protocol.trans (protocol.trans resolutionRelated rhsRelated) phaseRelated,
      ⟨⟨scope, rhsMap, rhsWorld, rhsHeap, rhsStore, canonical⟩, rhsState, sourceTarget.location, resolution.target,
        cell, optional, sourceRoot, rootValue, resolution.values, sourceTarget.projections, count, currentPath,
        protocol.trans resolutionRelated rhsRelated, phaseRelated, rfl, rfl, rfl, extension, frame, root, cellType,
        currentArguments, fault, receipt, tree⟩⟩
    unfold execute
    simp only [packed_renamed_type]
    have snapshotEvaluated := resolution.snapshotEvaluated
    simp only [packed_renamed_type] at snapshotEvaluated
    exact .letE (.var coreLookup)
      (LanguageResult.bind_success _ resolution.keysEvaluated
        (LanguageResult.bind_success _ snapshotEvaluated
          (LanguageResult.bind_success _ rhsResult.evaluated
            (LanguageResult.bind_success _ modifiedEvaluated
              (LanguageResult.bind_failure _ setterEvaluated)))))

end Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedFaults
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedPrefix
/-! Staged keys retain their original failure and reached heap. The native
getter runs only after the complete ordered key row, and keeps the existing
prepared route and snapshot representation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedPrefix
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution
open CompatiblePlaceKeyReflection CompatibleRenamedPlace CompatibleMixedRoute CompatiblePlaceKeys
universe u v

variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {cells : GenericHeap.CellModel ambient.definitions}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {program : Program} {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
  {place : PlaceResolution} {environment : Dynamic.Environment} {actual canonical : Environment}
  {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {scope : Scope}

inductive KeyResultAt (size : Nat)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩) (index : Nat)
    (rhs next : Expr) (output : Ty) (operator : Option BinaryOp) (bitNot : Bool) (invalid : Word)
    (value : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {failure : Staging.Recursive.Failure} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (ready : Staging.Recursive.ProjectedTarget.RootReady environment before place)
      (trace : Staging.Recursive.Size.Expressions program stages sourceSize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys place.projections) (.fault failure) after)
      (same : value = .inLeft output (.word token)) (matched : faults failure token)
      (heaps : GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore)
      (post : ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
      KeyResultAt size initial index rhs next output operator bitNot invalid value finalStore
  | keys {sourceSize remainingSize : Nat} {location : Dynamic.Location}
      {resolved : List Dynamic.EvaluatedProjection} {after : Dynamic.Heap}
      (lookup : Dynamic.Environment.LooksUp environment place.root location)
      (execution : CompatibleCellPlaceTargetKeys.Execution checked registry functions cells instances prepared place codes sourceTypes
        location resolved actual before after store mapping world index)
      (trace : Staging.Recursive.Size.Expressions program stages sourceSize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys place.projections) (.values execution.sources) after)
      (sourcesTyped : Dynamic.ValuesHaveTypes context after execution.sources sourceTypes)
      (sourceHeap : Dynamic.HeapWellTyped context after)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize
        (keysEnvironment prepared.route.rootType execution.target (packValues execution.values) actual) execution.keyStore
        (CompatiblePlaceKeyReflection.remainder prepared (SourceCoreCalls.packArguments codes).type rhs next output operator bitNot invalid) value finalStore)
      (post : ProtectedStateTransition.Transition protocol initial ⟨scope, execution.keyMap, execution.keyWorld, after, execution.keyStore, canonical⟩) :
      KeyResultAt size initial index rhs next output operator bitNot invalid value finalStore

inductive PrefixResultAt (size : Nat) (leaf : TypeSystem.Ty)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (rhs next : Expr) (output : Ty) (operator : Option BinaryOp) (bitNot : Bool) (invalid : Word)
    (value : Value) (finalStore : Store) : Prop where
  | keyFault {sourceSize : Nat} {failure : Staging.Recursive.Failure} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (ready : Staging.Recursive.ProjectedTarget.RootReady environment before place)
      (trace : Staging.Recursive.Size.Expressions program stages sourceSize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys place.projections) (.fault failure) after)
      (same : value = .inLeft output (.word token)) (matched : faults failure token)
      (heaps : GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore)
      (post : ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
      PrefixResultAt size leaf initial rhs next output operator bitNot invalid value finalStore
  | getterFault {sourceSize : Nat} {sources : List Dynamic.Value} {reason : Dynamic.SemanticFault}
      {token : Word} {after : Dynamic.Heap} {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : Staging.Recursive.Size.Expressions program stages sourceSize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys place.projections) (.values sources) after)
      (failed : Staging.Recursive.ProjectedTarget.GetterFault environment before after place sources reason)
      (same : value = .inLeft output (.word token)) (matched : faults (.semantic reason) token)
      (heaps : GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore)
      (post : ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
      PrefixResultAt size leaf initial rhs next output operator bitNot invalid value finalStore
  | resolved {sourceSize remainingSize : Nat} {target : Dynamic.ResolvedPlace} {after : Dynamic.Heap}
      (execution : CompatibleCellPlaceResolution.Execution checked registry functions cells instances prepared codes sourceTypes place leaf target
        actual store mapping world before after)
      (trace : Staging.Recursive.Size.Expressions program stages sourceSize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys place.projections) (.values execution.sources) after)
      (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before after place execution.sources target)
      (sourcesTyped : Dynamic.ValuesHaveTypes context after execution.sources sourceTypes)
      (sourceHeap : Dynamic.HeapWellTyped context after)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize (snapshotEnvironment prepared.route.rootType execution.target (packValues execution.values)
        (.inRight .unit execution.snapshot) actual) execution.store
        (CompatiblePlacePrefixReflection.remainder prepared (SourceCoreCalls.packArguments codes).type rhs next output operator bitNot invalid) value finalStore)
      (post : ProtectedStateTransition.Transition protocol initial ⟨scope, execution.mapping, execution.world, after, execution.store, canonical⟩) :
      PrefixResultAt size leaf initial rhs next output operator bitNot invalid value finalStore

variable {protocol}

theorem values_plain {size : Nat} {ids : List ExpressionId} {sources : List Dynamic.Value} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expressions program stages size invocation context environment before ids (.values sources) after) :
    Dynamic.ExpressionsEvaluate program context invocation.evidence invocation.source environment before ids sources after := by
  induction ids generalizing size before sources with
  | nil => cases trace; exact .nil
  | cons id ids ih =>
      cases trace with
      | cons head tail => exact .cons head.sound.value_plain (ih tail)


theorem reflects_keys (budget : Nat) {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient}
    {cells : GenericHeap.CellModel ambient.definitions}
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions} {program : Program} {context : SourceSemantics.Context}
    {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope} {scope : Scope}
    {certificate : Certificate} {faults : RecursiveStageMeaning.FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (_children : DataExpressionSequence.Tree invocation.source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {environment : Dynamic.Environment} {canonical coreEnvironment : Environment} {before : Dynamic.Heap} {store finalStore : Store}
    {location : Dynamic.Location} {initialCell : Dynamic.Cell} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (_heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sequenceMeaning : ∀ target,
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target) →
      RuntimeEnvironmentHasTypes world
        (.cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (OptionalCell.referenceType prepared.route.rootType :: actualContext) ambient.definitions →
      ∀ {keySize keyValue keyStore},
      EvaluationSize keySize (.cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment) store
        ((SourceCoreCalls.packArguments codes).expression.rename (DataPlaceChildExpressions.prefixRenaming 1 ξ)) keyValue keyStore →
      keySize < budget →
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Expressions program stages sourceSize invocation context environment before
          (Staging.Recursive.ProjectedTarget.keys place.projections) outcome after ∧
        RecursiveStageArguments.ResultFor (payloadModel checked registry functions) finalMap finalWorld sourceTypes codes faults outcome keyValue ∧
        GenericHeap.CellHeapRepresents cells finalMap finalWorld after keyStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap keyStore ∧ Dynamic.HeapMetadataExtend before after ∧
        CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after keyStore ∧
        (∀ sources, outcome = .values sources → Dynamic.ValuesHaveTypes context after sources sourceTypes ∧ Dynamic.HeapWellTyped context after) ∧
        ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, keyStore, canonical⟩)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    {rhs next : Expr} {outputType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word} {result : Value}
    {size : Nat} (completed : CoreProof.EvaluationSize size coreEnvironment store
      (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType operator bitNot invalid) result finalStore) (bounded : size ≤ budget) :
    KeyResultAt (cells := cells) (instances := instances) (checked := checked) (registry := registry) (functions := functions) (program := program)
      (context := context) (stages := stages) (invocation := invocation) (faults := faults)
      (prepared := prepared) (codes := renamedCodes codes ξ) (sourceTypes := sourceTypes)
      (place := place) (environment := environment) (actual := coreEnvironment)
      protocol size initialState (ξ index) rhs next outputType operator bitNot invalid result finalStore := by
  obtain ⟨target, selected, reference⟩ := environments.lookup_visible lookup slot
  have reflectKeys := fun {keySize : Nat} {keyValue : Value} {keyStore : Store}
      (evaluated : CoreProof.EvaluationSize keySize (referenceEnvironment prepared.route.rootType target coreEnvironment) store
        (shift 1 (SourceCoreCalls.packArguments (renamedCodes codes ξ)).expression) keyValue keyStore) (keyBound : keySize < size) =>
    sequenceMeaning target (agrees selected) (.cons (.cellRef reference.typed) actualTyped)
      (by simpa only [DataPlaceChildExpressions.rename_prefix, packed_renamed_expression, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated) (Nat.lt_of_lt_of_le keyBound bounded)
  cases completed with
  | letE referenceEvaluated tail =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic referenceEvaluated.sound (Evaluates.var (agrees selected))
    cases tail with
    | caseLeft keysEvaluated failed =>
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata, effect, sourceHeap, post⟩ := reflectKeys keysEvaluated (by omega)
      cases represented with
      | fault tokenRep =>
        cases failed with
        | inLeft valueEvaluated =>
          cases valueEvaluated with
          | var found =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst_vars
            exact .fault (.intro lookup initialRead) sourceTrace rfl tokenRep finalHeaps maps worlds frame metadata effect post
    | caseRight keysEvaluated tail =>
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata, effect, sourceHeap, post⟩ := reflectKeys keysEvaluated (by omega)
      cases represented with
      | @values sources values related =>
        obtain ⟨resolved, shaped, _plain⟩ := DataPlaceKeyOrder.values_projections
          (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using values_plain sourceTrace)
        obtain ⟨scheme, staticLookup, _, monomorphic, bodyEq⟩ := rootTyped.scheme
        obtain ⟨staticLocation, staticCell, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
        have locationEq := lookup.functional staticLookupRuntime
        subst staticLocation
        have cellEq := initialRead.functional staticRead
        subst staticCell
        obtain ⟨cell, read, type, _⟩ := metadata _ _ initialRead
        exact .keys lookup
          ⟨target, sources, values, _, finalMap, finalWorld, cell, read,
            (locals.mono metadata).descriptor_empty_of_monomorphic (sourceHeap _ rfl).2 staticLookup lookup read monomorphic,
            type.trans (staticCellType.trans bodyEq), reference.extend maps worlds, agrees selected, shaped,
            keysEvaluated.sound, by simpa only [renamedCodes_types] using related, finalHeaps, maps, worlds, frame, metadata, effect⟩ sourceTrace (sourceHeap _ rfl).1 (sourceHeap _ rfl).2 (by omega) tail post

theorem reflects_getter (budget : Nat) {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
    {program : Program} {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : RecursiveStageMeaning.FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming} {rhsType : Core.Ty}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation invocation.source certificate scope site place prepared codes sourceTypes leaf administrativeContext rhsType)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (functionTypes : FunctionRuntimeViews functions)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (missingFor : ProtectedPlaceReachedDiagnostics.MissingFor compilation.checked registry functions protocol
      invocation.source site place prepared leaf initialState (fun reason token => faults (.semantic reason) token))
    (uninitializedFor : ProtectedPlaceReachedDiagnostics.UninitializedFor compilation.checked registry functions protocol
      environment place prepared initialState (fun reason token => faults (.semantic reason) token))
    (sequenceMeaning : ∀ target,
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target) →
      RuntimeEnvironmentHasTypes world
        (.cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (OptionalCell.referenceType prepared.route.rootType :: actualContext) ambient.definitions →
      ∀ {keySize keyValue keyStore},
      EvaluationSize keySize (.cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment) store
        ((SourceCoreCalls.packArguments codes).expression.rename (DataPlaceChildExpressions.prefixRenaming 1 ξ)) keyValue keyStore →
      keySize < budget →
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Expressions program stages sourceSize invocation context environment before
          (Staging.Recursive.ProjectedTarget.keys place.projections) outcome after ∧
        RecursiveStageArguments.ResultFor (payloadModel compilation.checked registry functions) finalMap finalWorld sourceTypes codes faults outcome keyValue ∧
        GenericHeap.CellHeapRepresents cells finalMap finalWorld after keyStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap keyStore ∧ Dynamic.HeapMetadataExtend before after ∧
        CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after keyStore ∧
        (∀ sources, outcome = .values sources → Dynamic.ValuesHaveTypes context after sources sourceTypes ∧ Dynamic.HeapWellTyped context after) ∧
        ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, keyStore, canonical⟩)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {rhs next : Expr} {outputType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word} {result : Value}
    {size : Nat} (completed : CoreProof.EvaluationSize size coreEnvironment store
      (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType operator bitNot invalid) result finalStore) (bounded : size ≤ budget) :
    PrefixResultAt (cells := cells) (instances := instances) (checked := compilation.checked) (registry := registry) (functions := functions)
      (program := program) (context := context) (stages := stages) (invocation := invocation) (faults := faults)
      (prepared := prepared) (codes := renamedCodes codes ξ) (sourceTypes := sourceTypes)
      (place := place) (environment := environment) (actual := coreEnvironment)
      protocol size leaf initialState rhs next outputType operator bitNot invalid result finalStore := by
  have closed := virtual_closed layout ordinary
  have getterTyped := getter_typed layout closed (environment_respects environments.runtime_hasTypes actualTyped agrees)
  obtain ⟨scheme, staticLookup, _, _, _⟩ := rootTyped.scheme
  obtain ⟨location, initialCell, lookup, initialRead, _, _⟩ := locals.lookup staticLookup
  have keyPhase := reflects_keys budget layout.children protocol environments heaps locals agrees actualTyped initialState sequenceMeaning slot rootTyped lookup initialRead completed bounded
  cases keyPhase with
  | fault ready sourceFault resultEq tokenRep finalHeaps maps worlds frame metadata effect post =>
    exact .keyFault ready sourceFault resultEq tokenRep finalHeaps maps worlds frame metadata effect post
  | @keys keySourceSize keyTailSize sourceLocation resolved after keyLookup keys sourceTrace sourcesTyped sourceHeap keyBound continuation keyPost =>
    obtain ⟨keyState, keyStateRelated⟩ := keyPost
    have locationEq := lookup.functional keyLookup
    subst sourceLocation
    have keyRelated : DataExpressionSequence.Values (payloadModel compilation.checked registry functions) keys.keyMap keys.keyWorld sourceTypes (codes.map (·.type)) keys.sources keys.values := by
      simpa only [renamedCodes_types] using keys.related
    have arguments := layout.views.arguments keys.shaped keyRelated (fun _ _ found => by simpa only [Nat.zero_add] using found)
    have currentPath : PreparedPath compilation.checked invocation.source site keys.cell.type place.projections 0 prepared.steps prepared.keys leaf := keys.type ▸ layout.path
    have currentArguments : Arguments compilation.checked registry functions keys.keyMap keys.keyWorld invocation.source site keys.values currentPath resolved := by
      simpa only [keys.type] using arguments
    have typedEnvironment : RuntimeEnvironmentHasTypes keys.keyWorld
        (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
        ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
          actualContext) ambient.definitions :=
      .cons (CompatiblePlaceResolution.values_typed keyRelated)
        (.cons (.cellRef keys.reference.typed) (actualTyped.weaken keys.worlds))
    have reflectGetter := fun {value : Value} {afterStore : Store}
        (evaluated : Evaluates (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment) keys.keyStore
          (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0))) value afterStore) =>
      CompatibleCellPlaceGetterReflection.reflects ordinaryCells keys.ordinary currentArguments layout.leafProjected
        (fun k v same => layout.virtual k v (keys.type.symm.trans same))
        (fun nonmapping => ordinary (fun k v same => nonmapping k v (keys.type.trans same)))
        registryExtension layout.nonempty functionTypes faithful observations (layout.keyTypes ▸ keyRelated.length.2)
        keys.heaps keys.reference keys.read typedEnvironment getterTyped (.var rfl) (.var rfl) evaluated
    unfold CompatiblePlaceKeyReflection.remainder at continuation
    simp only [packed_renamed_type] at continuation
    cases continuation with
    | caseLeft getterEvaluated failed =>
      obtain ⟨futureWorld, administrative, resultRep, finalHeaps, extension, frame, appended⟩ := reflectGetter getterEvaluated.sound
      have getterEffect := appended.symm ▸ CellAwareScopeAuthority.Effect.append
        (instances := instances) keys.keyStore administrative (.refl after) (.refl keys.keyMap) extension
      cases resultRep with
      | @missing sourceRoot reason token count initial fault receipt =>
        cases failed with
        | inLeft valueEvaluated =>
          cases valueEvaluated with
          | var found =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst_vars
            obtain ⟨optional, rootValue, live⟩ := CompatibleCellPlaceRoot.root_of_initial ordinaryCells
              keys.heaps keys.reference keys.read keys.ordinary initial
              (fun k v same => layout.virtual k v (keys.type.symm.trans same)) registryExtension
            obtain ⟨otherToken, otherCount, otherReceipt, tree⟩ := currentArguments.faultTree live.payload fault prepared
            obtain ⟨rfl, rfl⟩ := receipt.functional otherReceipt
            let reached := transport.extend keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after)
            have phaseRelated := transport.related keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after)
            have witness : ProtectedPlaceReachedDiagnostics.MissingWitness compilation.checked registry functions protocol
                invocation.source site place prepared leaf initialState reached reason token :=
              ⟨⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩, keyState, location, keys.target,
                keys.cell, optional, sourceRoot, rootValue, keys.values, resolved, count, currentPath,
                keyStateRelated, phaseRelated, rfl, rfl, rfl, extension, frame, live, keys.type, currentArguments, fault, receipt, tree⟩
            exact .getterFault sourceTrace (.projection lookup initialRead (Staging.Recursive.ProjectedTarget.Values.of_data keys.shaped) keys.read initial fault) rfl
              (missingFor reached (protocol.trans keyStateRelated phaseRelated) witness) finalHeaps keys.maps (keys.worlds.trans extension) (keys.frame.trans frame) keys.metadata
              (keys.effect.trans getterEffect)
              ⟨reached, protocol.trans keyStateRelated phaseRelated⟩
      | uninitialized empty notMapping nonempty =>
        cases failed with
        | inLeft valueEvaluated =>
          cases valueEvaluated with
          | var found =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst_vars
            obtain ⟨optional, native, cellRep⟩ := CompatibleCellPlaceRoot.read_at ordinaryCells keys.heaps keys.reference keys.read keys.ordinary
            let reached := transport.extend keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after)
            have phaseRelated := transport.related keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after)
            have witness : ProtectedPlaceReachedDiagnostics.UninitializedWitness compilation.checked registry functions protocol
                environment place prepared initialState reached location :=
              ⟨⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩, keyState, keys.target,
                keys.cell, optional, keys.sources, resolved, keyStateRelated, phaseRelated, rfl, rfl, rfl, extension, frame,
                lookup, keys.read, keys.reference, native, cellRep, keys.type, empty, notMapping, layout.nonempty, keys.shaped, nonempty⟩
            exact .getterFault sourceTrace (.uninitialized lookup initialRead (Staging.Recursive.ProjectedTarget.Values.of_data keys.shaped) keys.read empty notMapping nonempty) rfl
              (uninitializedFor reached (protocol.trans keyStateRelated phaseRelated) witness) finalHeaps keys.maps (keys.worlds.trans extension) (keys.frame.trans frame) keys.metadata
              (keys.effect.trans getterEffect)
              ⟨reached, protocol.trans keyStateRelated phaseRelated⟩
    | caseRight getterEvaluated remaining =>
      obtain ⟨futureWorld, administrative, resultRep, finalHeaps, extension, frame, appended⟩ := reflectGetter getterEvaluated.sound
      have getterEffect := appended.symm ▸ CellAwareScopeAuthority.Effect.append
        (instances := instances) keys.keyStore administrative (.refl after) (.refl keys.keyMap) extension
      cases resultRep with
      | @read sourceRoot selected snapshot initial read represented =>
        refine .resolved
          { target := keys.target
            sources := keys.sources
            values := keys.values
            selected := selected
            snapshot := snapshot
            keyStore := keys.keyStore
            store := _
            mapping := keys.keyMap
            world := futureWorld
            selectedEq := rfl
            currentCell := keys.cell
            currentRead := keys.read
            ordinary := keys.ordinary
            currentType := keys.type
            reference := keys.reference.extend (.refl _) extension
            shaped := keys.shaped
            keysEvaluated := keys.evaluated
            snapshotEvaluated := by simpa only [packed_renamed_type] using getterEvaluated.sound
            keysRelated := keys.related.extend (.refl _) extension
            snapshotRelated := represented
            heaps := finalHeaps
            maps := keys.maps
            worlds := keys.worlds.trans extension
            frame := keys.frame.trans frame
            metadata := keys.metadata
            effect := keys.effect.trans getterEffect } sourceTrace
          (.intro lookup initialRead (Staging.Recursive.ProjectedTarget.Values.of_data keys.shaped) keys.read initial read)
          sourcesTyped sourceHeap ?_ (by simpa only [CompatiblePlacePrefixReflection.remainder, packed_renamed_type, snapshotEnvironment] using remaining)
          ⟨transport.extend keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after),
            protocol.trans keyStateRelated (transport.related keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after))⟩
        omega


end Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedBitNotCommit
/-! Projected unary writeback consumes the actual key/getter state. Its Unit
slot is administrative; it creates no Source expression or Source RHS step. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedBitNotCommit
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleRenamedPlace
universe u v

structure Execution (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (cells : GenericHeap.CellModel ambient.definitions)
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions) (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr)
    (environment : Environment) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (target : Location) (keys : List Value) (snapshot : Value) (before after : Dynamic.Heap)
    (updated : Dynamic.Value) (operator : Option BinaryOp) (invalid : Word) where
  replacement : Value
  value : Value
  helperStore : Store
  finalStore : Store
  finalWorld : StoreTyping
  related : ValueRep checked registry functions mapping finalWorld prepared.route.rootSourceType updated value prepared.route.rootType
  heaps : GenericHeap.CellHeapRepresents cells mapping finalWorld after finalStore
  worlds : WorldExtends world finalWorld
  frame : AdministrativePreserved mapping store mapping finalStore
  metadata : Dynamic.HeapMetadataExtend before after
  effect : CellAwareScopeAuthority.Effect instances mapping world before store mapping finalWorld after finalStore
  modified : Evaluates (rhsEnvironment prepared.route.rootType target (packValues keys) (.inRight .unit snapshot) .unit environment) store
    (SourceCoreCompatibleDataPlaces.modified prepared.route.leafType operator true (.var 1) (.var 0) invalid)
    (.inRight .word replacement) store
  setter : Evaluates (modifiedEnvironment prepared.route.rootType target (packValues keys) (.inRight .unit snapshot) .unit replacement environment) store
    (.apply (SourceCoreCompatibleDataPlaces.setter prepared (SourceCoreCalls.packArguments codes).type)
      (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0)))) (.inRight .word value) helperStore
  read : ∃ optional, helperStore.read? target = some optional
  written : helperStore.write? target (.inRight .unit value) = some finalStore

def writtenContext (prepared : Prepared) (keyType : Ty) (context : Core.Context) : Core.Context :=
  .unit :: prepared.route.rootType :: prepared.route.leafType :: .unit ::
    prepared.optionalLeaf :: keyType :: OptionalCell.referenceType prepared.route.rootType :: context

private theorem none_update {modify : Option Dynamic.Value → Dynamic.Value → Prop}
    {projections : List Dynamic.EvaluatedProjection} {updated : Dynamic.Value}
    (changed : Dynamic.ProjectionsUpdate modify none projections updated) : projections = [] := by
  cases changed
  rfl

private theorem resolved_nonempty {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf)
    {sources : List Dynamic.Value} {resolved : List Dynamic.EvaluatedProjection}
    (shaped : DataPlaceKeyOrder.Values projections sources resolved) (nonempty : steps ≠ []) : resolved ≠ [] := by
  have lengths : steps.length = resolved.length := by
    clear nonempty
    induction path generalizing sources resolved with
    | nil => cases shaped; rfl
    | member _ _ _ _ ih => cases shaped with | member tail => exact congrArg Nat.succ (ih tail)
    | index _ _ _ ih => cases shaped with | index tail => exact congrArg Nat.succ (ih tail)
  intro empty
  rw [empty, List.length_nil] at lengths
  exact nonempty (List.eq_nil_of_length_eq_zero lengths)

/-- Consume an independent snapshot write and derive its actual native
modifier, latest-root reconstruction and single mapped store update. -/
theorem typed_of_write {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext .unit)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (profile : SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before selectedHeap after : Dynamic.Heap} {store : Store} {target : Dynamic.ResolvedPlace} {updated : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (resolution : CompatibleCellPlaceResolution.Execution compilation.checked registry functions cells instances prepared (renamedCodes codes ξ) sourceTypes place leaf target
      coreEnvironment store mapping world before selectedHeap)
    (written : Dynamic.ResolvedPlaceWrites (fun _ value => Dynamic.BitNotSnapshot target.selected value) selectedHeap target updated after)
    (operator : Option BinaryOp) (invalid : Word) :
    ∃ commit : Execution compilation.checked registry functions cells instances prepared (renamedCodes codes ξ)
        coreEnvironment resolution.store resolution.mapping resolution.world resolution.target resolution.values
        resolution.snapshot selectedHeap after updated operator invalid,
      RuntimeEnvironmentHasTypes commit.finalWorld
        (writtenEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) .unit commit.replacement commit.value coreEnvironment)
        (writtenContext prepared (SourceCoreCalls.packArguments codes).type actualContext) ambient.definitions := by
  have closed := virtual_closed layout ordinary
  have setterTyped := setter_typed layout closed (environment_respects environments.runtime_hasTypes actualTyped agrees)
  have snapshotRep := resolution.snapshotRelated
  have keyRep : DataExpressionSequence.Values (payloadModel compilation.checked registry functions) resolution.mapping resolution.world
      sourceTypes (codes.map (·.type)) resolution.sources resolution.values := by
    simpa only [renamedCodes_types] using resolution.keysRelated
  have reference := resolution.reference
  have arguments := layout.views.arguments resolution.shaped keyRep (fun _ _ found => by simpa only [Nat.zero_add] using found)
  cases written with
  | @intro _ _ cell initial _ sourceRead _ initialValue update sourceWrite =>
    have cellEq := sourceRead.functional resolution.currentRead
    have cellOrdinary : cell.generalized = none := cellEq ▸ resolution.ordinary
    have cellType : cell.type = prepared.route.rootSourceType := cellEq ▸ resolution.currentType
    obtain ⟨replacement, applies, changed⟩ := DataPlaceAssignmentWriteBack.replacement_of_update update
    rw [resolution.selectedEq] at applies
    obtain ⟨replacement', replacementValue, replacementRep, applies', modifiedEvaluated, _⟩ :=
      CompatiblePlaceNumericBitNotModifier.success profile snapshotRep
        (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) .unit coreEnvironment)
        (.var (index := 1) rfl) operator resolution.store invalid
    have same := CompatiblePlaceBitNotModifier.functional applies' applies
    subst replacement'
    have present : ∃ sourceRoot, initial = some sourceRoot := by
      cases initial with
      | some value => exact ⟨value, rfl⟩
      | none => exact (resolved_nonempty layout.path resolution.shaped layout.nonempty (none_update changed)).elim
    obtain ⟨sourceRoot, rfl⟩ := present
    have rootExists := CompatibleCellPlaceRoot.root_of_initial ordinaryCells resolution.heaps reference
      sourceRead cellOrdinary initialValue (fun k v same => layout.virtual k v (cellType.symm.trans same)) registryExtension
    obtain ⟨optional, rootValue, root⟩ := rootExists
    have typedEnvironment : RuntimeEnvironmentHasTypes resolution.world
        (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) .unit replacementValue coreEnvironment)
        (prepared.route.leafType :: .unit :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
          OptionalCell.referenceType prepared.route.rootType :: actualContext)
        ambient.definitions :=
      .cons replacementRep.runtime_hasType (.cons .unit (.cons (.inRight snapshotRep.runtime_hasType)
        (.cons (CompatiblePlaceResolution.values_typed keyRep) (.cons (.cellRef reference.typed)
          (actualTyped.weaken resolution.worlds)))))
    have currentPath : PreparedPath compilation.checked source site cell.type place.projections
        0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
    have currentArguments : Arguments compilation.checked registry functions resolution.mapping resolution.world source site resolution.values
        currentPath target.projections := by simpa only [cellType] using arguments
    obtain ⟨updatedValue, helperStore, finalStore, finalWorld, updatedRep, setterEvaluated,
      helperRead, coreWritten, finalHeaps, extension, frame, metadata, effect⟩ :=
      CompatibleCellPlaceWriteback.preserves ordinaryCells root resolution.heaps cellOrdinary currentArguments replacementRep changed sourceWrite layout.nonempty
        faithful observations (layout.keyTypes ▸ keyRep.length.2) typedEnvironment setterTyped (.var rfl) (.var rfl) (.var rfl)
    refine ⟨⟨replacementValue, updatedValue, helperStore, finalStore, finalWorld,
      by simpa only [cellType] using updatedRep, finalHeaps, extension, frame, metadata, effect,
      modifiedEvaluated, ?_, ⟨_, helperRead⟩, coreWritten⟩, ?_⟩
    · simpa only [packed_renamed_type] using setterEvaluated
    · exact .cons .unit (.cons updatedRep.runtime_hasType (typedEnvironment.weaken extension))

/-- Protected callers carry the actual post-write witness. -/
theorem of_write {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext .unit)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (profile : SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before selectedHeap after : Dynamic.Heap} {store : Store} {target : Dynamic.ResolvedPlace} {updated : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (resolution : CompatibleCellPlaceResolution.Execution compilation.checked registry functions cells instances prepared (renamedCodes codes ξ) sourceTypes place leaf target
      coreEnvironment store mapping world before selectedHeap)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (selected : protocol.State ⟨scope, resolution.mapping, resolution.world, selectedHeap, resolution.store, canonical⟩)
    (related : protocol.Relates initial selected)
    (written : Dynamic.ResolvedPlaceWrites (fun _ value => Dynamic.BitNotSnapshot target.selected value) selectedHeap target updated after)
    (operator : Option BinaryOp) (invalid : Word) :
    ∃ commit : Execution compilation.checked registry functions cells instances prepared (renamedCodes codes ξ)
        coreEnvironment resolution.store resolution.mapping resolution.world resolution.target resolution.values
        resolution.snapshot selectedHeap after updated operator invalid,
      RuntimeEnvironmentHasTypes commit.finalWorld
        (writtenEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) .unit commit.replacement commit.value coreEnvironment)
        (writtenContext prepared (SourceCoreCalls.packArguments codes).type actualContext) ambient.definitions ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨scope, resolution.mapping, commit.finalWorld, after, commit.finalStore, canonical⟩ := by
  obtain ⟨commit, typed⟩ := typed_of_write ordinaryCells layout ordinary registryExtension faithful observations profile
    environments agrees actualTyped resolution written operator invalid
  exact ⟨commit, typed, transport.extend selected (.refl _) commit.worlds commit.frame commit.metadata,
    protocol.trans related (transport.related selected (.refl _) commit.worlds commit.frame commit.metadata)⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedBitNotCommit
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedBitNotTail
/-! Exact Unit-RHS sequencing for the absent source RHS branch. These laws
compose or invert a commit constructed from independent source semantics. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedBitNotCommit
open Core Frontend SourceInference GeneralHeap DataPatternValues CompatiblePayload CompatibleHeap
open SourceCoreCompatibleDataPlaces DataPlaceExecution CoreProof

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient}
  {cells : GenericHeap.CellModel ambient.definitions}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions} {prepared : Prepared} {codes : List SourceCoreBasic.LoweredExpr}
  {environment : Environment} {store : Store} {mapping : LocationMap} {world : StoreTyping}
  {target : Location} {keys : List Value} {snapshot : Value} {before after : Dynamic.Heap}
  {updated : Dynamic.Value} {operator : Option BinaryOp} {invalid : Word}

private theorem unit_rhs (environment : Environment) (store : Store) :
    Evaluates environment store (shift 3 (LanguageResult.success .unit)) (.inRight .word .unit) store := by
  simpa only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success] using
    (Evaluates.inRight (leftType := .word) (environment := environment) (initialStore := store) Evaluates.unit)

theorem Execution.plug (execution : Execution checked registry functions cells instances prepared codes environment store mapping world
    target keys snapshot before after updated operator invalid)
    {next : Expr} {outputType : Ty} {result : Value} {finalStore : Store}
    (continuation : Evaluates (writtenEnvironment prepared.route.rootType target (packValues keys)
      (.inRight .unit snapshot) .unit execution.replacement execution.value environment)
      execution.finalStore (shift 7 next) result finalStore) :
    Evaluates (snapshotEnvironment prepared.route.rootType target (packValues keys) (.inRight .unit snapshot) environment)
      store (CompatiblePlacePrefixReflection.remainder prepared (SourceCoreCalls.packArguments codes).type
        (LanguageResult.success .unit) next outputType operator true invalid) result finalStore := by
  obtain ⟨optional, read⟩ := execution.read
  exact LanguageResult.bind_success _ (unit_rhs _ _) (LanguageResult.bind_success _ execution.modified
    (LanguageResult.bind_success _ execution.setter
      (.letE (.storeCell (.var rfl) read (.inRight (.var rfl)) execution.written) continuation)))

/-- A completed absent-RHS tail must reach the exact generated mapped commit.
The remaining seven-slot continuation is recovered as an output witness. -/
theorem Execution.reflects (execution : Execution checked registry functions cells instances prepared codes environment store mapping world
    target keys snapshot before after updated operator invalid)
    {next : Expr} {outputType : Ty} {result : Value} {finalStore : Store}
    (completed : Evaluates (snapshotEnvironment prepared.route.rootType target (packValues keys) (.inRight .unit snapshot) environment)
      store (CompatiblePlacePrefixReflection.remainder prepared (SourceCoreCalls.packArguments codes).type
        (LanguageResult.success .unit) next outputType operator true invalid) result finalStore) :
    Evaluates (writtenEnvironment prepared.route.rootType target (packValues keys)
      (.inRight .unit snapshot) .unit execution.replacement execution.value environment)
      execution.finalStore (shift 7 next) result finalStore := by
  cases completed with
  | caseLeft rhsEvaluated failed =>
    have impossible := (evaluation_deterministic rhsEvaluated (unit_rhs _ _)).1
    cases impossible
  | caseRight rhsEvaluated remaining =>
    obtain ⟨same, stores⟩ := evaluation_deterministic rhsEvaluated (unit_rhs _ _)
    cases same
    subst_vars
    cases remaining with
    | caseLeft modifiedEvaluated failed =>
      have impossible := (evaluation_deterministic modifiedEvaluated execution.modified).1
      cases impossible
    | caseRight modifiedEvaluated remaining =>
      obtain ⟨same, stores⟩ := evaluation_deterministic modifiedEvaluated execution.modified
      cases same
      subst_vars
      cases remaining with
      | caseLeft setterEvaluated failed =>
        have impossible := (evaluation_deterministic setterEvaluated execution.setter).1
        cases impossible
      | caseRight setterEvaluated remaining =>
        obtain ⟨same, stores⟩ := evaluation_deterministic setterEvaluated execution.setter
        cases same
        subst_vars
        cases remaining with
        | letE written continuation =>
          obtain ⟨optional, read⟩ := execution.read
          have actual : Evaluates
              (execution.value :: modifiedEnvironment prepared.route.rootType target (packValues keys)
                (.inRight .unit snapshot) .unit execution.replacement environment) execution.helperStore
              (.storeCell (.var 5) (.inRight .unit (.var 0))) .unit execution.finalStore :=
            .storeCell (.var rfl) read (.inRight (.var rfl)) execution.written
          obtain ⟨same, stores⟩ := evaluation_deterministic written actual
          subst_vars
          exact continuation

theorem Execution.reflects_size (execution : Execution checked registry functions cells instances prepared codes environment store mapping world
    target keys snapshot before after updated operator invalid)
    {next : Expr} {outputType : Ty} {result : Value} {finalStore : Store} {size : Nat}
    (completed : CoreProof.EvaluationSize size (snapshotEnvironment prepared.route.rootType target (packValues keys) (.inRight .unit snapshot) environment)
      store (CompatiblePlacePrefixReflection.remainder prepared (SourceCoreCalls.packArguments codes).type
        (LanguageResult.success .unit) next outputType operator true invalid) result finalStore) :
    ∃ remainingSize, remainingSize < size ∧ CoreProof.EvaluationSize remainingSize (writtenEnvironment prepared.route.rootType target (packValues keys)
      (.inRight .unit snapshot) .unit execution.replacement execution.value environment)
      execution.finalStore (shift 7 next) result finalStore := by
  cases completed with
  | caseLeft rhsEvaluated failed =>
    have impossible := (evaluation_deterministic rhsEvaluated.sound (unit_rhs _ _)).1
    cases impossible
  | caseRight rhsEvaluated remaining =>
    obtain ⟨same, stores⟩ := evaluation_deterministic rhsEvaluated.sound (unit_rhs _ _)
    cases same
    subst_vars
    cases remaining with
    | caseLeft modifiedEvaluated failed =>
      have impossible := (evaluation_deterministic modifiedEvaluated.sound execution.modified).1
      cases impossible
    | caseRight modifiedEvaluated remaining =>
      obtain ⟨same, stores⟩ := evaluation_deterministic modifiedEvaluated.sound execution.modified
      cases same
      subst_vars
      cases remaining with
      | caseLeft setterEvaluated failed =>
        have impossible := (evaluation_deterministic setterEvaluated.sound execution.setter).1
        cases impossible
      | caseRight setterEvaluated remaining =>
        obtain ⟨same, stores⟩ := evaluation_deterministic setterEvaluated.sound execution.setter
        cases same
        subst_vars
        cases remaining with
        | letE written continuation =>
          obtain ⟨optional, read⟩ := execution.read
          have actual : Evaluates
              (execution.value :: modifiedEnvironment prepared.route.rootType target (packValues keys)
                (.inRight .unit snapshot) .unit execution.replacement environment) execution.helperStore
              (.storeCell (.var 5) (.inRight .unit (.var 0))) .unit execution.finalStore :=
            .storeCell (.var rfl) read (.inRight (.var rfl)) execution.written
          obtain ⟨same, stores⟩ := evaluation_deterministic written.sound actual
          subst_vars
          exact ⟨_, by omega, continuation⟩

/-- Prefix composition uses only the actual key, getter and unary executions. -/
theorem Execution.prefix_agreement
    {sourceTypes : List TypeSystem.Ty} {place : PlaceResolution} {leaf : TypeSystem.Ty}
    {before selectedHeap : Dynamic.Heap} {initialStore : Store} {initialMap : LocationMap} {initialWorld : StoreTyping}
    {sourceTarget : Dynamic.ResolvedPlace}
    (resolution : CompatibleCellPlaceResolution.Execution checked registry functions cells instances prepared codes sourceTypes place leaf sourceTarget
      environment initialStore initialMap initialWorld before selectedHeap)
    (execution : Execution checked registry functions cells instances prepared codes environment resolution.store resolution.mapping resolution.world
      resolution.target resolution.values resolution.snapshot selectedHeap after updated operator invalid)
    {index : Nat}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target))
    (next : Expr) (output : Ty) :
    ContinuationAgreement environment initialStore
      (execute prepared (.var index) (SourceCoreCalls.packArguments codes) (LanguageResult.success .unit) next output operator true invalid)
      (writtenEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
        (.inRight .unit resolution.snapshot) .unit execution.replacement execution.value environment)
      execution.finalStore (shift 7 next) := by
  obtain ⟨optional, read⟩ := execution.read
  exact (ContinuationAgreement.letE (.var lookup)).trans
    ((ContinuationAgreement.bind resolution.keysEvaluated).trans
      ((ContinuationAgreement.bind resolution.snapshotEvaluated).trans
        ((ContinuationAgreement.bind (unit_rhs _ _)).trans
          ((ContinuationAgreement.bind execution.modified).trans
            ((ContinuationAgreement.bind execution.setter).trans
              (ContinuationAgreement.letE (.storeCell (.var rfl) read (.inRight (.var rfl)) execution.written)))))))

end Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedBitNotCommit
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedBitNotFaults
/-! Pure failure phases consume the actual completed key or RHS execution.
The live root, fault token, reached diagnostic receipt, and caller transition
remain tied to that execution; no child-meaning callback is introduced. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedBitNotFaults
open CompatibleRenamedPlace
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces DataPlaceExecution
universe u v

variable {compilation : SourceCoreCompatibleDataPlaces.Context}
  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
  {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
  {administrativeContext actualContext : Core.Context} {ξ : Renaming}
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
  {before after : Dynamic.Heap} {store : Store} {index : Nat}
  {location : Dynamic.Location} {initialCell currentCell : Dynamic.Cell}
  {resolved : List Dynamic.EvaluatedProjection}

include ordinaryCells in
theorem preserves_projection
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext .unit)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (keys : CompatibleCellPlaceTargetKeys.Execution compilation.checked registry functions cells instances prepared place
      (renamedCodes codes ξ) sourceTypes location resolved coreEnvironment before after store mapping world (ξ index))
    (keyPost : ProtectedStateTransition.Transition protocol initialState
      ⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before place.projections resolved after)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {initial : Option Dynamic.Value} {reason : Dynamic.SemanticFault}
    (initialValue : Dynamic.RootInitialValue currentCell initial)
    (fault : Dynamic.ProjectionsFaults initial resolved reason)
    (next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceBitNotFaults program context evidence source environment before place reason after ∧
      Dynamic.RootInitialValue currentCell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps resolved reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) (LanguageResult.success .unit) next outputType
          (binaryOperator (prepared.route.leafType = .integer) .equal) true invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore ∧
      ProtectedPlaceReachedDiagnostics.MissingPost compilation.checked registry functions protocol source site place prepared leaf initialState
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ reason token := by
  have getterTyped := getter_typed layout (virtual_closed layout ordinary) (environment_respects environments.runtime_hasTypes actualTyped agrees)
  obtain ⟨keyState, keyStateRelated⟩ := keyPost
  have cellEq := currentRead.functional keys.read
  have cellOrdinary : currentCell.generalized = none := cellEq ▸ keys.ordinary
  have cellType : currentCell.type = prepared.route.rootSourceType := cellEq ▸ keys.type
  have present : ∃ sourceRoot, initial = some sourceRoot := by
    cases initial with
    | some value => exact ⟨value, rfl⟩
    | none => cases fault
  obtain ⟨sourceRoot, rfl⟩ := present
  have rootExists := CompatibleCellPlaceRoot.root_of_initial ordinaryCells keys.heaps keys.reference
    currentRead cellOrdinary initialValue (fun k v same => layout.virtual k v (cellType.symm.trans same)) registryExtension
  obtain ⟨optional, rootValue, root⟩ := rootExists
  have keyRelated : DataExpressionSequence.Values (payloadModel compilation.checked registry functions) keys.keyMap keys.keyWorld sourceTypes (codes.map (·.type)) keys.sources keys.values := by
    simpa only [renamedCodes_types] using keys.related
  have arguments := layout.views.arguments keys.shaped keyRelated (fun _ _ found => by simpa only [Nat.zero_add] using found)
  have currentPath : PreparedPath compilation.checked source site currentCell.type place.projections
      0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
  have currentArguments : Arguments compilation.checked registry functions keys.keyMap keys.keyWorld source site keys.values
      currentPath resolved := by simpa only [cellType] using arguments
  obtain ⟨token, count, receipt, tree⟩ := currentArguments.faultTree root.payload fault prepared
  have keyLength : prepared.keyTypes.length = keys.values.length := layout.keyTypes ▸ keyRelated.length.2
  obtain ⟨finalStore, administrative, _, _, evaluated, appended, _⟩ :=
    faultTree_at root tree layout.nonempty faithful observations keyLength
      (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
      (SourceCoreCalls.packArguments codes).type (.var 1) (.var 0) (.var rfl) (.var rfl)
  have typedEnvironment : RuntimeEnvironmentHasTypes keys.keyWorld
      (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
      ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
        actualContext) ambient.definitions :=
    .cons (CompatiblePlaceResolution.values_typed keyRelated)
      (.cons (.cellRef keys.reference.typed) (actualTyped.weaken keys.worlds))
  obtain ⟨finalWorld, extension, finalHeaps, _, frame⟩ :=
    CellMappingHeap.evaluation_preserves_frame keys.heaps typedEnvironment getterTyped evaluated appended
  let reached := transport.extend keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after)
  have phaseRelated := transport.related keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after)
  refine ⟨token, count, sourceRoot, finalStore, keys.keyMap, finalWorld,
    .target (.projectionRead lookup initialRead trace currentRead initialValue fault), initialValue, receipt, ?_,
    finalHeaps,
    keys.maps, keys.worlds.trans extension, keys.frame.trans frame, keys.metadata,
    keys.effect.trans (appended.symm ▸ CellAwareScopeAuthority.Effect.append keys.keyStore administrative
      (.refl after) (.refl keys.keyMap) extension),
    reached, protocol.trans keyStateRelated phaseRelated,
    ⟨⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩, keyState, location, keys.target,
      currentCell, optional, sourceRoot, rootValue, keys.values, resolved, count, currentPath,
      keyStateRelated, phaseRelated, rfl, rfl, rfl, extension, frame, root, cellType, currentArguments, fault, receipt, tree⟩⟩
  unfold execute
  simp only [packed_renamed_type]
  exact .letE (.var keys.selected)
    (LanguageResult.bind_success _ keys.evaluated (LanguageResult.bind_failure _ evaluated))

include ordinaryCells in
theorem preserves_uninitialized
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext .unit)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (keys : CompatibleCellPlaceTargetKeys.Execution compilation.checked registry functions cells instances prepared place
      (renamedCodes codes ξ) sourceTypes location resolved coreEnvironment before after store mapping world (ξ index))
    (keyPost : ProtectedStateTransition.Transition protocol initialState
      ⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before place.projections resolved after)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (empty : currentCell.value = none)
    (notMapping : ¬ ∃ key value, currentCell.type = .mapping key value)
    (hasProjection : resolved ≠ [])
    (next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ finalStore finalMap finalWorld,
      Dynamic.SourcePlaceBitNotFaults program context evidence source environment before place
        (.uninitializedLocation location) after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) (LanguageResult.success .unit) next outputType
          (binaryOperator (prepared.route.leafType = .integer) .equal) true invalidOperand)
        (.inLeft outputType (.word prepared.invalidProjection)) finalStore ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore ∧
      ProtectedPlaceReachedDiagnostics.UninitializedPost compilation.checked registry functions protocol environment place prepared initialState
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ location := by
  have cellEq := currentRead.functional keys.read
  have cellOrdinary : currentCell.generalized = none := cellEq ▸ keys.ordinary
  have cellType : currentCell.type = prepared.route.rootSourceType := cellEq ▸ keys.type
  have noVirtual : prepared.route.rootMapping = none := ordinary (fun key value same => notMapping ⟨key, value, cellType.trans same⟩)
  obtain ⟨optional, native, represented⟩ := CompatibleCellPlaceRoot.read_at ordinaryCells keys.heaps keys.reference currentRead cellOrdinary
  have absent : optional = .inLeft prepared.route.rootType .unit := by
    cases represented with
    | uninitialized => rfl
    | initialized => cases empty
  rw [absent] at native
  have evaluated : Evaluates (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
      keys.keyStore (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
      (.inLeft prepared.optionalLeaf (.word prepared.invalidProjection)) keys.keyStore := by
    apply Evaluates.apply .lambda (.pair (.loadCell (.var rfl) native) (.var rfl))
    cases steps : prepared.steps with
    | nil => exact (layout.nonempty steps).elim
    | cons head tail =>
      simp only [normalizeRoot, noVirtual, LanguageResult.failure]
      exact .caseLeft (.first (.var rfl)) (.inLeft .word)
  obtain ⟨keyState, keyRelated⟩ := keyPost
  refine ⟨keys.keyStore, keys.keyMap, keys.keyWorld,
    .target (.uninitialized lookup initialRead trace currentRead empty notMapping hasProjection), ?_,
    keys.heaps, keys.maps, keys.worlds, keys.frame, keys.metadata, keys.effect,
    keyState, keyRelated,
    ⟨⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩, keyState, keys.target, currentCell,
      .inLeft prepared.route.rootType .unit, keys.sources, resolved, keyRelated, protocol.refl keyState, rfl, rfl, rfl,
      .refl _, .refl _ _, lookup, currentRead, keys.reference, native, absent ▸ represented, cellType, empty, notMapping, layout.nonempty, keys.shaped, hasProjection⟩⟩
  unfold execute
  simp only [packed_renamed_type]
  exact .letE (.var keys.selected)
    (LanguageResult.bind_success _ keys.evaluated (LanguageResult.bind_failure _ evaluated))

end Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedBitNotFaults
end
