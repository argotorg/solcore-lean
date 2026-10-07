import Solcore.SourceSemantics.CoreLowering.CoreContinuationSize
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchHiddenPrefix
import Solcore.SourceSemantics.CoreLowering.ProtectedStateMatchPrefix

/-! The actual hidden-cell prefix derives runtime typing for both surviving
scrutinee temporaries and its new payload reference. Raw source type and erased
marker type remain separate, with exactly the allocator's world extension. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedHiddenPrefix
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly
open CallableIndexedHistory CallableIndexedAllocationCompletion CompatibleEncoding
universe u v

private theorem case_right {environment : Environment} {before middle : Store}
    {scrutinee left right : Expr} {leftType : Ty} {value : Value}
    (evaluated : Evaluates environment before scrutinee (.inRight leftType value) middle) :
    ContinuationAgreement environment before (.caseE scrutinee left right) (value :: environment) middle right := by
  constructor
  · intro result finalStore body; exact .caseRight evaluated body
  · intro result finalStore evaluation
    obtain ⟨_, sized⟩ := evaluation_has_size evaluation
    obtain ⟨_, _, body⟩ := sized.case_right evaluated
    exact body.sound

theorem Stateful.success_prefix_sized {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {source : TypedSource} {scope : SourceCoreSourceCells.Scope} {binder : TypedBinder}
    {payload outputType : Ty} {computation branches code : Expr} {internalReason : Word}
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (fresh : scope.any (fun binding => decide (binding.1 = binder.id)) = false)
    (accepted : SourceCoreSourceCells.letInitialized
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      source scope Renaming.id binder outputType payload computation
      (.caseE (.loadCell (.var 0)) (LanguageResult.failure outputType (.word internalReason)) branches) = .ok code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts frame model)
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitionsEq : layouts.definitions = definitions) (registered : frame.Registered definitions)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceType : TypeSystem.Ty}
    {sourceValue : Dynamic.Value} {value : Value} {contextLocation : Location} {native : NativeFrame}
    (represented : model.Represents mapping world sourceType sourceValue value payload)
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (evaluated : Evaluates actual before (computation.rename ξ) (.inRight .word value) store)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary contextLocation native) :
    ∃ hiddenHeap location nextStore nextWorld nextMap nextRef,
      Dynamic.Heap.Allocates heap sourceType (some sourceValue) location hiddenHeap ∧
      DataHeap.EnvRepresents catalog nextMap nextWorld administrative ((binder.id, payload) :: scope)
        environment (nextRef :: canonical) definitions ∧
      GenericHeap.HeapRepresents model nextMap nextWorld hiddenHeap nextStore ∧
      LocationMap.Extends mapping nextMap ∧ WorldExtends world nextWorld ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 1) ξ.lift).lift
        (value :: nextRef :: canonical) (value :: nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (value :: nextRef :: value :: actual)
        (payload :: OptionalCell.referenceType payload :: payload :: actualContext) definitions ∧
      ContinuationSize true actual before (code.rename ξ)
        (value :: nextRef :: value :: actual) nextStore
        (branches.rename (Renaming.comp (Renaming.insertion 1) ξ.lift).lift) ∧
      ∃ final : protocol.State ⟨(binder.id, payload) :: scope, nextMap, nextWorld, hiddenHeap, nextStore, nextRef :: canonical⟩,
        protocol.Relates initial final ∧ Nonempty (ProtectedStateTransition.ReturnTo protocol scope canonical
          ((binder.id, payload) :: scope) (nextRef :: canonical)) := by
  unfold SourceCoreSourceCells.letInitialized at accepted
  obtain ⟨allocationCode, compiled, sameCode⟩ := bind_ok accepted
  obtain ⟨allocation, annotation, same, emitted⟩ := accepted_receipts onError compiled
  cases sameCode
  rw [emitted]
  obtain ⟨captured, allocated, nextEnvironments, nextHeaps, framePreserved, payloadRead, transition⟩ :=
    CompatibleMatchHiddenAllocation.preserves_with_state allocation annotation same ordinary fresh protocol producer definitionsEq registered
      represented environments heaps agrees reference read initial (readyAt initial read) (Dynamic.Heap.Allocates.append (type := sourceType) (value := some sourceValue))
  obtain ⟨nextState, related⟩ := transition
  let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
  let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
    SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit value]
  refine ⟨_, _, nextStore, _, _, nextRef, .append, nextEnvironments, nextHeaps, ⟨_, rfl⟩, ⟨_, rfl⟩,
    framePreserved, ?_, ?_, ?_, nextState, related,
    ⟨ProtectedStateTransition.ReturnTo.binding stateBindings scope canonical binder.id payload nextRef⟩⟩
  · intro index foundValue found
    cases index with
    | zero => exact found
    | succ index => cases index with
      | zero => exact found
      | succ index => exact agrees found
  · have referenceTyped : RuntimeValueHasType
        (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload])
        nextRef (OptionalCell.referenceType payload) definitions := by
      obtain ⟨reference, same, typed⟩ := nextEnvironments.runtime_hasTypes.lookup (index := 0) (by rfl)
      have identical : nextRef = reference := Option.some.inj same
      cases identical
      exact typed
    exact .cons ((model.runtime_hasType represented).weaken ⟨_, rfl⟩)
      (.cons referenceTyped (.cons ((model.runtime_hasType represented).weaken ⟨_, rfl⟩) (actualTyped.weaken ⟨_, rfl⟩)))
  · simp only [LanguageResult.bind, Expr.rename, LoopRenaming.weakenOne]
    apply (ContinuationSize.bind evaluated).trans (b := true)
    apply (ContinuationSize.letE allocated).trans (b := true)
    have loaded : Evaluates (nextRef :: value :: actual) nextStore (.loadCell (.var 0))
        (.inRight .unit value) nextStore := .loadCell (.var rfl) payloadRead
    simpa [← Expr.rename_insertion, Expr.rename_comp, Expr.rename, Renaming.lift_comp,
      Renaming.lift, Renaming.insertion] using
      (ContinuationSize.case_right (left := (LanguageResult.failure outputType (.word internalReason)).rename
        (Renaming.comp (Renaming.insertion 1) ξ.lift).lift)
        (right := branches.rename (Renaming.comp (Renaming.insertion 1) ξ.lift).lift) loaded)


/-- Compatibility erasure of the same actual prefix. -/
theorem success_prefix_sized {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {source : TypedSource} {scope : SourceCoreSourceCells.Scope} {binder : TypedBinder}
    {payload outputType : Ty} {computation branches code : Expr} {internalReason : Word}
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (fresh : scope.any (fun binding => decide (binding.1 = binder.id)) = false)
    (accepted : SourceCoreSourceCells.letInitialized
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      source scope Renaming.id binder outputType payload computation
      (.caseE (.loadCell (.var 0)) (LanguageResult.failure outputType (.word internalReason)) branches) = .ok code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (definitionsEq : layouts.definitions = definitions) (registered : frame.Registered definitions)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceType : TypeSystem.Ty}
    {sourceValue : Dynamic.Value} {value : Value} {contextLocation : Location} {native : NativeFrame}
    (represented : model.Represents mapping world sourceType sourceValue value payload)
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (evaluated : Evaluates actual before (computation.rename ξ) (.inRight .word value) store) :
    ∃ hiddenHeap location nextStore nextWorld nextMap nextRef,
      Dynamic.Heap.Allocates heap sourceType (some sourceValue) location hiddenHeap ∧
      DataHeap.EnvRepresents catalog nextMap nextWorld administrative ((binder.id, payload) :: scope)
        environment (nextRef :: canonical) definitions ∧
      GenericHeap.HeapRepresents model nextMap nextWorld hiddenHeap nextStore ∧
      LocationMap.Extends mapping nextMap ∧ WorldExtends world nextWorld ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 1) ξ.lift).lift
        (value :: nextRef :: canonical) (value :: nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (value :: nextRef :: value :: actual)
        (payload :: OptionalCell.referenceType payload :: payload :: actualContext) definitions ∧
      ContinuationSize true actual before (code.rename ξ)
        (value :: nextRef :: value :: actual) nextStore
        (branches.rename (Renaming.comp (Renaming.insertion 1) ξ.lift).lift) := by
  obtain ⟨hiddenHeap, location, nextStore, nextWorld, nextMap, nextRef, allocated, nextEnv, nextHeaps,
    maps, worlds, frame, layout, typed, agreement, _final, _related, _return⟩ :=
    Stateful.success_prefix_sized onError ordinary fresh accepted
      ProtectedStateTransition.OrdinaryAllocation.unitProtocol
      (ProtectedStateTransition.MarkedAllocation.unitProducer layouts frame model)
      ProtectedStateTransition.MatchPrefix.unitBindings definitionsEq registered represented environments heaps agrees
      actualTyped reference read evaluated () (fun _ _ => True.intro)
  exact ⟨hiddenHeap, location, nextStore, nextWorld, nextMap, nextRef, allocated, nextEnv, nextHeaps,
    maps, worlds, frame, layout, typed, agreement⟩

theorem success_prefix_typed {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {source : TypedSource} {scope : SourceCoreSourceCells.Scope} {binder : TypedBinder}
    {payload outputType : Ty} {computation branches code : Expr} {internalReason : Word}
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (fresh : scope.any (fun binding => decide (binding.1 = binder.id)) = false)
    (accepted : SourceCoreSourceCells.letInitialized
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      source scope Renaming.id binder outputType payload computation
      (.caseE (.loadCell (.var 0)) (LanguageResult.failure outputType (.word internalReason)) branches) = .ok code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (definitionsEq : layouts.definitions = definitions) (registered : frame.Registered definitions)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceType : TypeSystem.Ty}
    {sourceValue : Dynamic.Value} {value : Value} {contextLocation : Location} {native : NativeFrame}
    (represented : model.Represents mapping world sourceType sourceValue value payload)
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (evaluated : Evaluates actual before (computation.rename ξ) (.inRight .word value) store) :
    ∃ hiddenHeap location nextStore nextWorld nextMap nextRef,
      Dynamic.Heap.Allocates heap sourceType (some sourceValue) location hiddenHeap ∧
      DataHeap.EnvRepresents catalog nextMap nextWorld administrative ((binder.id, payload) :: scope)
        environment (nextRef :: canonical) definitions ∧
      GenericHeap.HeapRepresents model nextMap nextWorld hiddenHeap nextStore ∧
      LocationMap.Extends mapping nextMap ∧ WorldExtends world nextWorld ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 1) ξ.lift).lift
        (value :: nextRef :: canonical) (value :: nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (value :: nextRef :: value :: actual)
        (payload :: OptionalCell.referenceType payload :: payload :: actualContext) definitions ∧
      ContinuationAgreement actual before (code.rename ξ)
        (value :: nextRef :: value :: actual) nextStore
        (branches.rename (Renaming.comp (Renaming.insertion 1) ξ.lift).lift) := by
  obtain ⟨hiddenHeap, location, nextStore, nextWorld, nextMap, nextRef, allocated, nextEnv, nextHeaps,
    maps, worlds, frame, layout, typed, agreement⟩ :=
    success_prefix_sized onError ordinary fresh accepted definitionsEq registered represented environments heaps agrees
      actualTyped reference read evaluated
  exact ⟨hiddenHeap, location, nextStore, nextWorld, nextMap, nextRef, allocated, nextEnv, nextHeaps,
    maps, worlds, frame, layout, typed, agreement.agreement⟩


end Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedHiddenPrefix
