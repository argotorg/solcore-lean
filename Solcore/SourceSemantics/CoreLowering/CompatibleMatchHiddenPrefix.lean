import Solcore.SourceSemantics.CoreLowering.CompatibleMatchHiddenAllocation

/-! Successful scrutinee evaluation reaches the actual compatible branch
fold after exactly one hidden source allocation and two administrative cells.
The raw source heap type and source lexical environment are retained. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchHiddenPrefix
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly
open CallableIndexedHistory CallableIndexedAllocationCompletion CompatibleMatchHiddenAllocation
open CompatibleEncoding (bind_ok)

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

/-- Scrutinee failure retains its effects and executes no allocator or arm. -/
theorem failure_prefix {source : TypedSource} {scope : SourceCoreSourceCells.Scope} {binder : TypedBinder}
    {allocator : SourceCoreSourceCells.Allocator} {payload outputType : Ty}
    {computation branches code : Expr} {internalReason reason : Word}
    (accepted : SourceCoreSourceCells.letInitialized (some allocator) source scope Renaming.id binder
      outputType payload computation (.caseE (.loadCell (.var 0))
        (LanguageResult.failure outputType (.word internalReason)) branches) = .ok code)
    {environment : Environment} {before after : Store} {ξ : Renaming} {inputType : Ty}
    (failed : Evaluates environment before (computation.rename ξ) (.inLeft inputType (.word reason)) after) :
    Evaluates environment before (code.rename ξ) (.inLeft outputType (.word reason)) after := by
  unfold SourceCoreSourceCells.letInitialized at accepted
  obtain ⟨allocation, compiled, same⟩ := bind_ok accepted
  cases same
  exact .caseLeft failed (.inLeft (.var rfl))

/-- The initializer evaluation is a compositional boundary. Everything after
it, including the marked hidden allocation and load, follows from actual
compiler receipts and live slots. Both finite continuation directions hold. -/
theorem success_prefix {layouts : SourceCoreAllocationLayouts.Prepared}
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
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceType : TypeSystem.Ty}
    {sourceValue : Dynamic.Value} {value : Value} {contextLocation : Location} {native : NativeFrame}
    (represented : model.Represents mapping world sourceType sourceValue value payload)
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
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
      ContinuationAgreement actual before (code.rename ξ)
        (value :: nextRef :: value :: actual) nextStore
        (branches.rename (Renaming.comp (Renaming.insertion 1) ξ.lift).lift) := by
  unfold SourceCoreSourceCells.letInitialized at accepted
  obtain ⟨allocationCode, compiled, sameCode⟩ := bind_ok accepted
  obtain ⟨allocation, annotation, same, emitted⟩ := accepted_receipts onError compiled
  cases sameCode
  rw [emitted]
  obtain ⟨captured, allocated, nextEnvironments, nextHeaps, framePreserved, payloadRead⟩ :=
    CompatibleMatchHiddenAllocation.preserves allocation annotation same ordinary fresh definitionsEq registered
      represented environments heaps agrees reference read (Dynamic.Heap.Allocates.append (type := sourceType) (value := some sourceValue))
  let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
  let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
    SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit value]
  refine ⟨_, _, nextStore, _, _, nextRef, .append, nextEnvironments, nextHeaps, ⟨_, rfl⟩, ⟨_, rfl⟩,
    framePreserved, ?_, ?_⟩
  · intro index foundValue found
    cases index with
    | zero => exact found
    | succ index => cases index with
      | zero => exact found
      | succ index => exact agrees found
  · simp only [LanguageResult.bind, Expr.rename, LoopRenaming.weakenOne]
    apply (ContinuationAgreement.bind evaluated).trans
    apply (ContinuationAgreement.letE allocated).trans
    have loaded : Evaluates (nextRef :: value :: actual) nextStore (.loadCell (.var 0))
        (.inRight .unit value) nextStore := .loadCell (.var rfl) payloadRead
    simpa [← Expr.rename_insertion, Expr.rename_comp, Expr.rename, Renaming.lift_comp,
      Renaming.lift, Renaming.insertion] using
      (case_right (left := (LanguageResult.failure outputType (.word internalReason)).rename
        (Renaming.comp (Renaming.insertion 1) ξ.lift).lift)
        (right := branches.rename (Renaming.comp (Renaming.insertion 1) ξ.lift).lift) loaded)

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchHiddenPrefix
