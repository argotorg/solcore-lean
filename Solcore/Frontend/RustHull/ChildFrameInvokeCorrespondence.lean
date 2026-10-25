import Solcore.Frontend.RustHull.ChildFrameStateFrameCorrespondence
import Solcore.Frontend.RustHull.ChildFrameResultCorrespondence
import Solcore.Frontend.RustHull.RuntimeLinkedReturnDataEffectsFrameCorrespondence

/-! A compiled catalog child executes through its actual fresh allocator,
captured frame closure and completion wrapper. The resulting shared state and
code links are returned to account dispatch; caller-local cells are retained. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildFrameCorrespondence
open Core Correspondence ScalarExecution CodeBuilder

theorem invoke_evaluates {source : ChildFrameSemantics.Code} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame source.program source.body (RuntimeExtendedInitializedEffects.slots true) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram (ContractReturnDataCorrespondence.supported true) source.functions)
    {depth : Nat} {environment captured : Environment} {initial : Store}
    {frame dispatcher creator gas code size known function : Code} {closure : Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : CodeValue depth environment function closure)
    (parent : RuntimeCallEffectsSemantics.State) (request : AccountCallSemantics.Request)
    (sharedState : AccountCallSemantics.Shared)
    {shared : AccountRuntime.References} {sharedCells : List InitializedCell}
    {accounts : StorageCorrespondence.Accounts} (world : accounts.map Prod.fst = sharedState.world)
    (references : RuntimeReferences depth environment shared sharedCells)
    (signature : sharedCells.map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse)
    (initialized : InitializedCells sharedCells initial) (separate : CellLocations sharedCells)
    (observed : ∀ cell ∈ sharedCells, Observed accounts (Initial parent request sharedState source.bytes) source.bytes cell)
    {creatorLocation : Nat} {creatorValue : Value}
    (creatorRelated : CodeValue depth environment creator (.cellRef (OptionalCell.cellType Creation.callbackType) creatorLocation))
    (creatorFound : initial.read? creatorLocation = some creatorValue)
    (creatorSeparate : ∀ cell ∈ sharedCells, cell.location ≠ creatorLocation)
    (frameRelated : CodeValue depth environment frame (CallTransportCorrespondence.requestValue request))
    (gasRelated : CodeValue depth environment gas (optionalWordValue (some request.gas)))
    (codeRelated : CodeValue depth environment code (WordMapping.encode (Memory.packBytes source.bytes)))
    (sizeRelated : CodeValue depth environment size (.word (Word.ofNatModulo source.bytes.length)))
    (knownRelated : CodeValue depth environment known (.bool true))
    {locations : AccountCallCorrespondence.SharedLocations} {anchors : List CatalogWorldCorrespondence.Anchor}
    (sharedReferences : AccountCallCorrespondence.SharedReferences depth environment shared locations)
    (linked : RuntimeLinkedWorldCorrespondence.StateRel anchors sharedState.world locations.world initial)
    {status : Semantics.Result Semantics.Value} {finalSource : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    {response : Semantics.Result AccountCallSemantics.Response}
    (evaluated : Semantics.EvalFunction source.functions (RuntimeReturnDataEffectsSemantics.effects (some source.bytes))
      source.entry [] ⟨[], Initial parent request sharedState source.bytes⟩ status finalSource)
    (responded : ChildResultSemantics.Respond
      (ChildFrameSemantics.completedStatus status finalSource.external.runtime.runtime.runtime.runtime)
      finalSource.external.runtime.runtime.runtime.runtime response) :
    ∃ target final, Core.Evaluates environment initial
      (AccountRuntime.allocateFrame (RuntimeExtendedInitializedEffects.slots true) shared frame dispatcher creator gas code size known
        (fun values => bind (apply function (packet values)) AccountRuntime.childResult) depth) target final ∧
      CallTransportCorrespondence.ResponseRel response target ∧
      AccountCallCorrespondence.LinkedSharedStateRel anchors locations
        (RuntimeCallEffectsSemantics.shared ⟨finalSource.external, request.depth⟩) final ∧
      AccountCallCorrespondence.SharedFrame locations initial final := by
  apply allocateFrame_initializes parent request sharedState source.bytes world references signature initialized separate observed
    creatorRelated creatorFound creatorSeparate frameRelated gasRelated codeRelated sizeRelated knownRelated
    (fun values => bind (apply function (packet values)) AccountRuntime.childResult)
    (fun target final => CallTransportCorrespondence.ResponseRel response target ∧
      AccountCallCorrespondence.LinkedSharedStateRel anchors locations
        (RuntimeCallEffectsSemantics.shared ⟨finalSource.external, request.depth⟩) final ∧
      AccountCallCorrespondence.SharedFrame locations initial final)
  intro extra suffix cells values valuesRelated stored cellsSignature allSeparate origins sharedOrigins ready
  have cellsSeparate := allSeparate.subset (fun _ member => List.mem_append_right _ member)
  have unique : (sharedCells.map InitializedCell.name).Nodup := by
    have names := congrArg (List.map Prod.fst) signature
    simp only [List.map_map, Function.comp_def, List.map_reverse] at names
    rw [names]
    decide
  have locationsEqual : sharedLocations ready.layout = locations :=
    shared_references_unique ((shared_cells ready sharedOrigins).references unique references) sharedReferences
  have initialLinked : RuntimeLinkedWorldCorrespondence.StateRel anchors sharedState.world ready.layout.storage.world (initial ++ suffix) := by
    have same := congrArg AccountCallCorrespondence.SharedLocations.world locationsEqual
    change ready.layout.storage.world = locations.world at same
    rw [same]
    exact linked.retained (StoreRetains.append initial suffix)
  have linkedState := RuntimeLinkedReturnDataEffectsCorrespondence.of_base ready.related initialLinked
  let slots := cells.map InitializedCell.effectSlot
  have slotTypes : RuntimeReturnDataEffectsFrameCorrespondence.slotTypes slots = RuntimeExtendedInitializedEffects.slots true := by
    simpa only [RuntimeReturnDataEffectsFrameCorrespondence.slotTypes, RuntimeLogEffectsFrameCorrespondence.slotTypes,
      MemoryFrameCorrespondence.slotTypes, slots, List.map_map, Function.comp_def, InitializedCell.effectSlot] using cellsSignature
  have environmentRelated := initialized_environment cells (RuntimeExtendedInitializedEffects.initialized_unique cellsSignature)
    (Value.unit :: bundleValues (cells.map InitializedCell.reference) :: captured)
  have runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (RuntimeReturnDataEffectsFrameCorrespondence.slotTypes slots)) Renaming.id
      ((cells.map InitializedCell.reference).reverse ++ Value.unit :: bundleValues (cells.map InitializedCell.reference) :: captured) := by
    simpa only [RuntimeReturnDataEffectsFrameCorrespondence.slotTypes, RuntimeLogEffectsFrameCorrespondence.slotTypes,
      MemoryFrameCorrespondence.slotTypes, slots, List.map_map, Function.comp_def, InitializedCell.effectSlot] using environmentRelated
  have member := ready.members
  obtain ⟨extension, statusValue, accounts', bodyStore, represented, statusRelated, called, state, _⟩ :=
    RuntimeLinkedReturnDataEffectsFrameCorrespondence.compileFrame_call_preserves_observed
      (by simpa only [slotTypes] using accepted)
      (by simpa only [ContractReturnDataCorrespondence.supported_actual slotTypes, ChildFrameSemantics.Code.functions,
        ChildFrameSemantics.Code.entry, AccountRuntime.frameFunction, AccountRuntime.frameEntry] using eligible)
      closureRelated ((resolved.prepend extra).evaluates (initial ++ suffix))
      ((CodeValue.packet valuesRelated).evaluates (initial ++ suffix)) (by simp [slots]) runtime
      (RuntimeExtendedInitializedEffects.initialized_separate cellsSignature)
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots])) ready.codes
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots])) ready.mode linkedState ready.passive evaluated
  have baseState := RuntimeLinkedReturnDataEffectsCorrespondence.base_related state
  have finalShared : AccountCallCorrespondence.LinkedSharedStateRel anchors (sharedLocations ready.layout)
      (RuntimeCallEffectsSemantics.shared ⟨finalSource.external, request.depth⟩) bodyStore :=
    ⟨shared_state ready cellsSeparate baseState request.depth, RuntimeLinkedReturnDataEffectsCorrespondence.linked_related state⟩
  have retained := parent_frame ready signature origins baseState
  rw [locationsEqual] at finalShared retained
  obtain ⟨target, final, resultRelated, executed, extractionRetains⟩ := bind_evaluates statusRelated represented responded called
  exact ⟨target, final, executed, resultRelated, finalShared.retained extractionRetains,
    retained.trans (AccountCallCorrespondence.SharedFrame.ofRetains extractionRetains)⟩

end Solcore.Frontend.RustHull.ChildFrameCorrespondence
