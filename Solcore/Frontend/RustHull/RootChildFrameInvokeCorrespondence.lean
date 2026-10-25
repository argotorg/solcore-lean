import Solcore.Frontend.RustHull.RootChildCatalogRunCorrespondence
import Solcore.Frontend.RustHull.RuntimeCallModeCallbackCorrespondence
import Solcore.Frontend.RustHull.ChildFrameCallModeAllocationCorrespondence
import Solcore.Frontend.RustHull.RuntimeCallModeEffectsFrameCorrespondence

/-! A callable child frame uses the actual allocator and installed dispatcher.
The callback interface is discharged by induction on the independent call tree. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RootChildFrameCorrespondence
open Core Correspondence ScalarExecution CodeBuilder ChildFrameCorrespondence
open RootChildCatalogExecutionCorrespondence (FrameExecution CatalogConnection RootFrame)

/-- Internal callback interface, uniform over actual catalog captures and fresh
frame layouts. It is not a premise of the public execution theorem. -/
def CatalogCallbacks (rootSource : ChildFrameSemantics.Code) (sourceCatalog : ChildFrameSemantics.Catalog)
    (catalog : List AccountRuntime.CodeDefinition) (anchors : List CatalogWorldCorrespondence.Anchor)
    (children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children) : Prop :=
  ∀ {fuel : Nat} {others : List Core.Expr},
    ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others →
    CatalogConnection rootSource sourceCatalog catalog anchors →
  ∀ {captured : Environment} {catalogValues : List Value} {rootClosure : Value},
    CapturedClosures captured others catalogValues →
    RootFrame rootSource fuel captured rootClosure →
  ∀ {images : List (Nat × List UInt8)} {cells : List InitializedCell} {creator : Nat}
    {layout : RuntimeCallEffectsCorrespondence.Layout} {initial : Store},
    (capture : ObjectCallbackCapture (RuntimeExtendedInitializedEffects.slots true) (others.length + 1) images catalog
      (rootClosure :: catalogValues) cells layout.dispatcher creator initial) →
    (inventory : NestedChildCallbackContextCorrespondence.Inventory layout cells creator) →
    (references : AccountCallCorrespondence.SharedReferences capture.depth capture.environment capture.shared
      (RuntimeCallEffectsCorrespondence.sharedLocations layout)) →
    (mode : AccountCallSemantics.Mode) → (parent : RuntimeCallEffectsSemantics.State) →
    (∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
      ContractEnvironmentCorrespondence.initializedValue parent.runtime.runtime.runtime.runtime.environment cell) →
    let dispatcher := ContractCallCorrespondence.captured_dispatcher capture _ references
    AccountCallModeCorrespondence.ChildRunPreservation mode anchors (RuntimeCallEffectsCorrespondence.sharedLocations layout)
      dispatcher.shared dispatcher.runFrame (children parent)
      (RuntimeChildCallEffectsCorrespondence.childReady layout
        (NestedChildCallbackContextCorrespondence.context inventory capture.closure)) dispatcher.depth dispatcher.captured

theorem frame_execution_of_callbacks {rootSource : ChildFrameSemantics.Code} {sourceCatalog : ChildFrameSemantics.Catalog}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    {children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children}
    (callbacks : CatalogCallbacks rootSource sourceCatalog catalog anchors children) :
    FrameExecution rootSource sourceCatalog catalog anchors (RuntimeCallModeSemantics.effectsWith children) := by
  intro source fuel compiled others accepted eligible catalogCompiled connection captured catalogValues rootClosure catalogCaptured rootCaptured
    images sharedCells dispatcherLocation creatorLocation initial capture depth environment frame dispatcher creator gas code size known function closure
    closureRelated resolved parent request sharedState accounts world references signature initialized separate observed
    creatorRelated creatorFound creatorSeparate dispatcherRelated dispatcherSeparate creatorDispatcher
    frameRelated gasRelated codeRelated sizeRelated knownRelated locations sharedReferences linked status finalSource response evaluated responded
  obtain ⟨creatorValue, creatorRead⟩ := creatorFound
  apply ChildFrameModeCorrespondence.allocateModeCallFrame_initializes parent request sharedState source.bytes world references signature initialized separate observed
    creatorRelated creatorRead creatorSeparate dispatcherRelated capture.stored dispatcherSeparate creatorDispatcher
    frameRelated gasRelated codeRelated sizeRelated knownRelated
    (fun values => bind (apply function (packet values)) AccountRuntime.childResult)
    (fun target final => CallTransportCorrespondence.ResponseRel response target ∧
      AccountCallCorrespondence.LinkedSharedStateRel anchors locations (RuntimeCallEffectsSemantics.shared finalSource.external) final ∧
      AccountCallCorrespondence.SharedFrame locations initial final)
  intro extra suffix cells values valuesRelated stored cellsSignature allSeparate origins sharedOrigins modeReady
  let ready := modeReady.base
  let inventory := ready.nestedInventory dispatcherSeparate creatorDispatcher
  let capture' := NestedChildCallbackContextCorrespondence.withDispatcher capture _ ready.call.dispatcherEqual
  have capturedReferences := ContractChildCallCorrespondence.inventory_references inventory.base capture'.references
  let dispatchCapture := ContractCallCorrespondence.captured_dispatcher capture' _ capturedReferences
  let handlers := modeReady.handlers dispatchCapture
  let callbackContext := NestedChildCallbackContextCorrespondence.context inventory capture.closure
  have locationsEqual : RuntimeCallEffectsCorrespondence.sharedLocations ready.call.layout = locations :=
    shared_references_unique (ContractChildCallCorrespondence.inventory_references inventory.base references) sharedReferences
  have initialLinked : RuntimeLinkedWorldCorrespondence.StateRel anchors sharedState.world ready.call.layout.storage.world (initial ++ suffix) := by
    have same := congrArg AccountCallCorrespondence.SharedLocations.world locationsEqual
    change ready.call.layout.storage.world = locations.world at same
    rw [same]
    exact linked.retained (StoreRetains.append initial suffix)
  have initialState := modeReady.related dispatchCapture callbackContext initialLinked
    (ready.nestedCaptured dispatcherSeparate creatorDispatcher)
  let slots := cells.map InitializedCell.effectSlot
  have slotTypes : RuntimeCallModeEffectsFrameCorrespondence.slotTypes slots = RuntimeExtendedInitializedEffects.slots true := by
    simpa only [RuntimeCallModeEffectsFrameCorrespondence.slotTypes, RuntimeReturnDataEffectsFrameCorrespondence.slotTypes,
      RuntimeLogEffectsFrameCorrespondence.slotTypes, MemoryFrameCorrespondence.slotTypes, slots, List.map_map,
      Function.comp_def, InitializedCell.effectSlot] using cellsSignature
  have environmentRelated := initialized_environment cells (RuntimeExtendedInitializedEffects.initialized_unique cellsSignature)
    (Value.unit :: bundleValues (cells.map InitializedCell.reference) :: captured)
  have runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (RuntimeCallModeEffectsFrameCorrespondence.slotTypes slots)) Renaming.id
      ((cells.map InitializedCell.reference).reverse ++ Value.unit :: bundleValues (cells.map InitializedCell.reference) :: captured) := by
    simpa only [RuntimeCallModeEffectsFrameCorrespondence.slotTypes, RuntimeReturnDataEffectsFrameCorrespondence.slotTypes,
      RuntimeLogEffectsFrameCorrespondence.slotTypes, MemoryFrameCorrespondence.slotTypes, slots, List.map_map,
      Function.comp_def, InitializedCell.effectSlot] using environmentRelated
  have member : ∀ slot ∈ RuntimeCallInitializedEffects.baseSlots ready.call.layout.toReturnDataLayout, slot ∈ slots := by
    simpa only [ready.call.baseEqual] using ready.base.members
  have callCodes : ∀ imageCells, ready.call.layout.toReturnDataLayout.codeCells = some imageCells →
      (⟨"code", WordMapping.type, imageCells.code⟩ : EffectSlot) ∈ slots ∧
      (⟨"codeKnown", .bool, imageCells.known⟩ : EffectSlot) ∈ slots := by
    rw [ready.call.baseEqual]
    exact ready.base.codes
  have slot_present (name : String) (type : Core.Ty)
      (present : (name, type) ∈ RuntimeExtendedInitializedEffects.slots true) :
      ∃ location, (⟨name, type, location⟩ : EffectSlot) ∈ slots := by
    rw [← cellsSignature] at present
    obtain ⟨cell, member, same⟩ := List.mem_map.mp present
    obtain ⟨named, typed⟩ := Prod.mk.inj same
    exact ⟨cell.location, List.mem_map.mpr ⟨cell, member, by simp only [InitializedCell.effectSlot, named, typed]⟩⟩
  have bodyCallbacks : ∀ {world state current},
      StateRel (RuntimeCallModeEffectsCorrespondence.model ready.call.layout
        (prefixRead ready.call.layout.boundary (initial ++ suffix)) slots (some source.bytes) handlers anchors callbackContext)
        world state current →
      ∀ operation, RuntimeCallModeEffectsCorrespondence.CallbackPreservation ready.call.layout handlers anchors callbackContext children operation state.external := by
    intro world state current related operation
    have base := RuntimeCallModeEffectsCorrespondence.base_related related
    have ambient := ChildCallbackContextCorrespondence.parent_observed inventory.base ready.sharedMembers base related.external.2.2.1.2.1.1
    apply RuntimeCallModeEffectsCorrespondence.callback_preserves
    · exact RuntimeCallEffectsCorrespondence.source_eq base
    · exact AccountCallModeCorrespondence.ChildRunPreservation.strengthen
        (callbacks catalogCompiled connection catalogCaptured rootCaptured capture' inventory capturedReferences operation.mode state.external ambient)
        (fun _ valid => ⟨valid.1, valid.2.1⟩)
  obtain ⟨extension, statusValue, accounts', bodyStore, represented, statusRelated, called, state, _⟩ :=
    RuntimeCallModeEffectsFrameCorrespondence.compileFrame_call_preserves_observed (withCode := true) (layout := ready.call.layout) (handlers := handlers)
      (by simpa only [slotTypes] using accepted)
      (by simpa only [ContractCallModeCorrespondence.supported_actual slotTypes, ChildFrameSemantics.Code.functions,
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
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      callCodes
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (by
        change ready.call.layout.toReturnDataLayout.codeCells.isSome = true
        rw [ready.call.baseEqual]
        exact ready.base.mode)
      ready.call.depthMember ready.call.handlerMember modeReady.callCode.member modeReady.delegateCall.member
      (slot_present "caller" .word (by simp [RuntimeExtendedInitializedEffects.slots, Effects.slots]))
      (slot_present "callvalue" .word (by simp [RuntimeExtendedInitializedEffects.slots, Effects.slots])) initialState
      (by simpa only [ready.call.baseEqual] using ready.base.passive) ready.callPassive bodyCallbacks evaluated
  have finalShared := ready.linked_shared_state state
  have retained := ready.parent_frame origins state
  rw [locationsEqual] at finalShared retained
  obtain ⟨target, final, resultRelated, executed, extractionRetains⟩ := bind_evaluates statusRelated represented responded called
  exact ⟨target, final, executed, resultRelated, finalShared.retained extractionRetains,
    retained.trans (AccountCallCorrespondence.SharedFrame.ofRetains extractionRetains)⟩

end Solcore.Frontend.RustHull.RootChildFrameCorrespondence
