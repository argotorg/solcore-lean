import Solcore.Frontend.RustHull.ContractCallInitializedExecution
import Solcore.Frontend.RustHull.ContractChildCallCorrespondence
import Solcore.Frontend.RustHull.ChildCatalogExecutionCorrespondence
import Solcore.Frontend.RustHull.ContractChildCallRuntimeFacts
/-! Actual parent initialization supplies the shared inventory, catalog links and
callback closure needed for independently derived child calls. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractChildCallCorrespondence
open Correspondence ScalarExecution CodeBuilder ContractRuntimeEffectsCorrespondence ContractEnvironmentCorrespondence
open ContractCallCorrespondence hiding supported supported_actual MessageRel contextInitialState
open ContractReturnDataCorrespondence (initializedReturnData fresh_returnData_observation shared_returnData_observation creator_returnData_observation initialized_returnDataSize)

abbrev contextInitialState := ContractCallCorrespondence.contextInitialState

private theorem known_observed {cells : List InitializedCell} {context : Contract.Context}
    {image : Option (List UInt8)} {withCode : Bool}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = RuntimeExtendedInitializedEffects.slots withCode)
    (observed : ∀ cell ∈ cells, ContractEnvironmentCorrespondence.initializedValue (contextEnvironment context image) cell) :
    ∀ cell ∈ cells, cell.name = "codeKnown" → cell.value = .bool image.isSome := by
  intro cell member named
  have present : (cell.name, cell.type) ∈ Effects.slots ++ Effects.codeSlots := by
    apply RuntimeExtendedInitializedEffects.slots_allowed withCode
    rw [← signature]
    exact List.mem_map_of_mem member
  have types : ∀ slot ∈ Effects.slots ++ Effects.codeSlots,
      slot.1 = "codeKnown" → slot.2 = Core.Ty.bool := by decide
  have typed : cell.type = .bool := types _ present named
  apply observed cell member
  simp only [EnvironmentBuiltinCorrespondence.observation, named, typed, contextEnvironment]

theorem objectFrame_evaluates {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (RuntimeExtendedInitializedEffects.slots true) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported true)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment captured : Core.Environment} {initial : Core.Store}
    {contextCode functions dispatcher creator : Code} {others : List Core.Expr}
    {images : List (Nat × List UInt8)} {image : Option (List UInt8)} {shared : AccountRuntime.References}
    {closure : Core.Value} (closureRelated : CapturedClosure compiled captured closure)
    (functionsRelated : CodeValue depth environment (part 0 (others.length + 1) functions) closure)
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    {sharedCells : List InitializedCell} (references : RuntimeReferences depth environment shared sharedCells)
    (initialized : InitializedCells sharedCells initial) (separate : CellLocations sharedCells)
    (description : sharedCells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip (ContractMemoryCorrespondence.contextSharedValues object context)).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse)
    {creatorLocation dispatcherLocation : Nat}
    (creatorRelated : CodeValue depth environment creator (.cellRef (Core.OptionalCell.cellType Creation.callbackType) creatorLocation))
    (creatorFound : ∃ value, initial.read? creatorLocation = some value)
    (creatorAfter : ∀ cell ∈ sharedCells, cell.location < creatorLocation)
    (dispatcherRelated : CodeValue depth environment dispatcher
      (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation))
    (dispatcherAfter : ∀ cell ∈ sharedCells, cell.location < dispatcherLocation)
    (dispatcherBefore : dispatcherLocation < creatorLocation)
    {catalog : List AccountRuntime.CodeDefinition} {catalogValues : List Core.Value}
    {sourceCatalog : ChildFrameSemantics.Catalog} {anchors : List CatalogWorldCorrespondence.Anchor}
    (capture : ObjectCallbackCapture (RuntimeExtendedInitializedEffects.slots true) (others.length + 1) images catalog
      (closure :: catalogValues) sharedCells dispatcherLocation creatorLocation initial)
    (catalogCompiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    (catalogCaptured : CapturedClosures captured others catalogValues)
    (connection : ChildCatalogExecutionCorrespondence.CatalogConnection sourceCatalog catalog anchors)
    (initialLinks : CatalogWorldCorrespondence.Links anchors (StorageCorrespondence.canonical (object.initialWorld context)))
    {finalSource : Semantics.State RuntimeCallEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCallEffectsSemantics.effectsWith (ChildFrameSemantics.CallFree sourceCatalog) image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectFrame (RuntimeExtendedInitializedEffects.slots true) (others.length + 1) images image contextCode functions shared dispatcher creator depth)
      value final ∧ MessageRel sourceResult finalSource.external context.address value := by
  let accounts := StorageCorrespondence.canonical (object.initialWorld context)
  let balances := Core.WordMapping.insertEntries context.address context.balance context.accounts
  have description' : sharedCells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip
        (ContractMemoryCorrespondence.sharedValues accounts context.completeWorld balances (ambientValues context.ambient))).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse := description
  have fresh : FrameInitializersValid depth environment initial
      (ContractMemoryCorrespondence.requestCode contextCode) dispatcher (part 5 12 contextCode)
      (constant (Core.WordMapping.literal (Memory.packBytes (image.getD []))))
      (number (image.getD []).length) (CodeBuilder.boolean image.isSome) shared
      (ContractEnvironmentCorrespondence.initializedValue (contextEnvironment context image)) :=
    ContractEnvironmentCorrespondence.fresh_initializers_observation_image context image (ContractMemoryCorrespondence.request_related object context contextRelated)
      (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes (image.getD [])) depth environment)
      (CodeValue.number (image.getD []).length depth environment) (CodeValue.boolean image.isSome depth environment) references description'
  have freshCode := ContractCodeCorrespondence.fresh_code_observation (store := initial) (dispatcher := dispatcher) (shared := shared) image
    (ContractMemoryCorrespondence.request_related object context contextRelated) rfl
    (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes (image.getD [])) depth environment)
    (CodeValue.number (image.getD []).length depth environment) (CodeValue.boolean image.isSome depth environment)
  have freshData := fresh_returnData_observation (store := initial) (dispatcher := dispatcher) (shared := shared)
    (ContractMemoryCorrespondence.request_related object context contextRelated) rfl
    (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes (image.getD [])) depth environment)
    (CodeValue.number (image.getD []).length depth environment) (CodeValue.boolean image.isSome depth environment)
  have dispatcherBelow : dispatcherLocation < initial.length :=
    (List.getElem?_eq_some_iff.mp capture.stored).1
  have freshHandler := fresh_handler_observation (store := initial) (shared := shared)
    (ContractMemoryCorrespondence.request_related object context contextRelated) rfl rfl dispatcherRelated
    (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes (image.getD [])) depth environment)
    (CodeValue.number (image.getD []).length depth environment) (CodeValue.boolean image.isSome depth environment)
  have freshDepth := fresh_depth_observation (store := initial) (dispatcher := dispatcher) (shared := shared)
    (ContractMemoryCorrespondence.request_related object context contextRelated) rfl rfl
    (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes (image.getD [])) depth environment)
    (CodeValue.number (image.getD []).length depth environment) (CodeValue.boolean image.isSome depth environment)
  have freshSeparate := fresh_dispatcher_separate (dispatcher := dispatcher) (shared := shared) dispatcherBelow
    (ContractMemoryCorrespondence.request_related object context contextRelated) rfl
    (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes (image.getD [])) depth environment)
    (CodeValue.number (image.getD []).length depth environment) (CodeValue.boolean image.isSome depth environment)
  have sharedPresent : ∀ name ∈ dispatchSharedNames, name ∈ sharedCells.map InitializedCell.name := by
    rw [capture.names]
    intro name member
    simp only [dispatchSharedNames, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [sharedSlotTypes]
  have freshOrigin := fresh_shared_origin (store := initial) (dispatcher := dispatcher) references sharedPresent
    (ContractMemoryCorrespondence.request_related object context contextRelated) rfl
    (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes (image.getD [])) depth environment)
    (CodeValue.number (image.getD []).length depth environment) (CodeValue.boolean image.isSome depth environment)
  have sharedSignature := ContractChildCallCorrespondence.shared_signature description (by
    simp [AccountRuntime.sharedInitializers, ContractMemoryCorrespondence.contextSharedValues,
      ambientValues, Ambient.slots])
  have childOrigin := ChildCallbackContextCorrespondence.fresh_origin (store := initial) (dispatcher := dispatcher) references sharedSignature
    (ContractMemoryCorrespondence.request_related object context contextRelated) rfl
    (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes (image.getD [])) depth environment)
    (CodeValue.number (image.getD []).length depth environment) (CodeValue.boolean image.isSome depth environment)
  apply ContractRuntimeEffectsCorrespondence.objectFrame_initializes_extended (fun _ member => RuntimeExtendedInitializedEffects.slots_allowed true member) object context contextRelated references initialized separate
    description creatorRelated creatorFound creatorAfter
    (fun cell => ContractEnvironmentCorrespondence.initializedValue (contextEnvironment context image) cell ∧ ContractCodeCorrespondence.initializedCode image cell ∧ initializedReturnData cell ∧
      initializedHandler context.address dispatcherLocation cell ∧ initializedDepth Core.Word.zero cell ∧
      cell.location ≠ dispatcherLocation ∧ sharedOrigin sharedCells cell ∧
      ChildCallbackContextCorrespondence.Origin sharedCells initial.length cell)
    (fun value _ => MessageRel sourceResult finalSource.external context.address value)
    (FrameInitializersValid.and fresh (FrameInitializersValid.and freshCode (FrameInitializersValid.and freshData
      (FrameInitializersValid.and freshHandler (FrameInitializersValid.and freshDepth (FrameInitializersValid.and freshSeparate (FrameInitializersValid.and freshOrigin childOrigin)))))))
    (fun cell member => ⟨ContractEnvironmentCorrespondence.shared_initialized_value context image description' cell member,
      ContractCodeCorrespondence.shared_code_observation image description' cell member,
      shared_returnData_observation description' cell member,
      shared_handler_observation context.address dispatcherLocation description' cell member,
      shared_depth_observation Core.Word.zero description' cell member,
      Nat.ne_of_lt (dispatcherAfter cell member), (fun _ => member),
      (fun _ => member), (fun _ => Or.inl member)⟩)
    (by
      intro value _
      constructor
      · intro _ impossible
        cases impossible
      · exact ⟨ContractCodeCorrespondence.creator_code_observation image creatorLocation value,
          creator_returnData_observation creatorLocation value,
          creator_handler_observation context.address dispatcherLocation creatorLocation value,
          creator_depth_observation Core.Word.zero creatorLocation value,
          Nat.ne_of_gt dispatcherBefore, creator_shared_origin sharedCells creatorLocation value,
          ChildCallbackContextCorrespondence.creator_origin sharedCells initial.length creatorLocation value⟩)
  intro extra suffix frameReferences cells worldLocation balancesLocation referenceValues stored signature observations cellLocations
    worldReference balancesReference balancesFound
  have observed := fun cell member => (observations cell member).1
  have environmentObserved := fun cell member => (observations cell member).2.1
  have codeObserved := fun cell member => (observations cell member).2.2.1
  have dataObserved := fun cell member => (observations cell member).2.2.2.1
  have handlerObserved := fun cell member => (observations cell member).2.2.2.2.1
  have depthObserved := fun cell member => (observations cell member).2.2.2.2.2.1
  have dispatchSeparate := fun cell member => (observations cell member).2.2.2.2.2.2.1
  have sharedOrigins := fun cell member => (observations cell member).2.2.2.2.2.2.2.1
  have childOrigins := fun cell member => (observations cell member).2.2.2.2.2.2.2.2
  have knownObserved := known_observed signature environmentObserved
  obtain ⟨ready, logReady, accountReady⟩ := RuntimeExtendedInitializedEffects.ready signature stored cellLocations
    (fun cell member => (observed cell member).1.1) rfl
    (words := []) (cursor := Core.Word.zero) (balances := balances)
    (fun cell member named => (observed cell member).1.2 "logs" (by decide) named)
    (fun cell member named => (observed cell member).1.2 "logSize" (by decide) named)
    (fun cell member named => (observed cell member).1.2 "balances" (by decide) named)
  obtain ⟨accountReady⟩ := accountReady
  obtain ⟨codeReady⟩ := RuntimeReturnDataInitializedEffects.ready signature stored cellLocations accountReady
    (image := image) dataObserved
    (fun cell member named typed => initialized_returnDataSize (environmentObserved cell member) named typed)
    (fun _ => codeObserved) (fun _ => knownObserved)
  have memoryLocation : codeReady.layout.memory = ready.memory := by
    change codeReady.layout.toAccountLayout.memory = ready.memory
    rw [codeReady.base]
    exact
    (congrArg (fun layout : RuntimeLogEffectsCorrespondence.Layout => layout.memory) accountReady.base).trans
      (congrArg RuntimeEffectsCorrespondence.Layout.memory logReady.base)
  have storageLocations : codeReady.layout.storage = ready.locations := by
    change codeReady.layout.toAccountLayout.storage = ready.locations
    rw [codeReady.base]
    exact
    (congrArg (fun layout : RuntimeLogEffectsCorrespondence.Layout => layout.storage) accountReady.base).trans
      (congrArg RuntimeEffectsCorrespondence.Layout.storage logReady.base)
  have boundary : codeReady.layout.boundary = (initial ++ suffix).length := by
    change codeReady.layout.toAccountLayout.boundary = (initial ++ suffix).length
    rw [codeReady.base]
    exact
    (congrArg (fun layout : RuntimeLogEffectsCorrespondence.Layout => layout.boundary) accountReady.base).trans
      (congrArg RuntimeEffectsCorrespondence.Layout.boundary logReady.base)
  let slots := cells.map InitializedCell.effectSlot
  have slotTypes : RuntimeEffectsFrameCorrespondence.slotTypes slots = RuntimeExtendedInitializedEffects.slots true := by
    simpa only [RuntimeEffectsFrameCorrespondence.slotTypes, MemoryFrameCorrespondence.slotTypes,
      slots, List.map_map, Function.comp_def, InitializedCell.effectSlot] using signature
  have environmentRelated := initialized_environment cells (RuntimeExtendedInitializedEffects.initialized_unique (withCode := true) signature)
    (Core.Value.unit :: bundleValues (cells.map InitializedCell.reference) :: captured)
  have runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (RuntimeEffectsFrameCorrespondence.slotTypes slots)) Core.Renaming.id
      ((cells.map InitializedCell.reference).reverse ++ Core.Value.unit :: bundleValues (cells.map InitializedCell.reference) :: captured) := by
    simpa only [slots, RuntimeEffectsFrameCorrespondence.slotTypes, MemoryFrameCorrespondence.slotTypes,
      List.map_map, Function.comp_def, InitializedCell.effectSlot] using environmentRelated
  have worldSame : ready.locations.world = worldLocation := by
    obtain ⟨cell, member, same⟩ := List.mem_map.mp ready.worldMember
    have named := congrArg EffectSlot.name same
    have atLocation := congrArg EffectSlot.location same
    exact atLocation.symm.trans ((observed cell member).2.1 named)
  have balanceSame : codeReady.layout.balances = balancesLocation := by
    change codeReady.layout.toAccountLayout.balances = balancesLocation
    rw [codeReady.base]
    obtain ⟨cell, member, same⟩ := List.mem_map.mp accountReady.balancesMember
    have named := congrArg EffectSlot.name same
    have atLocation := congrArg EffectSlot.location same
    exact atLocation.symm.trans ((observed cell member).2.2 named)
  have environmentInitial := initialized_related stored environmentObserved
  have returnRelated : StateRel (RuntimeReturnDataEffectsCorrespondence.model codeReady.layout
      (prefixRead codeReady.layout.boundary (initial ++ suffix)) slots image) []
      ⟨[], ContractReturnDataCorrespondence.contextInitialState image object context⟩ (initial ++ suffix) := by
    apply RuntimeReturnDataEffectsCorrespondence.initial_state
    · rw [codeReady.base]
      apply RuntimeAccountEffectsCorrespondence.initial_state
      · rw [accountReady.base]
        apply RuntimeLogEffectsCorrespondence.initial_state
        · simpa only [logReady.base, RuntimeEffectsCorrespondence.initialLayout] using
            RuntimeEnvironmentEffectsCorrespondence.initial_state ready.memoryRelated ready.storageRelated ready.distinct environmentInitial
        · exact logReady.logsRead
        · exact logReady.logSizeRead
      · exact accountReady.balancesRead
    · exact codeReady.readData
    · exact codeReady.readSize
    · exact codeReady.readCode
  have passiveEnvironment : RuntimeLogEffectsCorrespondence.Passive codeReady.layout.toLogLayout slots := by
    apply RuntimeLogEffectsCorrespondence.Passive.of_names
      (memoryMember := by simpa only [memoryLocation] using ready.memoryMember)
      (worldMember := by simpa only [storageLocations] using ready.worldMember)
      (memorySizeMember := by simpa only [storageLocations] using ready.sizeMember)
      (exitMember := by simpa only [storageLocations] using ready.exitMember)
      (offsetMember := by simpa only [storageLocations] using ready.offsetMember)
      (sizeMember := by simpa only [storageLocations] using ready.returnSizeMember)
      (logsMember := by simpa only [codeReady.base, accountReady.base] using logReady.logsMember) (logSizeMember := by simpa only [codeReady.base, accountReady.base] using logReady.logSizeMember)
    intro first firstMember second secondMember same
    obtain ⟨left, leftMember, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨right, rightMember, rfl⟩ := List.mem_map.mp secondMember
    exact cellLocations left leftMember right rightMember same
  have baseMembers := RuntimeCallInitializedEffects.base_members codeReady
  obtain ⟨callReady⟩ := RuntimeCallInitializedEffects.ready signature stored cellLocations boundary baseMembers
    (by rw [boundary]; exact Nat.lt_of_lt_of_le dispatcherBelow (by simp))
    dispatchSeparate depthObserved handlerObserved
  obtain ⟨creatorValue, creatorRead⟩ := creatorFound
  have creatorBelow : creatorLocation < initial.length := (List.getElem?_eq_some_iff.mp creatorRead).1
  obtain ⟨inventory, sharedMembers⟩ := initialized_inventory (layout := callReady.layout) sharedSignature signature stored cellLocations
    (by simpa only [callReady.baseEqual] using boundary)
    (by simpa only [callReady.baseEqual] using baseMembers) childOrigins creatorAfter creatorBelow (by simp)
  let dispatchCapture := captured_dispatcher capture _ (inventory_references inventory capture.references)
  let handlers : RuntimeCallEffectsCorrespondence.Handlers callReady.layout := {
    source := context.address
    dispatchValue := capture.closure
    handlerValue := callReady.handlerValue
    dispatch := dispatchCapture
    handler := by simpa only [callReady.dispatcherEqual] using callReady.handler }
  have initialRelated : StateRel (RuntimeCallEffectsCorrespondence.model callReady.layout
      (prefixRead callReady.layout.boundary (initial ++ suffix)) slots image handlers) []
      ⟨[], contextInitialState image object context⟩ (initial ++ suffix) := by
    apply RuntimeCallEffectsCorrespondence.initial_state
    · simpa only [callReady.baseEqual, contextInitialState, ContractCallCorrespondence.contextInitialState] using returnRelated
    · exact callReady.depthRead
    · simpa only [callReady.dispatcherEqual, Core.Store.read?, List.getElem?_append_left dispatcherBelow] using capture.stored
    · exact callReady.handlerRead
    · rfl
  have callCodes : ∀ imageCells, callReady.layout.toReturnDataLayout.codeCells = some imageCells →
      ⟨"code", Core.WordMapping.type, imageCells.code⟩ ∈ cells.map InitializedCell.effectSlot ∧
      ⟨"codeKnown", .bool, imageCells.known⟩ ∈ cells.map InitializedCell.effectSlot := by
    rw [callReady.baseEqual]
    exact codeReady.codeMembers
  have callMode : callReady.layout.toReturnDataLayout.codeCells.isSome = true := by
    rw [callReady.baseEqual]
    exact codeReady.mode
  have callPassive := RuntimeCallInitializedEffects.call_passive (layout := callReady.layout)
    (RuntimeExtendedInitializedEffects.initialized_unique signature) cellLocations
    (by simpa only [callReady.baseEqual] using baseMembers)
    callCodes
  let callbackContext := ChildCallbackContextCorrespondence.context inventory
  have creatorFinal : (initial ++ suffix).read? creatorLocation = some creatorValue := by
    simpa only [Core.Store.read?, List.getElem?_append_left creatorBelow] using creatorRead
  have capturedValid := ChildCallbackContextCorrespondence.initial inventory
    (fun cell member => stored cell (ChildCallbackContextCorrespondence.shared_included sharedSignature signature childOrigins cell member))
    ⟨creatorValue, creatorFinal⟩
  have linkedInitial : RuntimeLinkedWorldCorrespondence.StateRel anchors
      (RuntimeChildCallEffectsCorrespondence.sourceWorld (contextInitialState image object context))
      callReady.layout.storage.world (initial ++ suffix) := by
    refine ⟨accounts, rfl, initialLinks, ?_⟩
    rw [callReady.baseEqual, storageLocations]
    obtain ⟨cell, member, same⟩ := List.mem_map.mp ready.worldMember
    have named : cell.name = "world" := congrArg EffectSlot.name same
    have location : cell.location = ready.locations.world := congrArg EffectSlot.location same
    have valued := (observed cell member).1.1 (StorageCorrespondence.world accounts)
      (by simp only [RuntimeInitializedEffects.expected, named]; rfl)
    simpa only [← location, valued] using stored cell member
  have childInitial := RuntimeChildCallEffectsCorrespondence.of_base initialRelated linkedInitial capturedValid
  have callbacks : ∀ {world state current},
      StateRel (RuntimeChildCallEffectsCorrespondence.model callReady.layout
        (prefixRead callReady.layout.boundary (initial ++ suffix)) slots image handlers anchors callbackContext) world state current →
      RuntimeChildCallEffectsCorrespondence.CallbackPreservation callReady.layout handlers anchors callbackContext
        (ChildFrameSemantics.CallFree sourceCatalog) state.external := by
    intro world state current related
    have base := RuntimeChildCallEffectsCorrespondence.base_related related
    have ambient := ChildCallbackContextCorrespondence.parent_observed inventory sharedMembers base related.external.2.2.1.2
    apply RuntimeChildCallEffectsCorrespondence.callback_preserves
    · exact RuntimeCallEffectsCorrespondence.source_eq base
    · exact ChildCatalogExecutionCorrespondence.captured_child_runs_preserves connection catalogCompiled catalogCaptured capture
        inventory (inventory_references inventory capture.references) state.external ambient
  obtain ⟨value, final, completed, resultRelated⟩ := frameCall_message_evaluates (withCode := true)
    (by simpa only [slotTypes] using accepted)
    (by simpa only [supported_actual slotTypes] using eligible) closureRelated
    ((functionsRelated.prepend extra).evaluates (initial ++ suffix))
    ((CodeValue.packet referenceValues).evaluates (initial ++ suffix))
    (by simp [slots]) runtime (RuntimeExtendedInitializedEffects.initialized_separate (withCode := true) signature)
    (by simpa only [callReady.baseEqual, memoryLocation] using ready.memoryMember)
    (by simpa only [callReady.baseEqual, storageLocations] using ready.worldMember)
    (by simpa only [callReady.baseEqual, storageLocations] using ready.addressMember)
    (by simpa only [callReady.baseEqual, storageLocations] using ready.completeMember)
    (by simpa only [callReady.baseEqual, storageLocations] using ready.staticMember)
    (by simpa only [callReady.baseEqual, storageLocations] using ready.sizeMember)
    (by simpa only [callReady.baseEqual, storageLocations] using ready.exitMember)
    (by simpa only [callReady.baseEqual, storageLocations] using ready.offsetMember)
    (by simpa only [callReady.baseEqual, storageLocations] using ready.returnSizeMember)
    (by simpa only [callReady.baseEqual, codeReady.base, accountReady.base] using logReady.logsMember)
    (by simpa only [callReady.baseEqual, codeReady.base, accountReady.base] using logReady.logSizeMember)
    (by simpa only [callReady.baseEqual, codeReady.base] using accountReady.balancesMember)
    callCodes
    (by simpa only [callReady.baseEqual] using codeReady.dataMember)
    (by simpa only [callReady.baseEqual] using codeReady.dataSizeMember)
    callMode
    callReady.depthMember callReady.handlerMember childInitial
    (by simpa only [callReady.baseEqual] using passiveEnvironment) callPassive callbacks evaluated context.address
    (by simpa only [callReady.baseEqual, storageLocations, worldSame] using worldReference.prepend extra) (by simpa only [callReady.baseEqual, balanceSame] using balancesReference.prepend extra)
    ((contextRelated.part (index := 4) rfl).prepend extra)
    (by simpa only [notDeploying] using (contextRelated.part (index := 11) rfl).prepend extra)
  exact ⟨value, final, completed, resultRelated⟩

end Solcore.Frontend.RustHull.ContractChildCallCorrespondence
