import Solcore.Frontend.RustHull.ContractCallInitializedExecution
import Solcore.Frontend.RustHull.ContractCallModeCorrespondence
import Solcore.Frontend.RustHull.ChildFrameCallModeAllocationCorrespondence
import Solcore.Frontend.RustHull.ModeChildCatalogRunCorrespondence
import Solcore.Frontend.RustHull.RuntimeCallModeCallbackCorrespondence
import Solcore.Frontend.RustHull.ContractChildCallRuntimeFacts
/-! Actual parent initialization supplies the shared inventory, catalog links and
callback closure needed for independently derived child calls. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractCallModeCorrespondence
open Correspondence ScalarExecution CodeBuilder ContractRuntimeEffectsCorrespondence ContractEnvironmentCorrespondence
open ContractCallCorrespondence hiding supported supported_actual MessageRel contextInitialState
open ContractChildCallCorrespondence (initialized_inventory inventory_references)
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
    {sourceCatalog : ChildFrameSemantics.Catalog} {anchors : List CatalogWorldCorrespondence.Anchor} {height : Nat}
    (capture : ObjectCallbackCapture (RuntimeExtendedInitializedEffects.slots true) (others.length + 1) images catalog
      (closure :: catalogValues) sharedCells dispatcherLocation creatorLocation initial)
    {createValue : Core.Value} (createRead : initial.read? creatorLocation = some (.inRight .unit createValue))
    (createCaptured : CapturedClosure ((AccountRuntime.objectHandlers (RuntimeExtendedInitializedEffects.slots true)
      (others.length + 1) images catalog capture.functions capture.shared capture.dispatcher capture.creator).2
      (capture.depth + 1)) (.unit :: capture.environment) createValue)
    (catalogCompiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    (catalogCaptured : CapturedClosures captured others catalogValues)
    (connection : ModeChildCatalogExecutionCorrespondence.CatalogConnection sourceCatalog catalog anchors)
    (frameExecution : ModeChildCatalogExecutionCorrespondence.FrameExecution sourceCatalog catalog anchors
      (ChildFrameModeSemantics.effectsAt sourceCatalog height))
    (initialLinks : CatalogWorldCorrespondence.Links anchors (StorageCorrespondence.canonical (object.initialWorld context)))
    {finalSource : Semantics.State RuntimeCallEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (ChildFrameModeSemantics.effectsAt sourceCatalog (height + 1) image)
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
  have freshCallCode := ChildFrameModeCorrespondence.fresh_handler_observation .callCode (store := initial) (shared := shared)
    (ContractMemoryCorrespondence.request_related object context contextRelated) rfl rfl dispatcherRelated
    (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes (image.getD [])) depth environment)
    (CodeValue.number (image.getD []).length depth environment) (CodeValue.boolean image.isSome depth environment)
  have freshDelegate := ChildFrameModeCorrespondence.fresh_handler_observation .delegateCall (store := initial) (shared := shared)
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
  apply ContractRuntimeEffectsCorrespondence.objectFrame_initializes_creator (fun _ member => RuntimeExtendedInitializedEffects.slots_allowed true member) object context contextRelated references initialized separate
    description creatorRelated creatorFound creatorAfter
    (fun cell => (ContractEnvironmentCorrespondence.initializedValue (contextEnvironment context image) cell ∧ ContractCodeCorrespondence.initializedCode image cell ∧ initializedReturnData cell ∧
      initializedHandler context.address dispatcherLocation cell ∧ initializedDepth Core.Word.zero cell ∧
      cell.location ≠ dispatcherLocation ∧ sharedOrigin sharedCells cell ∧
      ChildCallbackContextCorrespondence.Origin sharedCells initial.length cell) ∧
      ChildFrameModeCorrespondence.initializedHandler .callCode context.address dispatcherLocation cell ∧
      ChildFrameModeCorrespondence.initializedHandler .delegateCall context.address dispatcherLocation cell)
    (fun value _ => MessageRel sourceResult finalSource.external context.address value)
    (FrameInitializersValid.and
      (FrameInitializersValid.and fresh (FrameInitializersValid.and freshCode (FrameInitializersValid.and freshData
        (FrameInitializersValid.and freshHandler (FrameInitializersValid.and freshDepth (FrameInitializersValid.and freshSeparate (FrameInitializersValid.and freshOrigin childOrigin)))))))
      (FrameInitializersValid.and freshCallCode freshDelegate))
    (fun cell member => ⟨⟨ContractEnvironmentCorrespondence.shared_initialized_value context image description' cell member,
      ContractCodeCorrespondence.shared_code_observation image description' cell member,
      shared_returnData_observation description' cell member,
      shared_handler_observation context.address dispatcherLocation description' cell member,
      shared_depth_observation Core.Word.zero description' cell member,
      Nat.ne_of_lt (dispatcherAfter cell member), (fun _ => member),
      (fun _ => member), (fun _ => Or.inl member)⟩,
      ChildFrameModeCorrespondence.shared_handler_observation .callCode sharedSignature _ _ cell member,
      ChildFrameModeCorrespondence.shared_handler_observation .delegateCall sharedSignature _ _ cell member⟩)
    (by
      intro value _
      constructor
      · constructor
        · intro _ impossible
          cases impossible
        · exact ⟨ContractCodeCorrespondence.creator_code_observation image creatorLocation value,
          creator_returnData_observation creatorLocation value,
          creator_handler_observation context.address dispatcherLocation creatorLocation value,
          creator_depth_observation Core.Word.zero creatorLocation value,
          Nat.ne_of_gt dispatcherBefore, creator_shared_origin sharedCells creatorLocation value,
          ChildCallbackContextCorrespondence.creator_origin sharedCells initial.length creatorLocation value⟩
      · exact ⟨ChildFrameModeCorrespondence.creator_handler_observation .callCode _ _ _ _,
          ChildFrameModeCorrespondence.creator_handler_observation .delegateCall _ _ _ _⟩)
  intro extra suffix frameReferences cells worldLocation balancesLocation referenceValues stored signature observations cellLocations
    creatorCells worldReference balancesReference balancesFound
  have previous := fun cell member => And.intro (observations cell member).1 (observations cell member).2.1
  have callCodeObserved := fun cell member => (observations cell member).2.2.1
  have delegateObserved := fun cell member => (observations cell member).2.2.2
  have observed := fun cell member => (previous cell member).1
  have environmentObserved := fun cell member => (previous cell member).2.1
  have codeObserved := fun cell member => (previous cell member).2.2.1
  have dataObserved := fun cell member => (previous cell member).2.2.2.1
  have handlerObserved := fun cell member => (previous cell member).2.2.2.2.1
  have depthObserved := fun cell member => (previous cell member).2.2.2.2.2.1
  have dispatchSeparate := fun cell member => (previous cell member).2.2.2.2.2.2.1
  have sharedOrigins := fun cell member => (previous cell member).2.2.2.2.2.2.2.1
  have childOrigins := fun cell member => (previous cell member).2.2.2.2.2.2.2.2
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
  let ordinaryHandlers : RuntimeCallEffectsCorrespondence.Handlers callReady.layout := {
    source := context.address
    dispatchValue := capture.closure
    handlerValue := callReady.handlerValue
    dispatch := dispatchCapture
    handler := by simpa only [callReady.dispatcherEqual] using callReady.handler }
  obtain ⟨callCodeReady⟩ := ChildFrameModeCorrespondence.extra_ready .callCode (layout := callReady.layout)
    (source := context.address) signature stored cellLocations
    (by simpa only [callReady.baseEqual] using boundary)
    (by simpa only [callReady.baseEqual] using baseMembers)
    (fun cell member => by simpa only [callReady.dispatcherEqual] using callCodeObserved cell member)
  obtain ⟨delegateReady⟩ := ChildFrameModeCorrespondence.extra_ready .delegateCall (layout := callReady.layout)
    (source := context.address) signature stored cellLocations
    (by simpa only [callReady.baseEqual] using boundary)
    (by simpa only [callReady.baseEqual] using baseMembers)
    (fun cell member => by simpa only [callReady.dispatcherEqual] using delegateObserved cell member)
  obtain ⟨runInit, identify, createShape⟩ := CreationImplementation.objectHandlers_create
    (RuntimeExtendedInitializedEffects.slots true) (others.length + 1) images catalog capture.functions capture.shared
    capture.dispatcher capture.creator
  let createHandler : RuntimeCallModeEffectsCorrespondence.CreateHandler callReady.layout := {
    location := creatorLocation
    below := inventory.creatorBelow
    outside := inventory.creatorOutside
    value := createValue
    closure := {
      depth := capture.depth + 1
      captured := .unit :: capture.environment
      shared := capture.shared
      runInit := runInit
      identify := identify
      closure := by rw [← createShape]; exact createCaptured
      references := (inventory_references inventory capture.references).prepend [.unit] } }
  let handlers : RuntimeCallModeEffectsCorrespondence.ModeHandlers callReady.layout := {
    ordinary := ordinaryHandlers, callCode := callCodeReady.handler, delegateCall := delegateReady.handler,
    create := createHandler }
  have initialRelated : StateRel (RuntimeCallEffectsCorrespondence.model callReady.layout
      (prefixRead callReady.layout.boundary (initial ++ suffix)) slots image ordinaryHandlers) []
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
  let nestedInventory : NestedChildCallbackContextCorrespondence.Inventory callReady.layout sharedCells creatorLocation := {
    base := inventory
    dispatcherSeparate := by
      intro cell member
      rw [callReady.dispatcherEqual]
      exact Nat.ne_of_lt (dispatcherAfter cell member)
    creatorDispatcher := by
      rw [callReady.dispatcherEqual]
      exact Nat.ne_of_gt dispatcherBefore }
  let callbackContext := NestedChildCallbackContextCorrespondence.context nestedInventory capture.closure
  have creatorFinal : (initial ++ suffix).read? creatorLocation = some creatorValue := by
    simpa only [Core.Store.read?, List.getElem?_append_left creatorBelow] using creatorRead
  have capturedBase := ChildCallbackContextCorrespondence.initial inventory
    (fun cell member => stored cell (ChildCallbackContextCorrespondence.shared_included sharedSignature signature childOrigins cell member))
    ⟨creatorValue, creatorFinal⟩
  have capturedValid : callbackContext.valid (prefixRead callReady.layout.boundary (initial ++ suffix)) :=
    NestedChildCallbackContextCorrespondence.initial nestedInventory capturedBase
      (by simpa only [callReady.dispatcherEqual, Core.Store.read?, List.getElem?_append_left dispatcherBelow] using capture.stored)
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
  have modeCaptured : (handlers.context callbackContext).valid (prefixRead callReady.layout.boundary (initial ++ suffix)) := by
    refine ⟨capturedValid, ?_, ?_, ?_⟩
    · simpa only [handlers, prefixRead, callCodeReady.handler.below, ↓reduceIte] using callCodeReady.read
    · simpa only [handlers, prefixRead, delegateReady.handler.below, ↓reduceIte] using delegateReady.read
    · have createFinal : (initial ++ suffix).read? creatorLocation = some (.inRight .unit createValue) := by
        simpa only [Core.Store.read?, List.getElem?_append_left creatorBelow] using createRead
      simpa only [handlers, createHandler, prefixRead, inventory.creatorBelow, ↓reduceIte] using createFinal
  have childInitial := RuntimeChildCallEffectsCorrespondence.of_base initialRelated linkedInitial modeCaptured
  have callbacks : ∀ {world state current},
      StateRel (RuntimeCallModeEffectsCorrespondence.model callReady.layout
        (prefixRead callReady.layout.boundary (initial ++ suffix)) slots image handlers anchors callbackContext) world state current →
      ∀ operation, RuntimeCallModeEffectsCorrespondence.CallbackPreservation callReady.layout handlers anchors callbackContext
        (ChildFrameModeSemantics.Children sourceCatalog (ChildFrameModeSemantics.effectsAt sourceCatalog height)) operation state.external := by
    intro world state current related operation
    have base := RuntimeCallModeEffectsCorrespondence.base_related related
    have ambient := ChildCallbackContextCorrespondence.parent_observed inventory sharedMembers base related.external.2.2.1.2.1.1
    apply RuntimeCallModeEffectsCorrespondence.callback_preserves
    · exact RuntimeCallEffectsCorrespondence.source_eq base
    · apply AccountCallModeCorrespondence.ChildRunPreservation.strengthen
        (ModeChildCatalogExecutionCorrespondence.captured_child_runs_preserves connection frameExecution catalogCompiled catalogCaptured
        (NestedChildCallbackContextCorrespondence.withDispatcher capture callReady.layout.dispatcher callReady.dispatcherEqual)
        nestedInventory (inventory_references inventory capture.references) createHandler rfl operation.mode state.external ambient)
      intro current ready
      exact ⟨ready.1, ready.2.1, ready.2.2.2.2⟩
  have namedSlot : ∀ name, (name, Core.Ty.word) ∈ RuntimeExtendedInitializedEffects.slots true →
      ∃ location, (⟨name, .word, location⟩ : EffectSlot) ∈ slots := by
    intro name member
    rw [← signature] at member
    obtain ⟨cell, present, same⟩ := List.mem_map.mp member
    obtain ⟨named, typed⟩ := Prod.mk.inj same
    exact ⟨cell.location, List.mem_map.mpr ⟨cell, present, by simp only [InitializedCell.effectSlot, named, typed]⟩⟩
  have callerMember := namedSlot "caller" (by simp [RuntimeExtendedInitializedEffects.slots, Effects.slots])
  have valueMember := namedSlot "callvalue" (by simp [RuntimeExtendedInitializedEffects.slots, Effects.slots])
  have gasMember : ∃ location, (⟨"availableGas", .sum .unit .word, location⟩ : EffectSlot) ∈ slots := by
    have member : ("availableGas", Core.Ty.sum .unit .word) ∈ RuntimeExtendedInitializedEffects.slots true := by
      simp [RuntimeExtendedInitializedEffects.slots, Effects.slots]
    rw [← signature] at member
    obtain ⟨cell, present, same⟩ := List.mem_map.mp member
    obtain ⟨named, typed⟩ := Prod.mk.inj same
    exact ⟨cell.location, List.mem_map.mpr ⟨cell, present, by simp only [InitializedCell.effectSlot, named, typed]⟩⟩
  have createMember : (⟨"createHandler", Core.OptionalCell.cellType Creation.callbackType, creatorLocation⟩ : EffectSlot) ∈ slots := by
    have member : ("createHandler", Core.OptionalCell.cellType Creation.callbackType) ∈ RuntimeExtendedInitializedEffects.slots true := by
      simp [RuntimeExtendedInitializedEffects.slots, Effects.slots]
    rw [← signature] at member
    obtain ⟨cell, present, same⟩ := List.mem_map.mp member
    obtain ⟨named, typed⟩ := Prod.mk.inj same
    have located : cell.location = creatorLocation := by
      rcases creatorCells cell present named with shared | located
      · have names := List.mem_map_of_mem (f := InitializedCell.name) shared
        rw [capture.names, named] at names
        simp [sharedSlotTypes, Ambient.slots] at names
      · exact located
    exact List.mem_map.mpr ⟨cell, present, by simp only [InitializedCell.effectSlot, named, typed, located]⟩
  obtain ⟨value, final, completed, resultRelated⟩ := frameCall_message_evaluates (withCode := true) (handlers := handlers)
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
    callReady.depthMember callReady.handlerMember callCodeReady.member delegateReady.member callerMember valueMember
    ⟨createMember, gasMember⟩ childInitial
    (by simpa only [callReady.baseEqual] using passiveEnvironment) callPassive callbacks evaluated context.address
    (by simpa only [callReady.baseEqual, storageLocations, worldSame] using worldReference.prepend extra) (by simpa only [callReady.baseEqual, balanceSame] using balancesReference.prepend extra)
    ((contextRelated.part (index := 4) rfl).prepend extra)
    (by simpa only [notDeploying] using (contextRelated.part (index := 11) rfl).prepend extra)
  exact ⟨value, final, completed, resultRelated⟩

end Solcore.Frontend.RustHull.ContractCallModeCorrespondence
