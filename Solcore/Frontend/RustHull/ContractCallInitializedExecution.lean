import Solcore.Frontend.RustHull.ContractCodeInitializedExecution
import Solcore.Frontend.RustHull.ContractCallCorrespondence
import Solcore.Frontend.RustHull.ContractReturnDataInitializedExecution
import Solcore.Frontend.RustHull.RuntimeCallInitializedResources
import Solcore.Frontend.RustHull.ContractExtendedRuntimeInitializationCorrespondence
import Solcore.Frontend.RustHull.ContractExtendedEnvironmentRuntimeFacts
import Solcore.Frontend.RustHull.RuntimeReturnDataInitializedEffects
import Solcore.Frontend.RustHull.ContractCodeRuntimeFacts
import Solcore.Frontend.RustHull.ContractReturnDataRuntimeFacts

/-! Actual frame initialization supplies empty caller return data and optional
code cells before independent source execution reaches message completion. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractCallCorrespondence
open Correspondence ScalarExecution CodeBuilder ContractRuntimeEffectsCorrespondence ContractEnvironmentCorrespondence
open ContractReturnDataCorrespondence (initializedReturnData fresh_returnData_observation shared_returnData_observation creator_returnData_observation initialized_returnDataSize)

def contextInitialState (image : Option (List UInt8)) (object : Contract.CompiledObject)
    (context : Contract.Context) : RuntimeCallEffectsSemantics.State :=
  ⟨ContractReturnDataCorrespondence.contextInitialState image object context, Core.Word.zero⟩

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

theorem objectFrame_evaluates {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (RuntimeExtendedInitializedEffects.slots withCode) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment captured : Core.Environment} {initial : Core.Store}
    {contextCode functions dispatcher creator : Code} {count : Nat}
    {images : List (Nat × List UInt8)} {image : Option (List UInt8)} {shared : AccountRuntime.References}
    {closure : Core.Value} (closureRelated : CapturedClosure compiled captured closure)
    (functionsRelated : CodeValue depth environment (part 0 count functions) closure)
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
    {catalog : List AccountRuntime.CodeDefinition} {allFunctions : List Core.Value}
    (capture : ObjectCallbackCapture (RuntimeExtendedInitializedEffects.slots withCode) count images catalog
      allFunctions sharedCells dispatcherLocation creatorLocation initial)
    {finalSource : Semantics.State RuntimeCallEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCallEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectFrame (RuntimeExtendedInitializedEffects.slots withCode) count images image contextCode functions shared dispatcher creator depth)
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
  apply ContractRuntimeEffectsCorrespondence.objectFrame_initializes_extended (fun _ member => RuntimeExtendedInitializedEffects.slots_allowed withCode member) object context contextRelated references initialized separate
    description creatorRelated creatorFound creatorAfter
    (fun cell => ContractEnvironmentCorrespondence.initializedValue (contextEnvironment context image) cell ∧ ContractCodeCorrespondence.initializedCode image cell ∧ initializedReturnData cell ∧
      initializedHandler context.address dispatcherLocation cell ∧ initializedDepth Core.Word.zero cell ∧
      cell.location ≠ dispatcherLocation ∧ sharedOrigin sharedCells cell)
    (fun value _ => MessageRel sourceResult finalSource.external context.address value)
    (FrameInitializersValid.and fresh (FrameInitializersValid.and freshCode (FrameInitializersValid.and freshData
      (FrameInitializersValid.and freshHandler (FrameInitializersValid.and freshDepth (FrameInitializersValid.and freshSeparate freshOrigin))))))
    (fun cell member => ⟨ContractEnvironmentCorrespondence.shared_initialized_value context image description' cell member,
      ContractCodeCorrespondence.shared_code_observation image description' cell member,
      shared_returnData_observation description' cell member,
      shared_handler_observation context.address dispatcherLocation description' cell member,
      shared_depth_observation Core.Word.zero description' cell member,
      Nat.ne_of_lt (dispatcherAfter cell member), fun _ => member⟩)
    (by
      intro value _
      constructor
      · intro _ impossible
        cases impossible
      · exact ⟨ContractCodeCorrespondence.creator_code_observation image creatorLocation value,
          creator_returnData_observation creatorLocation value,
          creator_handler_observation context.address dispatcherLocation creatorLocation value,
          creator_depth_observation Core.Word.zero creatorLocation value,
          Nat.ne_of_gt dispatcherBefore, creator_shared_origin sharedCells creatorLocation value⟩)
  intro extra suffix frameReferences cells worldLocation balancesLocation referenceValues stored signature observations cellLocations
    worldReference balancesReference balancesFound
  have observed := fun cell member => (observations cell member).1
  have environmentObserved := fun cell member => (observations cell member).2.1
  have codeObserved := fun cell member => (observations cell member).2.2.1
  have dataObserved := fun cell member => (observations cell member).2.2.2.1
  have handlerObserved := fun cell member => (observations cell member).2.2.2.2.1
  have depthObserved := fun cell member => (observations cell member).2.2.2.2.2.1
  have dispatchSeparate := fun cell member => (observations cell member).2.2.2.2.2.2.1
  have sharedOrigins := fun cell member => (observations cell member).2.2.2.2.2.2.2
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
  have slotTypes : RuntimeEffectsFrameCorrespondence.slotTypes slots = RuntimeExtendedInitializedEffects.slots withCode := by
    simpa only [RuntimeEffectsFrameCorrespondence.slotTypes, MemoryFrameCorrespondence.slotTypes,
      slots, List.map_map, Function.comp_def, InitializedCell.effectSlot] using signature
  have environmentRelated := initialized_environment cells (RuntimeExtendedInitializedEffects.initialized_unique (withCode := withCode) signature)
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
  have sharedUnique : (sharedCells.map InitializedCell.name).Nodup := by
    rw [capture.names]
    decide
  have sharedNamed := RuntimeCallInitializedEffects.shared_cells baseMembers sharedOrigins
  let dispatchCapture := captured_dispatcher capture _ (sharedNamed.references sharedUnique capture.references)
  let handlers : RuntimeCallEffectsCorrespondence.Handlers callReady.layout := {
    source := context.address
    dispatchValue := capture.closure
    handlerValue := callReady.handlerValue
    dispatch := by simpa only [RuntimeCallEffectsCorrespondence.sharedLocations, callReady.baseEqual] using dispatchCapture
    handler := by simpa only [callReady.dispatcherEqual] using callReady.handler }
  have initialRelated : StateRel (RuntimeCallEffectsCorrespondence.model callReady.layout
      (prefixRead callReady.layout.boundary (initial ++ suffix)) slots image handlers) []
      ⟨[], contextInitialState image object context⟩ (initial ++ suffix) := by
    apply RuntimeCallEffectsCorrespondence.initial_state
    · simpa only [callReady.baseEqual, contextInitialState] using returnRelated
    · exact callReady.depthRead
    · simpa only [callReady.dispatcherEqual, Core.Store.read?, List.getElem?_append_left dispatcherBelow] using capture.stored
    · exact callReady.handlerRead
    · rfl
  have callCodes : ∀ imageCells, callReady.layout.toReturnDataLayout.codeCells = some imageCells →
      ⟨"code", Core.WordMapping.type, imageCells.code⟩ ∈ cells.map InitializedCell.effectSlot ∧
      ⟨"codeKnown", .bool, imageCells.known⟩ ∈ cells.map InitializedCell.effectSlot := by
    rw [callReady.baseEqual]
    exact codeReady.codeMembers
  have callMode : callReady.layout.toReturnDataLayout.codeCells.isSome = withCode := by
    rw [callReady.baseEqual]
    exact codeReady.mode
  have callPassive := RuntimeCallInitializedEffects.call_passive (layout := callReady.layout)
    (RuntimeExtendedInitializedEffects.initialized_unique signature) cellLocations
    (by simpa only [callReady.baseEqual] using baseMembers)
    callCodes
  obtain ⟨value, final, completed, resultRelated⟩ := frameCall_message_evaluates (withCode := withCode)
    (by simpa only [slotTypes] using accepted)
    (by simpa only [supported_actual slotTypes] using eligible) closureRelated
    ((functionsRelated.prepend extra).evaluates (initial ++ suffix))
    ((CodeValue.packet referenceValues).evaluates (initial ++ suffix))
    (by simp [slots]) runtime (RuntimeExtendedInitializedEffects.initialized_separate (withCode := withCode) signature)
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
    callReady.depthMember callReady.handlerMember initialRelated
    (by simpa only [callReady.baseEqual] using passiveEnvironment) callPassive evaluated context.address
    (by simpa only [callReady.baseEqual, storageLocations, worldSame] using worldReference.prepend extra) (by simpa only [callReady.baseEqual, balanceSame] using balancesReference.prepend extra)
    ((contextRelated.part (index := 4) rfl).prepend extra)
    (by simpa only [notDeploying] using (contextRelated.part (index := 11) rfl).prepend extra)
  exact ⟨value, final, completed, resultRelated⟩

end Solcore.Frontend.RustHull.ContractCallCorrespondence
