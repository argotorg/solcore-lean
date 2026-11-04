import Solcore.Frontend.RustHull.ContractCodeTheorems
import Solcore.Frontend.RustHull.Internal.CallEffects
import Solcore.Frontend.RustHull.Internal.CallStates
import Solcore.Frontend.RustHull.Internal.RuntimeObjects
import Solcore.Frontend.RustHull.Internal.ChildFrameCalls
import Solcore.Frontend.RustHull.Internal.ChildFrames

/-!
# Hull contract meaning preservation: calls

The public theorems for message calls: compiled children, finite call trees, all four call modes and
root reentry. Main theorems: `ContractCallCorrespondence.compileObject_resumes_exact`,
`ContractChildCallCorrespondence.compileObject_resumes_exact`,
`ContractNestedChildCallCorrespondence.compileObject_resumes_exact`,
`ContractCallModeCorrespondence.compileObject_resumes_exact`,
`ContractRootCallCorrespondence.compileObject_resumes_exact`.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractCallInitializedExecution
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractCallExecutionCorrespondence
/-! Message calls reach the public contract runner through actual
compilation and initialization, including frames without code slots. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractCallCorrespondence
open Correspondence ScalarExecution CodeBuilder ContractRuntimeEffectsCorrespondence

theorem objectRuntime_preserves {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {others : List Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (RuntimeExtendedInitializedEffects.slots withCode) fuel = .ok compiled)
    (catalogCompiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots withCode) fuel catalog others)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment : Core.Environment} {initial : Core.Store} {contextCode : Code}
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    {finalSource : Semantics.State RuntimeCallEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCallEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime (RuntimeExtendedInitializedEffects.slots withCode) compiled others
        (ContractCatalogCorrespondence.images image catalog) image catalog contextCode depth) value final ∧
      MessageRel sourceResult finalSource.external context.address value := by
  obtain ⟨closure, captured⟩ := compileFrame_captures accepted environment
  obtain ⟨values, captures⟩ := catalogCompiled.captures environment
  apply objectRuntime_evaluates_callbacks
    (fun value _ => MessageRel sourceResult finalSource.external context.address value)
    (.cons captured captures) (ContractMemoryCorrespondence.sharedValues_related object context contextRelated)
  intro functions shared dispatcher creator extra allocated cells dispatcherLocation creatorLocation functionsRelated references initialized separate description _ dispatcherRelated creatorRelated creatorFound creatorAfter dispatcherAfter dispatcherBefore capture
  have entry := ContractCatalogCorrespondence.entry_reference captures functionsRelated
  exact objectFrame_evaluates accepted eligible captured entry object context notDeploying
    (contextRelated.prepend extra) references initialized separate description creatorRelated creatorFound creatorAfter dispatcherRelated dispatcherAfter dispatcherBefore capture evaluated

def PublicMessageRel (context : Contract.Context) (result : Semantics.Result Semantics.Value)
    (state : RuntimeCallEffectsSemantics.State) (value : Core.Value) : Prop :=
  MessageRel result state (Contract.normalizeContext context).address value

/-- The actual compiler supplies every catalog closure. The independent entry
evaluation determines the result, including code availability and copy faults. -/
theorem compileObject_preserves {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {object : Contract.CompiledObject}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel image catalog = .ok object)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported (image.isSome || !catalog.isEmpty))
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (context : Contract.Context) (notDeploying : context.deploying = false)
    {finalSource : Semantics.State RuntimeCallEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCallEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates [] [] (object.instantiate context).expression value final ∧
      PublicMessageRel context sourceResult finalSource.external value := by
  have compiled : AccountRuntime.compileObject program path fuel image catalog = .ok object.expression := by
    unfold Contract.compileObject at accepted
    obtain ⟨expression, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
    cases returned
    exact compiled
  obtain ⟨frame, others, frameCompiled, catalogCompiled, objectExpression⟩ :=
    ContractCatalogCorrespondence.compileObject_selected selected compiled
  have signature : ContractCatalogCorrespondence.slots image catalog =
      RuntimeExtendedInitializedEffects.slots (image.isSome || !catalog.isEmpty) := rfl
  rw [signature] at frameCompiled catalogCompiled objectExpression
  have normalized : (Contract.normalizeContext context).deploying = false := notDeploying
  obtain ⟨value, final, executed, related⟩ := objectRuntime_preserves frameCompiled
    (ContractCatalogCorrespondence.compiledCatalog catalogCompiled) eligible object
    (Contract.normalizeContext context) normalized
    (CodeValue.bound 0 [] (bundleValues (contextValues object (Contract.normalizeContext context)))) evaluated
  refine ⟨value, final, instantiate_evaluates context (parameter := AccountRuntime.contextType)
    (resultType := AccountRuntime.resultType) ?_ executed, related⟩
  rw [objectExpression]
  rfl

/-- Every genuine public resumption chain reaches the independently derived
message exactly when its cumulative fuel covers the required transitions. -/
theorem compileObject_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {object : Contract.CompiledObject}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel image catalog = .ok object)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported (image.isSome || !catalog.isEmpty))
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (context : Contract.Context) (notDeploying : context.deploying = false)
    {finalSource : Semantics.State RuntimeCallEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCallEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value, PublicMessageRel context sourceResult finalSource.external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨value, _, executed, related⟩ :=
    compileObject_preserves selected accepted eligible context notDeploying evaluated
  exact ⟨value, related, Contract.evaluation_resumes_exact executed⟩

theorem prepare_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {context : Contract.Context} {prepared : Contract.Prepared}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.prepare program path context fuel = .ok prepared)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported false)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (notDeploying : context.deploying = false) :
    ∃ object, Contract.compileObject program path fuel none [] = .ok object ∧
      prepared = object.instantiate context ∧
      ∀ (sourceResult : Semantics.Result Semantics.Value) (finalSource : Semantics.State RuntimeCallEffectsSemantics.State),
        Semantics.EvalFunction (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code])
          (RuntimeCallEffectsSemantics.effects none)
          (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState none object (Contract.normalizeContext context)⟩ sourceResult finalSource →
        ∃ value, PublicMessageRel context sourceResult finalSource.external value ∧
          ∃ required, ∀ initialFuel additional limit last,
            Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
            (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
            ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  unfold Contract.prepare at accepted
  obtain ⟨object, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
  cases returned
  exact ⟨object, compiled, rfl, fun _ _ evaluated =>
    compileObject_resumes_exact selected compiled eligible context notDeploying evaluated⟩

end Solcore.Frontend.RustHull.ContractCallCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractCallModeInitializedExecution
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
    {sourceCatalog : ChildFrameSemantics.Catalog} {initCatalog : ChildFrameSemantics.InitCatalog}
    {anchors : List CatalogWorldCorrespondence.Anchor} {height : Nat}
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
      (ChildFrameModeSemantics.effectsAt sourceCatalog initCatalog height))
    (initialLinks : CatalogWorldCorrespondence.Links anchors (StorageCorrespondence.canonical (object.initialWorld context)))
    {finalSource : Semantics.State RuntimeCallEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (ChildFrameModeSemantics.effectsAt sourceCatalog initCatalog (height + 1) image)
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
        (ChildFrameModeSemantics.Children sourceCatalog (ChildFrameModeSemantics.effectsAt sourceCatalog initCatalog height)) operation state.external := by
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractCallModeExecutionCorrespondence
/-! Finite source call trees using CALL, STATICCALL, CALLCODE and DELEGATECALL
reach public receipts and resumption chains. Actual initialization supplies all
three handlers; source-height induction discharges their child execution. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractCallModeCorrespondence
open Correspondence ScalarExecution CodeBuilder ContractRuntimeEffectsCorrespondence
open ContractChildCallCorrespondence (InitialCatalogLinks initial_links)

theorem objectRuntime_preserves {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {others : List Core.Expr}
    {sourceCatalog : ChildFrameSemantics.Catalog} {initCatalog : ChildFrameSemantics.InitCatalog}
    {anchors : List CatalogWorldCorrespondence.Anchor} {height : Nat}
    (accepted : AccountRuntime.compileFrame program code (RuntimeExtendedInitializedEffects.slots true) fuel = .ok compiled)
    (catalogCompiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported true)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (connection : ModeChildCatalogExecutionCorrespondence.CatalogConnection sourceCatalog catalog anchors)
    {depth : Nat} {environment : Core.Environment} {initial : Core.Store} {contextCode : Code}
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    (initialLinks : CatalogWorldCorrespondence.Links anchors (StorageCorrespondence.canonical (object.initialWorld context)))
    {finalSource : Semantics.State RuntimeCallEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code])
      (ChildFrameModeSemantics.effectsAt sourceCatalog initCatalog (height + 1) image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime (RuntimeExtendedInitializedEffects.slots true) compiled others
        (ContractCatalogCorrespondence.images image catalog) image catalog contextCode depth) value final ∧
      MessageRel sourceResult finalSource.external context.address value := by
  obtain ⟨closure, captured⟩ := compileFrame_captures accepted environment
  obtain ⟨values, captures⟩ := catalogCompiled.captures environment
  apply objectRuntime_evaluates_creator
    (fun value _ => MessageRel sourceResult finalSource.external context.address value)
    (.cons captured captures) (ContractMemoryCorrespondence.sharedValues_related object context contextRelated)
  intro functions shared dispatcher creator extra allocated cells dispatcherLocation creatorLocation functionsRelated references initialized separate description _ dispatcherRelated creatorRelated creatorFound creatorAfter dispatcherAfter dispatcherBefore capture createValue createRead createCaptured
  have entry := ContractCatalogCorrespondence.entry_reference captures functionsRelated
  exact objectFrame_evaluates accepted eligible captured entry object context notDeploying
    (contextRelated.prepend extra) references initialized separate description creatorRelated creatorFound creatorAfter
    dispatcherRelated dispatcherAfter dispatcherBefore capture createRead createCaptured catalogCompiled captures connection
    (ModeChildFrameCorrespondence.frame_execution sourceCatalog catalog anchors height) initialLinks evaluated

def PublicMessageRel (context : Contract.Context) (result : Semantics.Result Semantics.Value)
    (state : RuntimeCallEffectsSemantics.State) (value : Core.Value) : Prop :=
  MessageRel result state (Contract.normalizeContext context).address value

/-- Account code is checked in the same normalized source state that begins the
public execution. No Core store, captured closure or execution premise occurs. -/
def InitialContextLinks (image : Option (List UInt8)) (catalog : List AccountRuntime.CodeDefinition)
    (object : Contract.CompiledObject) (context : Contract.Context) (anchors : List CatalogWorldCorrespondence.Anchor) : Prop :=
  let normalized := Contract.normalizeContext context
  InitialCatalogLinks image catalog anchors (Contract.normalizeAddress normalized.address)
    (contextInitialState image object normalized).runtime.runtime.runtime.runtime.runtime.storage.world

-- The init-frame creation rule, which reads `initConnection`, follows separately.
set_option linter.unusedVariables false in
theorem compileObject_preserves {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {object : Contract.CompiledObject}
    {sourceCatalog : ChildFrameSemantics.Catalog} {initCatalog : ChildFrameSemantics.InitCatalog}
    {anchors : List CatalogWorldCorrespondence.Anchor} {height : Nat}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel image catalog = .ok object)
    (hasCode : (image.isSome || !catalog.isEmpty) = true)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported true)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (connection : ModeChildCatalogExecutionCorrespondence.CatalogConnection sourceCatalog catalog anchors)
    (initConnection : InitCatalogCorrespondence.InitCatalogConnection initCatalog image catalog)
    (context : Contract.Context) (notDeploying : context.deploying = false)
    (initialLinks : InitialContextLinks image catalog object context anchors)
    {finalSource : Semantics.State RuntimeCallEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code])
      (ChildFrameModeSemantics.effectsAt sourceCatalog initCatalog (height + 1) image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates [] [] (object.instantiate context).expression value final ∧
      PublicMessageRel context sourceResult finalSource.external value := by
  have compiled : AccountRuntime.compileObject program path fuel image catalog = .ok object.expression := by
    unfold Contract.compileObject at accepted
    obtain ⟨expression, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
    cases returned
    exact compiled
  obtain ⟨frame, others, frameCompiled, catalogCompiled, objectExpression⟩ :=
    ContractCatalogCorrespondence.compileObject_selected selected compiled
  have signature : ContractCatalogCorrespondence.slots image catalog = RuntimeExtendedInitializedEffects.slots true := by
    change RuntimeExtendedInitializedEffects.slots (image.isSome || !catalog.isEmpty) = _
    rw [hasCode]
  rw [signature] at frameCompiled catalogCompiled objectExpression
  have normalized : (Contract.normalizeContext context).deploying = false := notDeploying
  have links := initial_links object (Contract.normalizeContext context)
    (CatalogWorldCorrespondence.compileObject_images accepted) initialLinks
  obtain ⟨value, final, executed, related⟩ := objectRuntime_preserves frameCompiled
    (ContractCatalogCorrespondence.compiledCatalog catalogCompiled) eligible connection object
    (Contract.normalizeContext context) normalized
    (CodeValue.bound 0 [] (bundleValues (contextValues object (Contract.normalizeContext context)))) links evaluated
  refine ⟨value, final, instantiate_evaluates context (parameter := AccountRuntime.contextType)
    (resultType := AccountRuntime.resultType) ?_ executed, related⟩
  rw [objectExpression]
  rfl

/-- Public resumption uses the actual compiled evaluator. Its fuel threshold is
exact for the independently derived parent and child result. -/
theorem compileObject_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {object : Contract.CompiledObject}
    {sourceCatalog : ChildFrameSemantics.Catalog} {initCatalog : ChildFrameSemantics.InitCatalog}
    {anchors : List CatalogWorldCorrespondence.Anchor} {height : Nat}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel image catalog = .ok object)
    (hasCode : (image.isSome || !catalog.isEmpty) = true)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported true)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (connection : ModeChildCatalogExecutionCorrespondence.CatalogConnection sourceCatalog catalog anchors)
    (initConnection : InitCatalogCorrespondence.InitCatalogConnection initCatalog image catalog)
    (context : Contract.Context) (notDeploying : context.deploying = false)
    (initialLinks : InitialContextLinks image catalog object context anchors)
    {finalSource : Semantics.State RuntimeCallEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code])
      (ChildFrameModeSemantics.effectsAt sourceCatalog initCatalog (height + 1) image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value, PublicMessageRel context sourceResult finalSource.external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨value, _, executed, related⟩ :=
    compileObject_preserves selected accepted hasCode eligible connection initConnection context notDeploying initialLinks
      evaluated
  exact ⟨value, related, Contract.evaluation_resumes_exact executed⟩

end Solcore.Frontend.RustHull.ContractCallModeCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractChildCallInitializedExecution
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractChildCallExecutionCorrespondence
/-! Compiled catalog children reach public receipts and genuine resumption
chains. Initial identities follow from source account code and static catalog
selection; child execution follows from its independent source derivation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractChildCallCorrespondence
open Correspondence ScalarExecution CodeBuilder ContractRuntimeEffectsCorrespondence

theorem objectRuntime_preserves {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {others : List Core.Expr}
    {sourceCatalog : ChildFrameSemantics.Catalog} {anchors : List CatalogWorldCorrespondence.Anchor}
    (accepted : AccountRuntime.compileFrame program code (RuntimeExtendedInitializedEffects.slots true) fuel = .ok compiled)
    (catalogCompiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported true)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (connection : ChildCatalogExecutionCorrespondence.CatalogConnection sourceCatalog catalog anchors)
    {depth : Nat} {environment : Core.Environment} {initial : Core.Store} {contextCode : Code}
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    (initialLinks : CatalogWorldCorrespondence.Links anchors (StorageCorrespondence.canonical (object.initialWorld context)))
    {finalSource : Semantics.State RuntimeCallEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code])
      (RuntimeCallEffectsSemantics.effectsWith (ChildFrameSemantics.CallFree sourceCatalog) image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime (RuntimeExtendedInitializedEffects.slots true) compiled others
        (ContractCatalogCorrespondence.images image catalog) image catalog contextCode depth) value final ∧
      MessageRel sourceResult finalSource.external context.address value := by
  obtain ⟨closure, captured⟩ := compileFrame_captures accepted environment
  obtain ⟨values, captures⟩ := catalogCompiled.captures environment
  apply objectRuntime_evaluates_callbacks
    (fun value _ => MessageRel sourceResult finalSource.external context.address value)
    (.cons captured captures) (ContractMemoryCorrespondence.sharedValues_related object context contextRelated)
  intro functions shared dispatcher creator extra allocated cells dispatcherLocation creatorLocation functionsRelated references initialized separate description _ dispatcherRelated creatorRelated creatorFound creatorAfter dispatcherAfter dispatcherBefore capture
  have entry := ContractCatalogCorrespondence.entry_reference captures functionsRelated
  exact objectFrame_evaluates accepted eligible captured entry object context notDeploying
    (contextRelated.prepend extra) references initialized separate description creatorRelated creatorFound creatorAfter
    dispatcherRelated dispatcherAfter dispatcherBefore capture catalogCompiled captures connection initialLinks evaluated

def PublicMessageRel (context : Contract.Context) (result : Semantics.Result Semantics.Value)
    (state : RuntimeCallEffectsSemantics.State) (value : Core.Value) : Prop :=
  MessageRel result state (Contract.normalizeContext context).address value

/-- Account code is checked in the same normalized source state that begins the
public execution. No Core store, captured closure or execution premise occurs. -/
def InitialContextLinks (image : Option (List UInt8)) (catalog : List AccountRuntime.CodeDefinition)
    (object : Contract.CompiledObject) (context : Contract.Context) (anchors : List CatalogWorldCorrespondence.Anchor) : Prop :=
  let normalized := Contract.normalizeContext context
  InitialCatalogLinks image catalog anchors (Contract.normalizeAddress normalized.address)
    (contextInitialState image object normalized).runtime.runtime.runtime.runtime.runtime.storage.world

theorem compileObject_preserves {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {object : Contract.CompiledObject}
    {sourceCatalog : ChildFrameSemantics.Catalog} {anchors : List CatalogWorldCorrespondence.Anchor}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel image catalog = .ok object)
    (hasCode : (image.isSome || !catalog.isEmpty) = true)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported true)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (connection : ChildCatalogExecutionCorrespondence.CatalogConnection sourceCatalog catalog anchors)
    (context : Contract.Context) (notDeploying : context.deploying = false)
    (initialLinks : InitialContextLinks image catalog object context anchors)
    {finalSource : Semantics.State RuntimeCallEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code])
      (RuntimeCallEffectsSemantics.effectsWith (ChildFrameSemantics.CallFree sourceCatalog) image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates [] [] (object.instantiate context).expression value final ∧
      PublicMessageRel context sourceResult finalSource.external value := by
  have compiled : AccountRuntime.compileObject program path fuel image catalog = .ok object.expression := by
    unfold Contract.compileObject at accepted
    obtain ⟨expression, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
    cases returned
    exact compiled
  obtain ⟨frame, others, frameCompiled, catalogCompiled, objectExpression⟩ :=
    ContractCatalogCorrespondence.compileObject_selected selected compiled
  have signature : ContractCatalogCorrespondence.slots image catalog = RuntimeExtendedInitializedEffects.slots true := by
    change RuntimeExtendedInitializedEffects.slots (image.isSome || !catalog.isEmpty) = _
    rw [hasCode]
  rw [signature] at frameCompiled catalogCompiled objectExpression
  have normalized : (Contract.normalizeContext context).deploying = false := notDeploying
  have links := initial_links object (Contract.normalizeContext context)
    (CatalogWorldCorrespondence.compileObject_images accepted) initialLinks
  obtain ⟨value, final, executed, related⟩ := objectRuntime_preserves frameCompiled
    (ContractCatalogCorrespondence.compiledCatalog catalogCompiled) eligible connection object
    (Contract.normalizeContext context) normalized
    (CodeValue.bound 0 [] (bundleValues (contextValues object (Contract.normalizeContext context)))) links evaluated
  refine ⟨value, final, instantiate_evaluates context (parameter := AccountRuntime.contextType)
    (resultType := AccountRuntime.resultType) ?_ executed, related⟩
  rw [objectExpression]
  rfl

/-- Public resumption uses the actual compiled evaluator. Its fuel threshold is
exact for the independently derived parent and child result. -/
theorem compileObject_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {object : Contract.CompiledObject}
    {sourceCatalog : ChildFrameSemantics.Catalog} {anchors : List CatalogWorldCorrespondence.Anchor}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel image catalog = .ok object)
    (hasCode : (image.isSome || !catalog.isEmpty) = true)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported true)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (connection : ChildCatalogExecutionCorrespondence.CatalogConnection sourceCatalog catalog anchors)
    (context : Contract.Context) (notDeploying : context.deploying = false)
    (initialLinks : InitialContextLinks image catalog object context anchors)
    {finalSource : Semantics.State RuntimeCallEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code])
      (RuntimeCallEffectsSemantics.effectsWith (ChildFrameSemantics.CallFree sourceCatalog) image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value, PublicMessageRel context sourceResult finalSource.external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨value, _, executed, related⟩ :=
    compileObject_preserves selected accepted hasCode eligible connection context notDeploying initialLinks evaluated
  exact ⟨value, related, Contract.evaluation_resumes_exact executed⟩

end Solcore.Frontend.RustHull.ContractChildCallCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractNestedChildCallInitializedExecution
/-! Actual parent initialization supplies the shared inventory, catalog links and
callback closure needed for independently derived child calls. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractNestedChildCallCorrespondence
open Correspondence ScalarExecution CodeBuilder ContractRuntimeEffectsCorrespondence ContractEnvironmentCorrespondence
open ContractCallCorrespondence hiding supported supported_actual MessageRel contextInitialState
open ContractChildCallCorrespondence
open ContractReturnDataCorrespondence (initializedReturnData fresh_returnData_observation shared_returnData_observation creator_returnData_observation initialized_returnDataSize)

abbrev contextInitialState := ContractCallCorrespondence.contextInitialState
abbrev supported := ContractChildCallCorrespondence.supported
abbrev MessageRel := ContractChildCallCorrespondence.MessageRel

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
    (catalogCompiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    (catalogCaptured : CapturedClosures captured others catalogValues)
    (connection : NestedChildCatalogExecutionCorrespondence.CatalogConnection sourceCatalog catalog anchors)
    (frameExecution : NestedChildCatalogExecutionCorrespondence.FrameExecution sourceCatalog catalog anchors
      (ChildFrameSemantics.effectsAt sourceCatalog height))
    (initialLinks : CatalogWorldCorrespondence.Links anchors (StorageCorrespondence.canonical (object.initialWorld context)))
    {finalSource : Semantics.State RuntimeCallEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (ChildFrameSemantics.effectsAt sourceCatalog (height + 1) image)
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
  have childInitial := RuntimeChildCallEffectsCorrespondence.of_base initialRelated linkedInitial capturedValid
  have callbacks : ∀ {world state current},
      StateRel (RuntimeChildCallEffectsCorrespondence.model callReady.layout
        (prefixRead callReady.layout.boundary (initial ++ suffix)) slots image handlers anchors callbackContext) world state current →
      RuntimeChildCallEffectsCorrespondence.CallbackPreservation callReady.layout handlers anchors callbackContext
        (ChildFrameSemantics.Children sourceCatalog (ChildFrameSemantics.effectsAt sourceCatalog height)) state.external := by
    intro world state current related
    have base := RuntimeChildCallEffectsCorrespondence.base_related related
    have ambient := ChildCallbackContextCorrespondence.parent_observed inventory sharedMembers base related.external.2.2.1.2.1
    apply RuntimeChildCallEffectsCorrespondence.callback_preserves
    · exact RuntimeCallEffectsCorrespondence.source_eq base
    · exact NestedChildCatalogExecutionCorrespondence.captured_child_runs_preserves connection frameExecution catalogCompiled catalogCaptured
        (NestedChildCallbackContextCorrespondence.withDispatcher capture callReady.layout.dispatcher callReady.dispatcherEqual)
        nestedInventory (inventory_references inventory capture.references) state.external ambient
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

end Solcore.Frontend.RustHull.ContractNestedChildCallCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractNestedChildCallExecutionCorrespondence
/-! Finite nested source call trees reach public receipts and genuine
resumption chains. The internal frame interface is discharged by induction on
source height, independently of the Core evaluator's fuel. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractNestedChildCallCorrespondence
open Correspondence ScalarExecution CodeBuilder ContractRuntimeEffectsCorrespondence
open ContractChildCallCorrespondence (InitialCatalogLinks initial_links)

theorem objectRuntime_preserves {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {others : List Core.Expr}
    {sourceCatalog : ChildFrameSemantics.Catalog} {anchors : List CatalogWorldCorrespondence.Anchor} {height : Nat}
    (accepted : AccountRuntime.compileFrame program code (RuntimeExtendedInitializedEffects.slots true) fuel = .ok compiled)
    (catalogCompiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported true)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (connection : NestedChildCatalogExecutionCorrespondence.CatalogConnection sourceCatalog catalog anchors)
    {depth : Nat} {environment : Core.Environment} {initial : Core.Store} {contextCode : Code}
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    (initialLinks : CatalogWorldCorrespondence.Links anchors (StorageCorrespondence.canonical (object.initialWorld context)))
    {finalSource : Semantics.State RuntimeCallEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code])
      (ChildFrameSemantics.effectsAt sourceCatalog (height + 1) image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime (RuntimeExtendedInitializedEffects.slots true) compiled others
        (ContractCatalogCorrespondence.images image catalog) image catalog contextCode depth) value final ∧
      MessageRel sourceResult finalSource.external context.address value := by
  obtain ⟨closure, captured⟩ := compileFrame_captures accepted environment
  obtain ⟨values, captures⟩ := catalogCompiled.captures environment
  apply objectRuntime_evaluates_callbacks
    (fun value _ => MessageRel sourceResult finalSource.external context.address value)
    (.cons captured captures) (ContractMemoryCorrespondence.sharedValues_related object context contextRelated)
  intro functions shared dispatcher creator extra allocated cells dispatcherLocation creatorLocation functionsRelated references initialized separate description _ dispatcherRelated creatorRelated creatorFound creatorAfter dispatcherAfter dispatcherBefore capture
  have entry := ContractCatalogCorrespondence.entry_reference captures functionsRelated
  exact objectFrame_evaluates accepted eligible captured entry object context notDeploying
    (contextRelated.prepend extra) references initialized separate description creatorRelated creatorFound creatorAfter
    dispatcherRelated dispatcherAfter dispatcherBefore capture catalogCompiled captures connection
    (NestedChildFrameCorrespondence.frame_execution sourceCatalog catalog anchors height) initialLinks evaluated

def PublicMessageRel (context : Contract.Context) (result : Semantics.Result Semantics.Value)
    (state : RuntimeCallEffectsSemantics.State) (value : Core.Value) : Prop :=
  MessageRel result state (Contract.normalizeContext context).address value

/-- Account code is checked in the same normalized source state that begins the
public execution. No Core store, captured closure or execution premise occurs. -/
def InitialContextLinks (image : Option (List UInt8)) (catalog : List AccountRuntime.CodeDefinition)
    (object : Contract.CompiledObject) (context : Contract.Context) (anchors : List CatalogWorldCorrespondence.Anchor) : Prop :=
  let normalized := Contract.normalizeContext context
  InitialCatalogLinks image catalog anchors (Contract.normalizeAddress normalized.address)
    (contextInitialState image object normalized).runtime.runtime.runtime.runtime.runtime.storage.world

theorem compileObject_preserves {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {object : Contract.CompiledObject}
    {sourceCatalog : ChildFrameSemantics.Catalog} {anchors : List CatalogWorldCorrespondence.Anchor} {height : Nat}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel image catalog = .ok object)
    (hasCode : (image.isSome || !catalog.isEmpty) = true)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported true)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (connection : NestedChildCatalogExecutionCorrespondence.CatalogConnection sourceCatalog catalog anchors)
    (context : Contract.Context) (notDeploying : context.deploying = false)
    (initialLinks : InitialContextLinks image catalog object context anchors)
    {finalSource : Semantics.State RuntimeCallEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code])
      (ChildFrameSemantics.effectsAt sourceCatalog (height + 1) image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates [] [] (object.instantiate context).expression value final ∧
      PublicMessageRel context sourceResult finalSource.external value := by
  have compiled : AccountRuntime.compileObject program path fuel image catalog = .ok object.expression := by
    unfold Contract.compileObject at accepted
    obtain ⟨expression, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
    cases returned
    exact compiled
  obtain ⟨frame, others, frameCompiled, catalogCompiled, objectExpression⟩ :=
    ContractCatalogCorrespondence.compileObject_selected selected compiled
  have signature : ContractCatalogCorrespondence.slots image catalog = RuntimeExtendedInitializedEffects.slots true := by
    change RuntimeExtendedInitializedEffects.slots (image.isSome || !catalog.isEmpty) = _
    rw [hasCode]
  rw [signature] at frameCompiled catalogCompiled objectExpression
  have normalized : (Contract.normalizeContext context).deploying = false := notDeploying
  have links := initial_links object (Contract.normalizeContext context)
    (CatalogWorldCorrespondence.compileObject_images accepted) initialLinks
  obtain ⟨value, final, executed, related⟩ := objectRuntime_preserves frameCompiled
    (ContractCatalogCorrespondence.compiledCatalog catalogCompiled) eligible connection object
    (Contract.normalizeContext context) normalized
    (CodeValue.bound 0 [] (bundleValues (contextValues object (Contract.normalizeContext context)))) links evaluated
  refine ⟨value, final, instantiate_evaluates context (parameter := AccountRuntime.contextType)
    (resultType := AccountRuntime.resultType) ?_ executed, related⟩
  rw [objectExpression]
  rfl

/-- Public resumption uses the actual compiled evaluator. Its fuel threshold is
exact for the independently derived parent and child result. -/
theorem compileObject_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {object : Contract.CompiledObject}
    {sourceCatalog : ChildFrameSemantics.Catalog} {anchors : List CatalogWorldCorrespondence.Anchor} {height : Nat}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel image catalog = .ok object)
    (hasCode : (image.isSome || !catalog.isEmpty) = true)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported true)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (connection : NestedChildCatalogExecutionCorrespondence.CatalogConnection sourceCatalog catalog anchors)
    (context : Contract.Context) (notDeploying : context.deploying = false)
    (initialLinks : InitialContextLinks image catalog object context anchors)
    {finalSource : Semantics.State RuntimeCallEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code])
      (ChildFrameSemantics.effectsAt sourceCatalog (height + 1) image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value, PublicMessageRel context sourceResult finalSource.external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨value, _, executed, related⟩ :=
    compileObject_preserves selected accepted hasCode eligible connection context notDeploying initialLinks evaluated
  exact ⟨value, related, Contract.evaluation_resumes_exact executed⟩

end Solcore.Frontend.RustHull.ContractNestedChildCallCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractRootCallInitializedExecution
/-! Actual root initialization supplies its own compiled closure alongside the
catalog captures, so finite child trees may reenter the packet-head frame. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractRootCallCorrespondence
open Correspondence ScalarExecution CodeBuilder ContractRuntimeEffectsCorrespondence ContractEnvironmentCorrespondence
open ContractCallCorrespondence hiding supported supported_actual MessageRel contextInitialState
open ContractCallModeCorrespondence (supported supported_actual MessageRel frameCall_message_evaluates)
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
    {images : List (Nat × List UInt8)} {rootBytes : List UInt8} {shared : AccountRuntime.References}
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
    {sourceCatalog : ChildFrameSemantics.Catalog} {initCatalog : ChildFrameSemantics.InitCatalog}
    {anchors : List CatalogWorldCorrespondence.Anchor} {height : Nat}
    (capture : ObjectCallbackCapture (RuntimeExtendedInitializedEffects.slots true) (others.length + 1) images catalog
      (closure :: catalogValues) sharedCells dispatcherLocation creatorLocation initial)
    {createValue : Core.Value} (createRead : initial.read? creatorLocation = some (.inRight .unit createValue))
    (createCaptured : CapturedClosure ((AccountRuntime.objectHandlers (RuntimeExtendedInitializedEffects.slots true)
      (others.length + 1) images catalog capture.functions capture.shared capture.dispatcher capture.creator).2
      (capture.depth + 1)) (.unit :: capture.environment) createValue)
    (catalogCompiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    (catalogCaptured : CapturedClosures captured others catalogValues)
    (connection : RootChildCatalogExecutionCorrespondence.CatalogConnection ⟨program, code, rootBytes⟩ sourceCatalog catalog anchors)
    (frameExecution : RootChildCatalogExecutionCorrespondence.FrameExecution ⟨program, code, rootBytes⟩ sourceCatalog catalog anchors
      (ChildFrameModeSemantics.effectsAt sourceCatalog initCatalog height))
    (initialLinks : CatalogWorldCorrespondence.Links anchors (StorageCorrespondence.canonical (object.initialWorld context)))
    {finalSource : Semantics.State RuntimeCallEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (ChildFrameModeSemantics.effectsAt sourceCatalog initCatalog (height + 1) (some rootBytes))
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState (some rootBytes) object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectFrame (RuntimeExtendedInitializedEffects.slots true) (others.length + 1) images (some rootBytes) contextCode functions shared dispatcher creator depth)
      value final ∧ MessageRel sourceResult finalSource.external context.address value := by
  have rootCaptured : RootChildCatalogExecutionCorrespondence.RootFrame ⟨program, code, rootBytes⟩ fuel captured closure :=
    ⟨compiled, accepted, eligible, closureRelated⟩
  let accounts := StorageCorrespondence.canonical (object.initialWorld context)
  let balances := Core.WordMapping.insertEntries context.address context.balance context.accounts
  have description' : sharedCells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip
        (ContractMemoryCorrespondence.sharedValues accounts context.completeWorld balances (ambientValues context.ambient))).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse := description
  have fresh : FrameInitializersValid depth environment initial
      (ContractMemoryCorrespondence.requestCode contextCode) dispatcher (part 5 12 contextCode)
      (constant (Core.WordMapping.literal (Memory.packBytes ((some rootBytes).getD []))))
      (number ((some rootBytes).getD []).length) (CodeBuilder.boolean (some rootBytes).isSome) shared
      (ContractEnvironmentCorrespondence.initializedValue (contextEnvironment context (some rootBytes))) :=
    ContractEnvironmentCorrespondence.fresh_initializers_observation_image context (some rootBytes) (ContractMemoryCorrespondence.request_related object context contextRelated)
      (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes ((some rootBytes).getD [])) depth environment)
      (CodeValue.number ((some rootBytes).getD []).length depth environment) (CodeValue.boolean (some rootBytes).isSome depth environment) references description'
  have freshCode := ContractCodeCorrespondence.fresh_code_observation (store := initial) (dispatcher := dispatcher) (shared := shared) (some rootBytes)
    (ContractMemoryCorrespondence.request_related object context contextRelated) rfl
    (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes ((some rootBytes).getD [])) depth environment)
    (CodeValue.number ((some rootBytes).getD []).length depth environment) (CodeValue.boolean (some rootBytes).isSome depth environment)
  have freshData := fresh_returnData_observation (store := initial) (dispatcher := dispatcher) (shared := shared)
    (ContractMemoryCorrespondence.request_related object context contextRelated) rfl
    (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes ((some rootBytes).getD [])) depth environment)
    (CodeValue.number ((some rootBytes).getD []).length depth environment) (CodeValue.boolean (some rootBytes).isSome depth environment)
  have dispatcherBelow : dispatcherLocation < initial.length :=
    (List.getElem?_eq_some_iff.mp capture.stored).1
  have freshHandler := fresh_handler_observation (store := initial) (shared := shared)
    (ContractMemoryCorrespondence.request_related object context contextRelated) rfl rfl dispatcherRelated
    (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes ((some rootBytes).getD [])) depth environment)
    (CodeValue.number ((some rootBytes).getD []).length depth environment) (CodeValue.boolean (some rootBytes).isSome depth environment)
  have freshCallCode := ChildFrameModeCorrespondence.fresh_handler_observation .callCode (store := initial) (shared := shared)
    (ContractMemoryCorrespondence.request_related object context contextRelated) rfl rfl dispatcherRelated
    (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes ((some rootBytes).getD [])) depth environment)
    (CodeValue.number ((some rootBytes).getD []).length depth environment) (CodeValue.boolean (some rootBytes).isSome depth environment)
  have freshDelegate := ChildFrameModeCorrespondence.fresh_handler_observation .delegateCall (store := initial) (shared := shared)
    (ContractMemoryCorrespondence.request_related object context contextRelated) rfl rfl dispatcherRelated
    (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes ((some rootBytes).getD [])) depth environment)
    (CodeValue.number ((some rootBytes).getD []).length depth environment) (CodeValue.boolean (some rootBytes).isSome depth environment)
  have freshDepth := fresh_depth_observation (store := initial) (dispatcher := dispatcher) (shared := shared)
    (ContractMemoryCorrespondence.request_related object context contextRelated) rfl rfl
    (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes ((some rootBytes).getD [])) depth environment)
    (CodeValue.number ((some rootBytes).getD []).length depth environment) (CodeValue.boolean (some rootBytes).isSome depth environment)
  have freshSeparate := fresh_dispatcher_separate (dispatcher := dispatcher) (shared := shared) dispatcherBelow
    (ContractMemoryCorrespondence.request_related object context contextRelated) rfl
    (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes ((some rootBytes).getD [])) depth environment)
    (CodeValue.number ((some rootBytes).getD []).length depth environment) (CodeValue.boolean (some rootBytes).isSome depth environment)
  have sharedPresent : ∀ name ∈ dispatchSharedNames, name ∈ sharedCells.map InitializedCell.name := by
    rw [capture.names]
    intro name member
    simp only [dispatchSharedNames, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [sharedSlotTypes]
  have freshOrigin := fresh_shared_origin (store := initial) (dispatcher := dispatcher) references sharedPresent
    (ContractMemoryCorrespondence.request_related object context contextRelated) rfl
    (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes ((some rootBytes).getD [])) depth environment)
    (CodeValue.number ((some rootBytes).getD []).length depth environment) (CodeValue.boolean (some rootBytes).isSome depth environment)
  have sharedSignature := ContractChildCallCorrespondence.shared_signature description (by
    simp [AccountRuntime.sharedInitializers, ContractMemoryCorrespondence.contextSharedValues,
      ambientValues, Ambient.slots])
  have childOrigin := ChildCallbackContextCorrespondence.fresh_origin (store := initial) (dispatcher := dispatcher) references sharedSignature
    (ContractMemoryCorrespondence.request_related object context contextRelated) rfl
    (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes ((some rootBytes).getD [])) depth environment)
    (CodeValue.number ((some rootBytes).getD []).length depth environment) (CodeValue.boolean (some rootBytes).isSome depth environment)
  apply ContractRuntimeEffectsCorrespondence.objectFrame_initializes_creator (fun _ member => RuntimeExtendedInitializedEffects.slots_allowed true member) object context contextRelated references initialized separate
    description creatorRelated creatorFound creatorAfter
    (fun cell => (ContractEnvironmentCorrespondence.initializedValue (contextEnvironment context (some rootBytes)) cell ∧ ContractCodeCorrespondence.initializedCode (some rootBytes) cell ∧ initializedReturnData cell ∧
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
    (fun cell member => ⟨⟨ContractEnvironmentCorrespondence.shared_initialized_value context (some rootBytes) description' cell member,
      ContractCodeCorrespondence.shared_code_observation (some rootBytes) description' cell member,
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
        · exact ⟨ContractCodeCorrespondence.creator_code_observation (some rootBytes) creatorLocation value,
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
    (image := (some rootBytes)) dataObserved
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
      (prefixRead codeReady.layout.boundary (initial ++ suffix)) slots (some rootBytes)) []
      ⟨[], ContractReturnDataCorrespondence.contextInitialState (some rootBytes) object context⟩ (initial ++ suffix) := by
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
      (prefixRead callReady.layout.boundary (initial ++ suffix)) slots (some rootBytes) ordinaryHandlers) []
      ⟨[], contextInitialState (some rootBytes) object context⟩ (initial ++ suffix) := by
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
      (RuntimeChildCallEffectsCorrespondence.sourceWorld (contextInitialState (some rootBytes) object context))
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
        (prefixRead callReady.layout.boundary (initial ++ suffix)) slots (some rootBytes) handlers anchors callbackContext) world state current →
      ∀ operation, RuntimeCallModeEffectsCorrespondence.CallbackPreservation callReady.layout handlers anchors callbackContext
        (ChildFrameModeSemantics.Children sourceCatalog (ChildFrameModeSemantics.effectsAt sourceCatalog initCatalog height)) operation state.external := by
    intro world state current related operation
    have base := RuntimeCallModeEffectsCorrespondence.base_related related
    have ambient := ChildCallbackContextCorrespondence.parent_observed inventory sharedMembers base related.external.2.2.1.2.1.1
    apply RuntimeCallModeEffectsCorrespondence.callback_preserves
    · exact RuntimeCallEffectsCorrespondence.source_eq base
    · apply AccountCallModeCorrespondence.ChildRunPreservation.strengthen
        (RootChildCatalogExecutionCorrespondence.captured_child_runs_preserves connection frameExecution catalogCompiled catalogCaptured rootCaptured
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

end Solcore.Frontend.RustHull.ContractRootCallCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractRootCallExecutionCorrespondence
/-! Root and catalog calls reach public receipts and resumption chains. The actual
entry compilation and captured closure supply root reentry; source-height
induction discharges every executed child without an execution premise. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractRootCallCorrespondence
open Correspondence ScalarExecution CodeBuilder ContractRuntimeEffectsCorrespondence
open ContractCallModeCorrespondence (supported MessageRel)

theorem objectRuntime_preserves {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    {rootBytes : List UInt8} {catalog : List AccountRuntime.CodeDefinition} {others : List Core.Expr}
    {sourceCatalog : ChildFrameSemantics.Catalog} {initCatalog : ChildFrameSemantics.InitCatalog}
    {anchors : List CatalogWorldCorrespondence.Anchor} {height : Nat}
    (accepted : AccountRuntime.compileFrame program code (RuntimeExtendedInitializedEffects.slots true) fuel = .ok compiled)
    (catalogCompiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported true)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (connection : RootChildCatalogExecutionCorrespondence.CatalogConnection ⟨program, code, rootBytes⟩ sourceCatalog catalog anchors)
    {depth : Nat} {environment : Core.Environment} {initial : Core.Store} {contextCode : Code}
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    (initialLinks : CatalogWorldCorrespondence.Links anchors (StorageCorrespondence.canonical (object.initialWorld context)))
    {finalSource : Semantics.State RuntimeCallEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code])
      (ChildFrameModeSemantics.effectsAt sourceCatalog initCatalog (height + 1) (some rootBytes))
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState (some rootBytes) object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime (RuntimeExtendedInitializedEffects.slots true) compiled others
        (ContractCatalogCorrespondence.images (some rootBytes) catalog) (some rootBytes) catalog contextCode depth) value final ∧
      MessageRel sourceResult finalSource.external context.address value := by
  obtain ⟨closure, captured⟩ := compileFrame_captures accepted environment
  obtain ⟨values, captures⟩ := catalogCompiled.captures environment
  apply objectRuntime_evaluates_creator
    (fun value _ => MessageRel sourceResult finalSource.external context.address value)
    (.cons captured captures) (ContractMemoryCorrespondence.sharedValues_related object context contextRelated)
  intro functions shared dispatcher creator extra allocated cells dispatcherLocation creatorLocation functionsRelated references initialized separate description _ dispatcherRelated creatorRelated creatorFound creatorAfter dispatcherAfter dispatcherBefore capture createValue createRead createCaptured
  have entry := ContractCatalogCorrespondence.entry_reference captures functionsRelated
  exact objectFrame_evaluates accepted eligible captured entry object context notDeploying
    (contextRelated.prepend extra) references initialized separate description creatorRelated creatorFound creatorAfter
    dispatcherRelated dispatcherAfter dispatcherBefore capture createRead createCaptured catalogCompiled captures connection
    (RootChildFrameCorrespondence.frame_execution ⟨program, code, rootBytes⟩ sourceCatalog catalog anchors height) initialLinks evaluated

def PublicMessageRel (context : Contract.Context) (result : Semantics.Result Semantics.Value)
    (state : RuntimeCallEffectsSemantics.State) (value : Core.Value) : Prop :=
  MessageRel result state (Contract.normalizeContext context).address value

-- The init-frame creation rule, which reads `initConnection`, follows separately.
set_option linter.unusedVariables false in
theorem compileObject_preserves {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {rootBytes : List UInt8} {catalog : List AccountRuntime.CodeDefinition} {object : Contract.CompiledObject}
    {sourceCatalog : ChildFrameSemantics.Catalog} {initCatalog : ChildFrameSemantics.InitCatalog}
    {anchors : List CatalogWorldCorrespondence.Anchor} {height : Nat}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel (some rootBytes) catalog = .ok object)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported true)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (connection : RootChildCatalogExecutionCorrespondence.CatalogConnection ⟨program, code, rootBytes⟩ sourceCatalog catalog anchors)
    (initConnection : InitCatalogCorrespondence.InitCatalogConnection initCatalog (some rootBytes) catalog)
    (context : Contract.Context) (notDeploying : context.deploying = false)
    (initialLinks : InitialContextLinks (some rootBytes) catalog object context anchors)
    {finalSource : Semantics.State RuntimeCallEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code])
      (ChildFrameModeSemantics.effectsAt sourceCatalog initCatalog (height + 1) (some rootBytes))
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState (some rootBytes) object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates [] [] (object.instantiate context).expression value final ∧
      PublicMessageRel context sourceResult finalSource.external value := by
  have compiled : AccountRuntime.compileObject program path fuel (some rootBytes) catalog = .ok object.expression := by
    unfold Contract.compileObject at accepted
    obtain ⟨expression, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
    cases returned
    exact compiled
  obtain ⟨frame, others, frameCompiled, catalogCompiled, objectExpression⟩ :=
    ContractCatalogCorrespondence.compileObject_selected selected compiled
  have signature : ContractCatalogCorrespondence.slots (some rootBytes) catalog = RuntimeExtendedInitializedEffects.slots true := by
    change RuntimeExtendedInitializedEffects.slots ((some rootBytes).isSome || !catalog.isEmpty) = _
    rfl
  rw [signature] at frameCompiled catalogCompiled objectExpression
  have normalized : (Contract.normalizeContext context).deploying = false := notDeploying
  have links := initial_context_links accepted context initialLinks
  obtain ⟨value, final, executed, related⟩ := objectRuntime_preserves frameCompiled
    (ContractCatalogCorrespondence.compiledCatalog catalogCompiled) eligible connection object
    (Contract.normalizeContext context) normalized
    (CodeValue.bound 0 [] (bundleValues (contextValues object (Contract.normalizeContext context)))) links evaluated
  refine ⟨value, final, instantiate_evaluates context (parameter := AccountRuntime.contextType)
    (resultType := AccountRuntime.resultType) ?_ executed, related⟩
  rw [objectExpression]
  rfl

/-- Public resumption uses the actual compiled evaluator. Its fuel threshold is
exact for the independently derived parent and child result. -/
theorem compileObject_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {rootBytes : List UInt8} {catalog : List AccountRuntime.CodeDefinition} {object : Contract.CompiledObject}
    {sourceCatalog : ChildFrameSemantics.Catalog} {initCatalog : ChildFrameSemantics.InitCatalog}
    {anchors : List CatalogWorldCorrespondence.Anchor} {height : Nat}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel (some rootBytes) catalog = .ok object)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported true)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (connection : RootChildCatalogExecutionCorrespondence.CatalogConnection ⟨program, code, rootBytes⟩ sourceCatalog catalog anchors)
    (initConnection : InitCatalogCorrespondence.InitCatalogConnection initCatalog (some rootBytes) catalog)
    (context : Contract.Context) (notDeploying : context.deploying = false)
    (initialLinks : InitialContextLinks (some rootBytes) catalog object context anchors)
    {finalSource : Semantics.State RuntimeCallEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code])
      (ChildFrameModeSemantics.effectsAt sourceCatalog initCatalog (height + 1) (some rootBytes))
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState (some rootBytes) object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value, PublicMessageRel context sourceResult finalSource.external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨value, _, executed, related⟩ :=
    compileObject_preserves selected accepted eligible connection initConnection context notDeploying initialLinks evaluated
  exact ⟨value, related, Contract.evaluation_resumes_exact executed⟩

end Solcore.Frontend.RustHull.ContractRootCallCorrespondence
end
