import Solcore.Frontend.RustHull.ChildFrameAllocationCorrespondence
import Solcore.Frontend.RustHull.ContractChildCallRuntimeFacts

/-! Child allocation also installs the concrete callback and call-depth cells.
The observations remain tied to the allocator and its current shared cells. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildFrameCorrespondence
open Core Correspondence ScalarExecution CodeBuilder

theorem allocateFrame_initializes_extra {depth : Nat} {environment : Environment} {initial : Store}
    {frame dispatcher creator gas code size known : Code} {shared : AccountRuntime.References}
    (parent : RuntimeCallEffectsSemantics.State) (request : AccountCallSemantics.Request)
    (sharedState : AccountCallSemantics.Shared) (bytes : List UInt8)
    {accounts : StorageCorrespondence.Accounts} (world : accounts.map Prod.fst = sharedState.world)
    {sharedCells : List InitializedCell}
    (references : RuntimeReferences depth environment shared sharedCells)
    (signature : sharedCells.map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse)
    (initialized : InitializedCells sharedCells initial) (separate : CellLocations sharedCells)
    (observed : ∀ cell ∈ sharedCells, Observed accounts (Initial parent request sharedState bytes) bytes cell)
    {creatorLocation : Nat} {creatorValue : Value}
    (creatorRelated : CodeValue depth environment creator
      (.cellRef (OptionalCell.cellType Creation.callbackType) creatorLocation))
    (creatorFound : initial.read? creatorLocation = some creatorValue)
    (creatorSeparate : ∀ cell ∈ sharedCells, cell.location ≠ creatorLocation)
    (frameRelated : CodeValue depth environment frame (CallTransportCorrespondence.requestValue request))
    (gasRelated : CodeValue depth environment gas (optionalWordValue (some request.gas)))
    (codeRelated : CodeValue depth environment code (WordMapping.encode (Memory.packBytes bytes)))
    (sizeRelated : CodeValue depth environment size (.word (Word.ofNatModulo bytes.length)))
    (knownRelated : CodeValue depth environment known (.bool true))
    (extraProperty : InitializedCell → Prop)
    (freshExtra : FrameInitializersValid depth environment initial frame dispatcher gas code size known shared extraProperty)
    (sharedExtra : ∀ cell ∈ sharedCells, extraProperty cell)
    (creatorExtra : extraProperty (ContractRuntimeEffectsCorrespondence.creatorCell creatorLocation creatorValue))
    (continuation : List Code → Code) (observes : Value → Store → Prop)
    (continued : ∀ extra suffix cells values,
      CodeValues (depth + extra.length) (extra ++ environment) values (cells.map InitializedCell.reference) →
      InitializedCells cells (initial ++ suffix) →
      cells.map (fun cell => (cell.name, cell.type)) = RuntimeExtendedInitializedEffects.slots true →
      CellLocations (sharedCells ++ [ContractRuntimeEffectsCorrespondence.creatorCell creatorLocation creatorValue] ++ cells) →
      (∀ cell ∈ cells, cell.location < initial.length → cell ∈ sharedCells ∨ cell.name = "createHandler") →
      (∀ cell ∈ cells, cell.name ∈ sharedSlotTypes.map Prod.fst → cell ∈ sharedCells) →
      (∀ cell ∈ cells, extraProperty cell) →
      Ready cells (initial ++ suffix) (Initial parent request sharedState bytes) bytes →
      ∃ value final, Core.Evaluates (extra ++ environment) (initial ++ suffix)
        (continuation values (depth + extra.length)) value final ∧ observes value final) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.allocateFrame (RuntimeExtendedInitializedEffects.slots true) shared
        frame dispatcher creator gas code size known continuation depth) value final ∧ observes value final := by
  let knownCells := sharedCells ++ [ContractRuntimeEffectsCorrespondence.creatorCell creatorLocation creatorValue]
  have names : shared.map Prod.fst = (sharedSlotTypes.map Prod.fst).reverse := by
    rw [references.names]
    have same := congrArg (List.map Prod.fst) signature
    simpa only [List.map_map, Function.comp_def, List.map_reverse] using same
  have fresh := fresh_observed (store := initial) (dispatcher := dispatcher)
    parent request sharedState bytes accounts names frameRelated gasRelated codeRelated sizeRelated knownRelated
  let property := fun cell => Observed accounts (Initial parent request sharedState bytes) bytes cell ∧
    (cell.location < initial.length → cell ∈ sharedCells ∨ cell.name = "createHandler") ∧
    (cell.name ∈ sharedSlotTypes.map Prod.fst → cell ∈ sharedCells) ∧ extraProperty cell
  have freshOrigin : FrameInitializersValid depth environment initial frame dispatcher gas code size known shared
      (fun cell => (cell.location < initial.length → cell ∈ sharedCells ∨ cell.name = "createHandler") ∧
        (cell.name ∈ sharedSlotTypes.map Prod.fst → cell ∈ sharedCells)) := by
    apply frameInitializers_valid frameRelated rfl gasRelated codeRelated sizeRelated knownRelated
    intro name type location value absent bound _
    exact ⟨fun before => False.elim (Nat.not_lt_of_ge bound before),
      fun member => False.elim (absent_shared_name names absent member)⟩
  have sharedReady : FrameSharedValid depth environment initial (RuntimeExtendedInitializedEffects.slots true) shared
      (fun cell => property cell ∧ cell ∈ knownCells) := by
    apply references.sharedValid initialized
    · intro slot member cell cellMember named
      apply sharedSlotTypes_compatible (sharedSlot := (cell.name, cell.type)) member _ named
      have present := List.mem_map_of_mem (f := fun cell : InitializedCell => (cell.name, cell.type)) cellMember
      rw [signature] at present
      exact List.mem_reverse.mp present
    · intro cell member
      exact ⟨⟨observed cell member, (fun _ => Or.inl member), fun _ => member, sharedExtra cell member⟩, List.mem_append_left _ member⟩
  have creatorReady : FrameCreatorValid depth environment initial (RuntimeExtendedInitializedEffects.slots true) creator
      (fun cell => property cell ∧ cell ∈ knownCells) := by
    intro type member
    have types : ∀ slot ∈ RuntimeExtendedInitializedEffects.slots true,
        slot.1 = "createHandler" → slot.2 = OptionalCell.cellType Creation.callbackType := by decide
    cases types ("createHandler", type) member rfl
    exact ⟨ContractRuntimeEffectsCorrespondence.creatorCell creatorLocation creatorValue,
      rfl, rfl, creatorRelated, creatorFound,
      ⟨creator_observed accounts _ bytes creatorLocation creatorValue, (fun _ => Or.inr rfl),
        by intro impossible; simp [ContractRuntimeEffectsCorrespondence.creatorCell, sharedSlotTypes, Ambient.slots] at impossible, creatorExtra⟩,
      List.mem_append_right _ (.head _)⟩
  have knownStored : InitializedCells knownCells initial := by
    intro cell member
    rcases List.mem_append.mp member with member | member
    · exact initialized cell member
    · have same : cell = ContractRuntimeEffectsCorrespondence.creatorCell creatorLocation creatorValue := by simpa using member
      subst cell
      exact creatorFound
  have knownSeparate : CellLocations knownCells := by
    intro left leftMember right rightMember same
    rcases List.mem_append.mp leftMember with leftMember | leftMember
    · rcases List.mem_append.mp rightMember with rightMember | rightMember
      · exact separate left leftMember right rightMember same
      · have equal : right = ContractRuntimeEffectsCorrespondence.creatorCell creatorLocation creatorValue := by simpa using rightMember
        subst right
        exact False.elim (creatorSeparate left leftMember same)
    · have equal : left = ContractRuntimeEffectsCorrespondence.creatorCell creatorLocation creatorValue := by simpa using leftMember
      subst left
      rcases List.mem_append.mp rightMember with rightMember | rightMember
      · exact False.elim (creatorSeparate right rightMember same.symm)
      · have equal : right = ContractRuntimeEffectsCorrespondence.creatorCell creatorLocation creatorValue := by simpa using rightMember
        subst right
        rfl
  have extra : FrameInitializersValid depth environment initial frame dispatcher gas code size known shared
      (fun cell => (cell.location < initial.length → cell ∈ sharedCells ∨ cell.name = "createHandler") ∧
        (cell.name ∈ sharedSlotTypes.map Prod.fst → cell ∈ sharedCells) ∧ extraProperty cell) := by
    intro more suffix name type absent
    obtain ⟨value, evaluated, origin⟩ := freshOrigin more suffix name type absent
    obtain ⟨other, otherEvaluated, additional⟩ := freshExtra more suffix name type absent
    have same := (Core.evaluation_deterministic evaluated otherEvaluated).1
    subst other
    exact ⟨value, evaluated, origin.1, origin.2, additional⟩
  obtain ⟨extra, suffix, values, cells, related, stored, signature', valid, locations, evaluates⟩ :=
    allocateFrameSlots_separates (ContractRuntimeEffectsCorrespondence.FrameInitializersValid.and fresh extra) sharedReady creatorReady (previous := []) (previousCells := [])
      .nil (by intro cell member; cases member) (by intro cell member; cases member) knownStored
      (by simpa only [List.append_nil] using knownSeparate)
  simp only [List.reverse_nil, List.nil_append, List.append_nil] at related stored valid locations
  obtain ⟨ready⟩ := initialized_ready parent request sharedState bytes world signature' stored
    (locations.subset (fun _ member => List.mem_append_right _ member)) (fun cell member => (valid cell member).1)
  obtain ⟨value, final, evaluated, result⟩ := continued extra suffix cells values related stored signature' locations (fun cell member => (valid cell member).2.1) (fun cell member => (valid cell member).2.2.1) (fun cell member => (valid cell member).2.2.2) ready
  exact ⟨value, final, evaluates continuation value final evaluated, result⟩


private def callMutableSlots (layout : RuntimeCallEffectsCorrespondence.Layout) : List EffectSlot :=
  [⟨"balances", WordMapping.type, layout.balances⟩,
   ⟨"returnData", WordMapping.type, layout.returnData⟩,
   ⟨"returnDataSize", .word, layout.returnDataSize⟩,
   ⟨"logs", WordMapping.type, layout.logs⟩,
   ⟨"logSize", .word, layout.logSize⟩,
   ⟨"memory", WordMapping.type, layout.memory⟩,
   ⟨"memorySize", .word, layout.storage.memorySize⟩,
   ⟨"world", AccountState.type, layout.storage.world⟩,
   ⟨"exit", .word, layout.storage.exit⟩,
   ⟨"returnOffset", .word, layout.storage.returnOffset⟩,
   ⟨"returnSize", .word, layout.storage.returnSize⟩]

/-- Separation suffices even when allocation is entered from another child. -/
theorem creator_outside_separate {layout : RuntimeCallEffectsCorrespondence.Layout}
    {shared cells : List InitializedCell} {creator boundary : Nat}
    (before : creator < boundary) (separate : ∀ cell ∈ shared, cell.location ≠ creator)
    (origin : ∀ cell ∈ cells, ChildCallbackContextCorrespondence.Origin shared boundary cell)
    (members : ∀ slot ∈ RuntimeCallInitializedEffects.baseSlots layout.toReturnDataLayout,
      slot ∈ cells.map InitializedCell.effectSlot) :
    creator ∉ RuntimeCallEffectsCorrespondence.mutable layout := by
  have included : ∀ slot ∈ callMutableSlots layout, slot ∈ cells.map InitializedCell.effectSlot := by
    intro slot member
    apply members slot
    simp only [callMutableSlots, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [RuntimeCallInitializedEffects.baseSlots]
  intro inside
  change creator ∈ (callMutableSlots layout).map EffectSlot.location at inside
  obtain ⟨slot, slotMember, same⟩ := List.mem_map.mp inside
  obtain ⟨cell, cellMember, equal⟩ := List.mem_map.mp (included slot slotMember)
  have location : cell.location = creator := (congrArg EffectSlot.location equal).trans same
  rcases (origin cell cellMember).2 (location ▸ before) with member | named
  · exact separate cell member location
  · have names := List.mem_map_of_mem (f := EffectSlot.name) slotMember
    have slotName : slot.name = "createHandler" := (congrArg EffectSlot.name equal).symm.trans named
    simp [callMutableSlots, slotName] at names

structure CallAllocationReady (sharedCells cells : List InitializedCell) (store : Store)
    (parent : RuntimeCallEffectsSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8)
    (dispatcher creator : Nat) (dispatchValue : Value) where
  base : Ready cells store (Initial parent request shared bytes) bytes
  call : RuntimeCallInitializedEffects.Ready base.layout cells store request.depth request.target dispatcher
  inventory : ChildCallbackContextCorrespondence.Inventory call.layout sharedCells creator
  sharedMembers : ∀ cell ∈ sharedCells, cell.effectSlot ∈ cells.map InitializedCell.effectSlot
  captured : (ChildCallbackContextCorrespondence.context inventory).valid (prefixRead call.layout.boundary store)
  callPassive : RuntimeCallEffectsCorrespondence.CallPassive call.layout (cells.map InitializedCell.effectSlot)
  dispatcherOutside : ∀ cell ∈ cells, cell.location ≠ dispatcher
  dispatcherRead : store.read? dispatcher = some (.inRight .unit dispatchValue)

/-- The child handler captures its own address while reusing the object's
actual dispatcher closure and the same current shared locations. -/
def CallAllocationReady.handlers {sharedCells cells : List InitializedCell} {store : Store}
    {parent : RuntimeCallEffectsSemantics.State} {request : AccountCallSemantics.Request}
    {shared : AccountCallSemantics.Shared} {bytes : List UInt8}
    {dispatcher creator : Nat} {dispatchValue : Value}
    (ready : CallAllocationReady sharedCells cells store parent request shared bytes dispatcher creator dispatchValue)
    (dispatch : AccountCallCorrespondence.DispatcherClosure
      (RuntimeCallEffectsCorrespondence.sharedLocations ready.call.layout) dispatchValue) :
    RuntimeCallEffectsCorrespondence.Handlers ready.call.layout where
  source := request.target
  dispatchValue := dispatchValue
  handlerValue := ready.call.handlerValue
  dispatch := dispatch
  handler := by simpa only [ready.call.dispatcherEqual] using ready.call.handler

theorem CallAllocationReady.related {sharedCells cells : List InitializedCell} {store : Store}
    {parent : RuntimeCallEffectsSemantics.State} {request : AccountCallSemantics.Request}
    {shared : AccountCallSemantics.Shared} {bytes : List UInt8}
    {dispatcher creator : Nat} {dispatchValue : Value}
    (ready : CallAllocationReady sharedCells cells store parent request shared bytes dispatcher creator dispatchValue)
    (dispatch : AccountCallCorrespondence.DispatcherClosure
      (RuntimeCallEffectsCorrespondence.sharedLocations ready.call.layout) dispatchValue) :
    StateRel (RuntimeCallEffectsCorrespondence.model ready.call.layout
      (prefixRead ready.call.layout.boundary store) (cells.map InitializedCell.effectSlot)
      (some bytes) (ready.handlers dispatch)) [] ⟨[], ChildFrameSemantics.initial parent request shared bytes⟩ store := by
  apply RuntimeCallEffectsCorrespondence.initial_state
  · simpa only [ready.call.baseEqual] using ready.base.related
  · exact ready.call.depthRead
  · simpa only [ready.call.dispatcherEqual, CallAllocationReady.handlers] using ready.dispatcherRead
  · exact ready.call.handlerRead
  · rfl

/-- Actual fresh initialization supplies a callable child frame, including its
captured source address, depth, current shared inventory and retained dispatcher. -/
theorem allocateCallFrame_initializes {depth : Nat} {environment : Environment} {initial : Store}
    {frame dispatcher creator gas code size known : Code} {shared : AccountRuntime.References}
    (parent : RuntimeCallEffectsSemantics.State) (request : AccountCallSemantics.Request)
    (sharedState : AccountCallSemantics.Shared) (bytes : List UInt8)
    {accounts : StorageCorrespondence.Accounts} (world : accounts.map Prod.fst = sharedState.world)
    {sharedCells : List InitializedCell}
    (references : RuntimeReferences depth environment shared sharedCells)
    (signature : sharedCells.map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse)
    (initialized : InitializedCells sharedCells initial) (separate : CellLocations sharedCells)
    (observed : ∀ cell ∈ sharedCells, Observed accounts (Initial parent request sharedState bytes) bytes cell)
    {creatorLocation : Nat} {creatorValue : Value}
    (creatorRelated : CodeValue depth environment creator
      (.cellRef (OptionalCell.cellType Creation.callbackType) creatorLocation))
    (creatorFound : initial.read? creatorLocation = some creatorValue)
    (creatorSeparate : ∀ cell ∈ sharedCells, cell.location ≠ creatorLocation)
    {dispatcherLocation : Nat} {dispatchValue : Value}
    (dispatcherRelated : CodeValue depth environment dispatcher
      (.cellRef (OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation))
    (dispatcherFound : initial.read? dispatcherLocation = some (.inRight .unit dispatchValue))
    (dispatcherSeparate : ∀ cell ∈ sharedCells, cell.location ≠ dispatcherLocation)
    (creatorDispatcher : creatorLocation ≠ dispatcherLocation)
    (frameRelated : CodeValue depth environment frame (CallTransportCorrespondence.requestValue request))
    (gasRelated : CodeValue depth environment gas (optionalWordValue (some request.gas)))
    (codeRelated : CodeValue depth environment code (WordMapping.encode (Memory.packBytes bytes)))
    (sizeRelated : CodeValue depth environment size (.word (Word.ofNatModulo bytes.length)))
    (knownRelated : CodeValue depth environment known (.bool true))
    (continuation : List Code → Code) (observes : Value → Store → Prop)
    (continued : ∀ extra suffix cells values,
      CodeValues (depth + extra.length) (extra ++ environment) values (cells.map InitializedCell.reference) →
      InitializedCells cells (initial ++ suffix) →
      cells.map (fun cell => (cell.name, cell.type)) = RuntimeExtendedInitializedEffects.slots true →
      CellLocations (sharedCells ++ [ContractRuntimeEffectsCorrespondence.creatorCell creatorLocation creatorValue] ++ cells) →
      (∀ cell ∈ cells, cell.location < initial.length → cell ∈ sharedCells ∨ cell.name = "createHandler") →
      (∀ cell ∈ cells, cell.name ∈ sharedSlotTypes.map Prod.fst → cell ∈ sharedCells) →
      CallAllocationReady sharedCells cells (initial ++ suffix) parent request sharedState bytes
        dispatcherLocation creatorLocation dispatchValue →
      ∃ value final, Core.Evaluates (extra ++ environment) (initial ++ suffix)
        (continuation values (depth + extra.length)) value final ∧ observes value final) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.allocateFrame (RuntimeExtendedInitializedEffects.slots true) shared
        frame dispatcher creator gas code size known continuation depth) value final ∧ observes value final := by
  have dispatcherBelow := (List.getElem?_eq_some_iff.mp dispatcherFound).1
  have creatorBelow := (List.getElem?_eq_some_iff.mp creatorFound).1
  let property := fun cell => ContractCallCorrespondence.initializedDepth request.depth cell ∧
    ContractCallCorrespondence.initializedHandler request.target dispatcherLocation cell ∧ cell.location ≠ dispatcherLocation
  have fresh : FrameInitializersValid depth environment initial frame dispatcher gas code size known shared property :=
    ContractRuntimeEffectsCorrespondence.FrameInitializersValid.and
      (ContractCallCorrespondence.fresh_depth_observation frameRelated rfl rfl gasRelated codeRelated sizeRelated knownRelated)
      (ContractRuntimeEffectsCorrespondence.FrameInitializersValid.and
        (ContractCallCorrespondence.fresh_handler_observation frameRelated rfl rfl dispatcherRelated gasRelated codeRelated sizeRelated knownRelated)
        (ContractCallCorrespondence.fresh_dispatcher_separate dispatcherBelow frameRelated rfl gasRelated codeRelated sizeRelated knownRelated))
  have sharedExtra : ∀ cell ∈ sharedCells, property cell := by
    intro cell member
    have present := List.mem_map_of_mem (f := fun cell : InitializedCell => (cell.name, cell.type)) member
    rw [signature] at present
    have typed := List.mem_reverse.mp present
    have names := List.mem_map_of_mem (f := Prod.fst) typed
    refine ⟨?_, ?_, dispatcherSeparate cell member⟩
    · intro named
      simp [named, sharedSlotTypes, Ambient.slots] at names
    · intro named
      simp [named, sharedSlotTypes, Ambient.slots] at names
  have creatorExtra : property (ContractRuntimeEffectsCorrespondence.creatorCell creatorLocation creatorValue) :=
    ⟨ContractCallCorrespondence.creator_depth_observation _ _ _,
      ContractCallCorrespondence.creator_handler_observation _ _ _ _, creatorDispatcher⟩
  apply allocateFrame_initializes_extra parent request sharedState bytes world references signature initialized separate
    observed creatorRelated creatorFound creatorSeparate frameRelated gasRelated codeRelated sizeRelated knownRelated
    property fresh sharedExtra creatorExtra continuation observes
  intro extra suffix cells values valuesRelated stored fullSignature locations origins sharedOrigins additional base
  have cellSeparate : CellLocations cells := locations.subset (fun _ member => List.mem_append_right _ member)
  obtain ⟨call⟩ := RuntimeCallInitializedEffects.ready fullSignature stored cellSeparate base.boundary base.members
    (by rw [base.boundary]; exact Nat.lt_of_lt_of_le dispatcherBelow (by simp))
    (fun cell member => (additional cell member).2.2)
    (fun cell member => (additional cell member).1)
    (fun cell member => (additional cell member).2.1)
  have boundary : call.layout.boundary = (initial ++ suffix).length := by
    change call.layout.toReturnDataLayout.boundary = _
    rw [call.baseEqual]
    exact base.boundary
  have baseMembers : ∀ slot ∈ RuntimeCallInitializedEffects.baseSlots call.layout.toReturnDataLayout,
      slot ∈ cells.map InitializedCell.effectSlot := by
    rw [call.baseEqual]
    exact base.members
  have origin : ∀ cell ∈ cells, ChildCallbackContextCorrespondence.Origin sharedCells initial.length cell :=
    fun cell member => ⟨sharedOrigins cell member, origins cell member⟩
  have included := ChildCallbackContextCorrespondence.shared_included signature fullSignature origin
  have sharedLocations : ContractCallCorrespondence.SharedCells sharedCells
      (RuntimeCallEffectsCorrespondence.sharedLocations call.layout) :=
    RuntimeCallInitializedEffects.shared_cells baseMembers (fun cell member named => sharedOrigins cell member (by
      simp only [ContractCallCorrespondence.dispatchSharedNames, List.mem_cons, List.not_mem_nil, or_false] at named
      rcases named with named | named | named | named | named
      all_goals simp [named, sharedSlotTypes]))
  let inventory : ChildCallbackContextCorrespondence.Inventory call.layout sharedCells creatorLocation := {
    signature := signature
    shared := sharedLocations
    separate := separate
    below := fun cell member => by rw [boundary]; exact stored.location_bound (included cell member)
    creatorBelow := by rw [boundary]; exact Nat.lt_of_lt_of_le creatorBelow (by simp)
    creatorSeparate := creatorSeparate
    ambientOutside := ChildCallbackContextCorrespondence.ambient_outside included cellSeparate baseMembers
    creatorOutside := creator_outside_separate creatorBelow creatorSeparate origin baseMembers }
  have unique : (cells.map InitializedCell.name).Nodup := by
    have names := congrArg (List.map Prod.fst) fullSignature
    simp only [List.map_map, Function.comp_def] at names
    rw [names]
    decide
  have codeMembers : ∀ imageCells, call.layout.codeCells = some imageCells →
      ⟨"code", WordMapping.type, imageCells.code⟩ ∈ cells.map InitializedCell.effectSlot ∧
      ⟨"codeKnown", .bool, imageCells.known⟩ ∈ cells.map InitializedCell.effectSlot := by
    change ∀ imageCells, call.layout.toReturnDataLayout.codeCells = some imageCells → _
    rw [call.baseEqual]
    exact base.codes
  apply continued extra suffix cells values valuesRelated stored fullSignature locations origins sharedOrigins
  exact {
    base := base
    call := call
    inventory := inventory
    sharedMembers := fun cell member => List.mem_map_of_mem (included cell member)
    captured := ContractChildCallCorrespondence.initialized_context inventory initialized ⟨creatorValue, creatorFound⟩
      (StoreRetains.append initial suffix)
    callPassive := RuntimeCallInitializedEffects.call_passive unique cellSeparate baseMembers codeMembers
    dispatcherOutside := fun cell member => (additional cell member).2.2
    dispatcherRead := ((StoreRetains.append initial suffix).read dispatcherLocation dispatcherBelow).trans dispatcherFound }

end Solcore.Frontend.RustHull.ChildFrameCorrespondence
