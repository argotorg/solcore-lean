import Solcore.Frontend.RustHull.Internal.ChildFrames
import Solcore.Frontend.RustHull.Internal.RuntimeObjects
import Solcore.Frontend.RustHull.Internal.CallStates
import Solcore.Frontend.RustHull.Semantics.Frames
import Solcore.Frontend.RustHull.Internal.LinkedWorld
import Solcore.Frontend.RustHull.Internal.CallLayout
import Solcore.Frontend.RustHull.Internal.Derivations
import Solcore.Frontend.RustHull.Internal.Creation
import Solcore.Frontend.RustHull.Internal.AccountCalls
import Solcore.Frontend.RustHull.Internal.CallEffects

/-!
# Child frames with nested calls

Finite call trees: nested children, call modes and root reentry, with their catalog links.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.ChildFrameCallAllocationCorrespondence
/-! Child allocation also installs the concrete callback and call-depth cells.
The observations remain tied to the allocator and its current shared cells. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildFrameCorrespondence
open Core Correspondence ScalarExecution CodeBuilder

/-- The allocation also identifies the frame's create-handler cell as the
installed creator cell. -/
theorem allocateFrame_initializes_creator {depth : Nat} {environment : Environment} {initial : Store}
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
      (∀ cell ∈ cells, cell.name = "createHandler" →
        cell = ContractRuntimeEffectsCorrespondence.creatorCell creatorLocation creatorValue) →
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
  obtain ⟨extra, suffix, values, cells, related, stored, signature', valid, locations, creators, evaluates⟩ :=
    allocateFrameSlots_creates (ContractRuntimeEffectsCorrespondence.FrameInitializersValid.and fresh extra) sharedReady creatorReady (previous := []) (previousCells := [])
      .nil (by intro cell member; cases member) (by intro cell member; cases member) knownStored
      (by simpa only [List.append_nil] using knownSeparate)
  simp only [List.reverse_nil, List.nil_append, List.append_nil] at related stored valid locations
  obtain ⟨ready⟩ := initialized_ready parent request sharedState bytes world signature' stored
    (locations.subset (fun _ member => List.mem_append_right _ member)) (fun cell member => (valid cell member).1)
  have creatorCells : ∀ cell ∈ cells, cell.name = "createHandler" →
      cell = ContractRuntimeEffectsCorrespondence.creatorCell creatorLocation creatorValue := by
    intro cell member named
    rcases List.mem_append.mp (creators cell member named) with sharedMember | creatorMember
    · have present := List.mem_map_of_mem (f := fun cell : InitializedCell => (cell.name, cell.type)) sharedMember
      rw [signature] at present
      have names := List.mem_map_of_mem (f := Prod.fst) (List.mem_reverse.mp present)
      change cell.name ∈ sharedSlotTypes.map Prod.fst at names
      rw [named] at names
      simp [sharedSlotTypes, Ambient.slots] at names
    · simpa using creatorMember
  obtain ⟨value, final, evaluated, result⟩ := continued extra suffix cells values related stored signature' locations (fun cell member => (valid cell member).2.1) (fun cell member => (valid cell member).2.2.1) (fun cell member => (valid cell member).2.2.2) creatorCells ready
  exact ⟨value, final, evaluates continuation value final evaluated, result⟩


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
  apply allocateFrame_initializes_creator parent request sharedState bytes world references signature initialized separate
    observed creatorRelated creatorFound creatorSeparate frameRelated gasRelated codeRelated sizeRelated knownRelated
    extraProperty freshExtra sharedExtra creatorExtra continuation observes
  intro extra suffix cells values related stored cellSignature locations origins sharedOrigins additional _ ready
  exact continued extra suffix cells values related stored cellSignature locations origins sharedOrigins additional ready

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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.NestedChildCallbackContextCorrespondence
/-! Nested children retain the actual dispatcher cell as well as the shared
ambient and creator references. Refreshing a capture changes its store witness
and shared values, while retaining the same compiled closure and code references. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.NestedChildCallbackContextCorrespondence
open Core Correspondence ScalarExecution
open RuntimeCallEffectsCorrespondence (Layout)

structure Inventory (layout : Layout) (cells : List InitializedCell) (creator : Nat) : Prop
    extends base : ChildCallbackContextCorrespondence.Inventory layout cells creator where
  dispatcherSeparate : ∀ cell ∈ cells, cell.location ≠ layout.dispatcher
  creatorDispatcher : creator ≠ layout.dispatcher

def context {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    (inventory : Inventory layout cells creator) (dispatcher : Value) :
    RuntimeChildCallEffectsCorrespondence.Context layout where
  valid read := (ChildCallbackContextCorrespondence.context inventory.base).valid read ∧
    read layout.dispatcher = some (.inRight .unit dispatcher)
  frame := by
    intro before after retained valid
    refine ⟨(ChildCallbackContextCorrespondence.context inventory.base).frame retained valid.1, ?_⟩
    rw [retained _ (RuntimeCallEffectsCorrespondence.call_separation layout _ (by simp))]
    exact valid.2

theorem initial {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    (inventory : Inventory layout cells creator) {store : Store} {dispatcher : Value}
    (captured : (ChildCallbackContextCorrespondence.context inventory.base).valid (prefixRead layout.boundary store))
    (found : store.read? layout.dispatcher = some (.inRight .unit dispatcher)) :
    (context inventory dispatcher).valid (prefixRead layout.boundary store) := by
  refine ⟨captured, ?_⟩
  simpa only [prefixRead, layout.dispatcherBelow, ↓reduceIte] using found

theorem dispatcher_read {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    {inventory : Inventory layout cells creator} {store : Store} {dispatcher : Value}
    (valid : (context inventory dispatcher).valid (prefixRead layout.boundary store)) :
    store.read? layout.dispatcher = some (.inRight .unit dispatcher) := by
  simpa only [prefixRead, layout.dispatcherBelow, ↓reduceIte] using valid.2

def refreshCapture {slots : List (String × Core.Ty)} {count : Nat}
    {images : List (Nat × List UInt8)} {catalog : List AccountRuntime.CodeDefinition}
    {functions : List Value} {cells : List InitializedCell} {dispatcher creator : Nat} {initial : Store}
    (capture : ObjectCallbackCapture slots count images catalog functions cells dispatcher creator initial)
    (store : Store) (found : store.read? dispatcher = some (.inRight .unit capture.closure)) :
    ObjectCallbackCapture slots count images catalog functions (ChildFrameCorrespondence.refresh store cells)
      dispatcher creator store where
  depth := capture.depth
  environment := capture.environment
  functions := capture.functions
  shared := capture.shared
  dispatcher := capture.dispatcher
  creator := capture.creator
  functionValues := capture.functionValues
  names := by
    simpa only [ChildFrameCorrespondence.refresh, List.map_map, Function.comp_def,
      ChildFrameCorrespondence.refreshCell] using capture.names
  references := ChildFrameCorrespondence.refresh_references capture.references store
  dispatcherValue := capture.dispatcherValue
  creatorValue := capture.creatorValue
  closure := capture.closure
  captured := capture.captured
  stored := found

def withDispatcher {slots : List (String × Core.Ty)} {count : Nat}
    {images : List (Nat × List UInt8)} {catalog : List AccountRuntime.CodeDefinition}
    {functions : List Value} {cells : List InitializedCell} {dispatcher creator : Nat} {store : Store}
    (capture : ObjectCallbackCapture slots count images catalog functions cells dispatcher creator store)
    (location : Nat) (same : location = dispatcher) :
    ObjectCallbackCapture slots count images catalog functions cells location creator store where
  depth := capture.depth
  environment := capture.environment
  functions := capture.functions
  shared := capture.shared
  dispatcher := capture.dispatcher
  creator := capture.creator
  functionValues := capture.functionValues
  names := capture.names
  references := capture.references
  dispatcherValue := by simpa only [same] using capture.dispatcherValue
  creatorValue := capture.creatorValue
  closure := capture.closure
  captured := capture.captured
  stored := by simpa only [same] using capture.stored

end Solcore.Frontend.RustHull.NestedChildCallbackContextCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ChildFrameCallStateFrameCorrespondence
/-! A callable child preserves its parent's local cells. Its final shared
resources include changes made by nested calls and retain exact catalog links. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildFrameCorrespondence
open Core Correspondence ScalarExecution

/-- The same concrete inventory also records dispatcher separation for the
next child allocation. -/
theorem CallAllocationReady.nestedInventory {sharedCells cells : List InitializedCell} {store : Store}
    {parent : RuntimeCallEffectsSemantics.State} {request : AccountCallSemantics.Request}
    {shared : AccountCallSemantics.Shared} {bytes : List UInt8}
    {dispatcher creator : Nat} {dispatchValue : Value}
    (ready : CallAllocationReady sharedCells cells store parent request shared bytes dispatcher creator dispatchValue)
    (dispatcherSeparate : ∀ cell ∈ sharedCells, cell.location ≠ dispatcher)
    (creatorDispatcher : creator ≠ dispatcher) :
    NestedChildCallbackContextCorrespondence.Inventory ready.call.layout sharedCells creator where
  base := ready.inventory
  dispatcherSeparate := by simpa only [ready.call.dispatcherEqual] using dispatcherSeparate
  creatorDispatcher := by simpa only [ready.call.dispatcherEqual] using creatorDispatcher

theorem CallAllocationReady.nestedCaptured {sharedCells cells : List InitializedCell} {store : Store}
    {parent : RuntimeCallEffectsSemantics.State} {request : AccountCallSemantics.Request}
    {shared : AccountCallSemantics.Shared} {bytes : List UInt8}
    {dispatcher creator : Nat} {dispatchValue : Value}
    (ready : CallAllocationReady sharedCells cells store parent request shared bytes dispatcher creator dispatchValue)
    (dispatcherSeparate : ∀ cell ∈ sharedCells, cell.location ≠ dispatcher)
    (creatorDispatcher : creator ≠ dispatcher) :
    (NestedChildCallbackContextCorrespondence.context
      (ready.nestedInventory dispatcherSeparate creatorDispatcher) dispatchValue).valid
      (prefixRead ready.call.layout.boundary store) := by
  apply NestedChildCallbackContextCorrespondence.initial _ ready.captured
  simpa only [ready.call.dispatcherEqual] using ready.dispatcherRead

/-- Below the initial child boundary, balances and the old mutable cells are
all shared. Fresh child memory, return data and termination cells stay local. -/
theorem CallAllocationReady.mutable_early_shared {sharedCells cells : List InitializedCell}
    {initial allocated : Store} {parent : RuntimeCallEffectsSemantics.State}
    {request : AccountCallSemantics.Request} {shared : AccountCallSemantics.Shared} {bytes : List UInt8}
    {dispatcher creator : Nat} {dispatchValue : Value}
    (ready : CallAllocationReady sharedCells cells allocated parent request shared bytes dispatcher creator dispatchValue)
    (origins : ∀ cell ∈ cells, cell.location < initial.length → cell ∈ sharedCells ∨ cell.name = "createHandler")
    {location : Nat} (below : location < initial.length)
    (member : location ∈ RuntimeCallEffectsCorrespondence.mutable ready.call.layout) :
    location ∈ (RuntimeCallEffectsCorrespondence.sharedLocations ready.call.layout).mutable := by
  change location ∈ ready.call.layout.balances :: mutable ready.call.layout.toReturnDataLayout at member
  rcases List.mem_cons.mp member with same | member
  · simp [same, RuntimeCallEffectsCorrespondence.sharedLocations, AccountCallCorrespondence.SharedLocations.mutable]
  · have present : location ∈ mutable ready.base.layout := by
      simpa only [ready.call.baseEqual] using member
    have shared := ChildFrameCorrespondence.mutable_early_shared ready.base ready.inventory.signature origins below present
    change location ∈ (sharedLocations ready.call.layout.toReturnDataLayout).mutable
    simpa only [ready.call.baseEqual] using shared

/-- Calls made by the child may update balances; all older nonshared reads
still agree with the store from before the child frame was allocated. -/
theorem CallAllocationReady.parent_frame {sharedCells cells : List InitializedCell}
    {initial suffix final : Store} {parent : RuntimeCallEffectsSemantics.State}
    {request : AccountCallSemantics.Request} {shared : AccountCallSemantics.Shared} {bytes : List UInt8}
    {dispatcher creator : Nat} {dispatchValue : Value}
    (ready : CallAllocationReady sharedCells cells (initial ++ suffix) parent request shared bytes dispatcher creator dispatchValue)
    (origins : ∀ cell ∈ cells, cell.location < initial.length → cell ∈ sharedCells ∨ cell.name = "createHandler")
    {handlers : RuntimeCallEffectsCorrespondence.Handlers ready.call.layout}
    {anchors : RuntimeChildCallEffectsCorrespondence.Anchors}
    {context : RuntimeChildCallEffectsCorrespondence.Context ready.call.layout}
    {world : World} {next : Semantics.State RuntimeCallEffectsSemantics.State}
    (related : StateRel (RuntimeChildCallEffectsCorrespondence.model ready.call.layout
      (prefixRead ready.call.layout.boundary (initial ++ suffix)) (cells.map InitializedCell.effectSlot)
      (some bytes) handlers anchors context) world next final) :
    AccountCallCorrespondence.SharedFrame (RuntimeCallEffectsCorrespondence.sharedLocations ready.call.layout) initial final := by
  have boundary : ready.call.layout.boundary = (initial ++ suffix).length := by
    change ready.call.layout.toReturnDataLayout.boundary = _
    rw [ready.call.baseEqual]
    exact ready.base.boundary
  have base := RuntimeChildCallEffectsCorrespondence.base_related related
  refine ⟨?_, ?_⟩
  · have bounded := base.external.1
    rw [boundary] at bounded
    exact Nat.le_trans (by simp) bounded
  · intro location value outside found
    have below : location < initial.length := (List.getElem?_eq_some_iff.mp found).1
    have beforeBoundary : location < ready.call.layout.boundary := by
      rw [boundary]
      exact Nat.lt_of_lt_of_le below (by simp)
    have preserved := RuntimeCallEffectsCorrespondence.other_related base
      (fun member => outside (ready.mutable_early_shared origins below member))
    have same : final.read? location = initial.read? location := by
      simpa only [prefixRead, beforeBoundary, ↓reduceIte, Core.Store.read?, List.getElem?_append_left below] using preserved
    exact same.trans found

theorem CallAllocationReady.shared_state {sharedCells cells : List InitializedCell} {initial final : Store}
    {parent : RuntimeCallEffectsSemantics.State} {request : AccountCallSemantics.Request}
    {shared : AccountCallSemantics.Shared} {bytes : List UInt8}
    {dispatcher creator : Nat} {dispatchValue : Value}
    (ready : CallAllocationReady sharedCells cells initial parent request shared bytes dispatcher creator dispatchValue)
    {handlers : RuntimeCallEffectsCorrespondence.Handlers ready.call.layout}
    {anchors : RuntimeChildCallEffectsCorrespondence.Anchors}
    {context : RuntimeChildCallEffectsCorrespondence.Context ready.call.layout}
    {world : World} {next : Semantics.State RuntimeCallEffectsSemantics.State}
    (related : StateRel (RuntimeChildCallEffectsCorrespondence.model ready.call.layout
      (prefixRead ready.call.layout.boundary initial) (cells.map InitializedCell.effectSlot)
      (some bytes) handlers anchors context) world next final) :
    AccountCallCorrespondence.SharedStateRel (RuntimeCallEffectsCorrespondence.sharedLocations ready.call.layout)
      (RuntimeCallEffectsSemantics.shared next.external) final :=
  RuntimeCallEffectsCorrespondence.shared_related (RuntimeChildCallEffectsCorrespondence.base_related related)

theorem CallAllocationReady.linked_shared_state {sharedCells cells : List InitializedCell} {initial final : Store}
    {parent : RuntimeCallEffectsSemantics.State} {request : AccountCallSemantics.Request}
    {shared : AccountCallSemantics.Shared} {bytes : List UInt8}
    {dispatcher creator : Nat} {dispatchValue : Value}
    (ready : CallAllocationReady sharedCells cells initial parent request shared bytes dispatcher creator dispatchValue)
    {handlers : RuntimeCallEffectsCorrespondence.Handlers ready.call.layout}
    {anchors : RuntimeChildCallEffectsCorrespondence.Anchors}
    {context : RuntimeChildCallEffectsCorrespondence.Context ready.call.layout}
    {world : World} {next : Semantics.State RuntimeCallEffectsSemantics.State}
    (related : StateRel (RuntimeChildCallEffectsCorrespondence.model ready.call.layout
      (prefixRead ready.call.layout.boundary initial) (cells.map InitializedCell.effectSlot)
      (some bytes) handlers anchors context) world next final) :
    AccountCallCorrespondence.LinkedSharedStateRel anchors (RuntimeCallEffectsCorrespondence.sharedLocations ready.call.layout)
      (RuntimeCallEffectsSemantics.shared next.external) final :=
  ⟨ready.shared_state related, RuntimeChildCallEffectsCorrespondence.linked_related related⟩

end Solcore.Frontend.RustHull.ChildFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ChildFrameCallModeAllocationCorrespondence
/-! Fresh frame allocation captures the execution address in every call-mode
handler. Their concrete cells remain outside the mutable frame resources. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildFrameModeCorrespondence
open Core Correspondence ScalarExecution CodeBuilder ChildFrameCorrespondence
open RuntimeCallModeEffectsCorrespondence (ExtraHandler ModeHandlers CreateHandler)

def handlerName : AccountCallSemantics.Mode → String
  | .ordinary => "callHandler"
  | .callCode => "callCodeHandler"
  | .delegateCall => "delegateCallHandler"

def initializedHandler (mode : AccountCallSemantics.Mode) (source : Word)
    (dispatcherLocation : Nat) (cell : InitializedCell) : Prop :=
  cell.name = handlerName mode → ∃ value, cell.value = .inRight .unit value ∧
    Nonempty (AccountCallModeCorrespondence.CallHandlerClosure mode source dispatcherLocation value)

theorem fresh_handler_observation (mode : AccountCallSemantics.Mode)
    {depth : Nat} {environment : Environment} {store : Store}
    {frame dispatcher gas code codeSize codeKnown : Code} {shared : AccountRuntime.References}
    {values : List Value} {gasValue codeValue sizeValue knownValue : Value}
    {source : Word} {dispatcherLocation : Nat}
    (frameRelated : CodeValue depth environment frame (bundleValues values)) (length : values.length = 8)
    (address : values[0]? = some (.word source))
    (dispatcherRelated : CodeValue depth environment dispatcher
      (.cellRef (OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation))
    (gasRelated : CodeValue depth environment gas gasValue)
    (codeRelated : CodeValue depth environment code codeValue)
    (sizeRelated : CodeValue depth environment codeSize sizeValue)
    (knownRelated : CodeValue depth environment codeKnown knownValue) :
    FrameInitializersValid depth environment store frame dispatcher gas code codeSize codeKnown shared
      (initializedHandler mode source dispatcherLocation) := by
  intro extra suffix name type _
  by_cases named : name = handlerName mode
  · subst name
    have lambda : LambdaCode (AccountRuntime.frameCallHandler mode.number frame dispatcher) := by
      intro here
      exact ⟨_, _, _, rfl⟩
    obtain ⟨value, captured⟩ := lambda.captures (depth + extra.length) (extra ++ environment)
    refine ⟨.inRight .unit value, ?_, fun _ => ⟨value, rfl, ⟨{
      depth := depth + extra.length
      captured := extra ++ environment
      frame := frame
      dispatcher := dispatcher
      closure := captured
      address := ?_
      dispatcherReference := dispatcherRelated.prepend extra }⟩⟩⟩
    · cases mode <;> exact .inRight (captured.evaluates (store ++ suffix))
    · simpa only [length] using (frameRelated.part address).prepend extra
  · obtain ⟨value, evaluated⟩ := frameInitializers_ready frameRelated length gasRelated codeRelated sizeRelated knownRelated
      extra name (store ++ suffix)
    exact ⟨value, evaluated, fun impossible => False.elim (named impossible)⟩

theorem shared_handler_observation (mode : AccountCallSemantics.Mode)
    {cells : List InitializedCell}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse)
    (source : Word) (dispatcher : Nat) :
    ∀ cell ∈ cells, initializedHandler mode source dispatcher cell := by
  intro cell member named
  have present := List.mem_map_of_mem (f := fun cell : InitializedCell => (cell.name, cell.type)) member
  rw [signature] at present
  have names := List.mem_map_of_mem (f := Prod.fst) (List.mem_reverse.mp present)
  change cell.name = handlerName mode at named
  rw [named] at names
  cases mode <;> simp [handlerName, sharedSlotTypes, Ambient.slots] at names

theorem creator_handler_observation (mode : AccountCallSemantics.Mode)
    (source : Word) (dispatcher location : Nat) (value : Value) :
    initializedHandler mode source dispatcher (ContractRuntimeEffectsCorrespondence.creatorCell location value) := by
  intro impossible
  cases mode <;> simp [handlerName, ContractRuntimeEffectsCorrespondence.creatorCell] at impossible

structure ExtraReady (layout : RuntimeCallEffectsCorrespondence.Layout) (cells : List InitializedCell)
    (store : Store) (source : Word) (mode : AccountCallSemantics.Mode) where
  handler : ExtraHandler layout source mode
  member : ⟨handlerName mode, OptionalCell.cellType Calls.callbackType, handler.location⟩ ∈ cells.map InitializedCell.effectSlot
  read : store.read? handler.location = some (.inRight .unit handler.value)

theorem extra_ready (mode : AccountCallSemantics.Mode)
    {cells : List InitializedCell} {store : Store} {extra : List (String × Core.Ty)}
    {layout : RuntimeCallEffectsCorrespondence.Layout} {source : Word}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots ++ extra)
    (initialized : InitializedCells cells store) (separate : CellLocations cells)
    (boundary : layout.boundary = store.length)
    (members : ∀ slot ∈ RuntimeCallInitializedEffects.baseSlots layout.toReturnDataLayout,
      slot ∈ cells.map InitializedCell.effectSlot)
    (observed : ∀ cell ∈ cells, initializedHandler mode source layout.dispatcher cell) :
    Nonempty (ExtraReady layout cells store source mode) := by
  have present : (handlerName mode, OptionalCell.cellType Calls.callbackType) ∈
      cells.map (fun cell => (cell.name, cell.type)) := by
    rw [signature]
    apply List.mem_append_left
    cases mode <;> simp [handlerName, Effects.slots]
  obtain ⟨cell, cellMember, cellSame⟩ := List.mem_map.mp present
  obtain ⟨named, typed⟩ := Prod.mk.inj cellSame
  obtain ⟨value, valueEqual, ⟨closure⟩⟩ := observed cell cellMember named
  have outside : cell.location ∉ RuntimeCallEffectsCorrespondence.mutable layout := by
    intro inside
    have baseMember : cell.location ∈
        (RuntimeCallInitializedEffects.baseSlots layout.toReturnDataLayout).map EffectSlot.location := by
      simp only [RuntimeCallEffectsCorrespondence.mutable, RuntimeLogEffectsCorrespondence.mutable,
        RuntimeEffectsCorrespondence.mutable, StorageBuiltinCorrespondence.Locations.mutable,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at inside
      simp only [RuntimeCallInitializedEffects.baseSlots, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false]
      rcases inside with h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
    obtain ⟨slot, slotMember, sameLocation⟩ := List.mem_map.mp baseMember
    obtain ⟨other, otherMember, sameSlot⟩ := List.mem_map.mp (members slot slotMember)
    have same : other.location = cell.location := (congrArg EffectSlot.location sameSlot).trans sameLocation
    have sameName := separate other otherMember cell cellMember same
    have slotName : slot.name = handlerName mode := (congrArg EffectSlot.name sameSlot).symm.trans (sameName.trans named)
    have names := List.mem_map_of_mem (f := EffectSlot.name) slotMember
    rw [slotName] at names
    cases mode <;> simp [handlerName, RuntimeCallInitializedEffects.baseSlots] at names
  exact ⟨⟨⟨cell.location, by rw [boundary]; exact initialized.location_bound cellMember,
    outside, value, closure⟩,
    List.mem_map.mpr ⟨cell, cellMember, by simp only [InitializedCell.effectSlot, named, typed]⟩,
    by simpa only [valueEqual] using initialized cell cellMember⟩⟩

structure ModeAllocationReady (sharedCells cells : List InitializedCell) (store : Store)
    (parent : RuntimeCallModeSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8)
    (dispatcher creator : Nat) (dispatchValue : Value) where
  base : CallAllocationReady sharedCells cells store parent request shared bytes dispatcher creator dispatchValue
  callCode : ExtraReady base.call.layout cells store request.target .callCode
  delegateCall : ExtraReady base.call.layout cells store request.target .delegateCall

def ModeAllocationReady.handlers {sharedCells cells : List InitializedCell} {store : Store}
    {parent : RuntimeCallModeSemantics.State} {request : AccountCallSemantics.Request}
    {shared : AccountCallSemantics.Shared} {bytes : List UInt8}
    {dispatcher creator : Nat} {dispatchValue : Value}
    (ready : ModeAllocationReady sharedCells cells store parent request shared bytes dispatcher creator dispatchValue)
    (dispatch : AccountCallCorrespondence.DispatcherClosure
      (RuntimeCallEffectsCorrespondence.sharedLocations ready.base.call.layout) dispatchValue)
    (create : CreateHandler ready.base.call.layout) :
    ModeHandlers ready.base.call.layout where
  ordinary := ready.base.handlers dispatch
  callCode := ready.callCode.handler
  delegateCall := ready.delegateCall.handler
  create := create

theorem ModeAllocationReady.captured {sharedCells cells : List InitializedCell} {store : Store}
    {parent : RuntimeCallModeSemantics.State} {request : AccountCallSemantics.Request}
    {shared : AccountCallSemantics.Shared} {bytes : List UInt8}
    {dispatcher creator : Nat} {dispatchValue : Value}
    (ready : ModeAllocationReady sharedCells cells store parent request shared bytes dispatcher creator dispatchValue)
    (dispatch : AccountCallCorrespondence.DispatcherClosure
      (RuntimeCallEffectsCorrespondence.sharedLocations ready.base.call.layout) dispatchValue)
    (create : CreateHandler ready.base.call.layout)
    (createRead : store.read? create.location = some (.inRight .unit create.value))
    (context : RuntimeChildCallEffectsCorrespondence.Context ready.base.call.layout)
    (valid : context.valid (prefixRead ready.base.call.layout.boundary store)) :
    ((ready.handlers dispatch create).context context).valid (prefixRead ready.base.call.layout.boundary store) := by
  refine ⟨valid, ?_, ?_, ?_⟩
  · simpa only [ModeAllocationReady.handlers, prefixRead, ready.callCode.handler.below, ↓reduceIte] using ready.callCode.read
  · simpa only [ModeAllocationReady.handlers, prefixRead, ready.delegateCall.handler.below, ↓reduceIte] using ready.delegateCall.read
  · simpa only [ModeAllocationReady.handlers, prefixRead, create.below, ↓reduceIte] using createRead

theorem ModeAllocationReady.related {sharedCells cells : List InitializedCell} {store : Store}
    {parent : RuntimeCallModeSemantics.State} {request : AccountCallSemantics.Request}
    {shared : AccountCallSemantics.Shared} {bytes : List UInt8}
    {dispatcher creator : Nat} {dispatchValue : Value}
    (ready : ModeAllocationReady sharedCells cells store parent request shared bytes dispatcher creator dispatchValue)
    (dispatch : AccountCallCorrespondence.DispatcherClosure
      (RuntimeCallEffectsCorrespondence.sharedLocations ready.base.call.layout) dispatchValue)
    (create : CreateHandler ready.base.call.layout)
    (createRead : store.read? create.location = some (.inRight .unit create.value))
    {anchors : RuntimeChildCallEffectsCorrespondence.Anchors}
    (context : RuntimeChildCallEffectsCorrespondence.Context ready.base.call.layout)
    (linked : RuntimeLinkedWorldCorrespondence.StateRel anchors shared.world ready.base.call.layout.storage.world store)
    (valid : context.valid (prefixRead ready.base.call.layout.boundary store)) :
    StateRel (RuntimeCallModeEffectsCorrespondence.model ready.base.call.layout
      (prefixRead ready.base.call.layout.boundary store) (cells.map InitializedCell.effectSlot)
      (some bytes) (ready.handlers dispatch create) anchors context) []
      ⟨[], ChildFrameSemantics.initial parent request shared bytes⟩ store :=
  RuntimeChildCallEffectsCorrespondence.of_base (ready.base.related dispatch) linked
    (ready.captured dispatch create createRead context valid)

/-- The actual allocator installs all three handler closures at the execution
address carried by its frame request. -/
theorem allocateModeCallFrame_initializes {depth : Nat} {environment : Environment} {initial : Store}
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
      (⟨"createHandler", OptionalCell.cellType Creation.callbackType, creatorLocation⟩ : EffectSlot) ∈
        cells.map InitializedCell.effectSlot →
      ModeAllocationReady sharedCells cells (initial ++ suffix) parent request sharedState bytes
        dispatcherLocation creatorLocation dispatchValue →
      ∃ value final, Core.Evaluates (extra ++ environment) (initial ++ suffix)
        (continuation values (depth + extra.length)) value final ∧ observes value final) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.allocateFrame (RuntimeExtendedInitializedEffects.slots true) shared
        frame dispatcher creator gas code size known continuation depth) value final ∧ observes value final := by
  have dispatcherBelow := (List.getElem?_eq_some_iff.mp dispatcherFound).1
  have creatorBelow := (List.getElem?_eq_some_iff.mp creatorFound).1
  let ordinaryProperty := fun cell => ContractCallCorrespondence.initializedDepth request.depth cell ∧
    ContractCallCorrespondence.initializedHandler request.target dispatcherLocation cell ∧ cell.location ≠ dispatcherLocation
  let property := fun cell => ordinaryProperty cell ∧
    initializedHandler .callCode request.target dispatcherLocation cell ∧
    initializedHandler .delegateCall request.target dispatcherLocation cell
  have ordinaryFresh : FrameInitializersValid depth environment initial frame dispatcher gas code size known shared ordinaryProperty :=
    ContractRuntimeEffectsCorrespondence.FrameInitializersValid.and
      (ContractCallCorrespondence.fresh_depth_observation frameRelated rfl rfl gasRelated codeRelated sizeRelated knownRelated)
      (ContractRuntimeEffectsCorrespondence.FrameInitializersValid.and
        (ContractCallCorrespondence.fresh_handler_observation frameRelated rfl rfl dispatcherRelated gasRelated codeRelated sizeRelated knownRelated)
        (ContractCallCorrespondence.fresh_dispatcher_separate dispatcherBelow frameRelated rfl gasRelated codeRelated sizeRelated knownRelated))
  have fresh : FrameInitializersValid depth environment initial frame dispatcher gas code size known shared property :=
    ContractRuntimeEffectsCorrespondence.FrameInitializersValid.and ordinaryFresh
      (ContractRuntimeEffectsCorrespondence.FrameInitializersValid.and
        (fresh_handler_observation .callCode frameRelated rfl rfl dispatcherRelated gasRelated codeRelated sizeRelated knownRelated)
        (fresh_handler_observation .delegateCall frameRelated rfl rfl dispatcherRelated gasRelated codeRelated sizeRelated knownRelated))
  have sharedExtra : ∀ cell ∈ sharedCells, property cell := by
    intro cell member
    have present := List.mem_map_of_mem (f := fun cell : InitializedCell => (cell.name, cell.type)) member
    rw [signature] at present
    have typed := List.mem_reverse.mp present
    have names := List.mem_map_of_mem (f := Prod.fst) typed
    refine ⟨⟨?_, ?_, dispatcherSeparate cell member⟩,
      shared_handler_observation .callCode signature _ _ cell member,
      shared_handler_observation .delegateCall signature _ _ cell member⟩
    · intro named
      simp [named, sharedSlotTypes, Ambient.slots] at names
    · intro named
      simp [named, sharedSlotTypes, Ambient.slots] at names
  have creatorExtra : property (ContractRuntimeEffectsCorrespondence.creatorCell creatorLocation creatorValue) :=
    ⟨⟨ContractCallCorrespondence.creator_depth_observation _ _ _,
      ContractCallCorrespondence.creator_handler_observation _ _ _ _, creatorDispatcher⟩,
      creator_handler_observation .callCode _ _ _ _, creator_handler_observation .delegateCall _ _ _ _⟩
  apply allocateFrame_initializes_creator parent request sharedState bytes world references signature initialized separate
    observed creatorRelated creatorFound creatorSeparate frameRelated gasRelated codeRelated sizeRelated knownRelated
    property fresh sharedExtra creatorExtra continuation observes
  intro extra suffix cells values valuesRelated stored fullSignature locations origins sharedOrigins additional creatorCells base
  have cellSeparate : CellLocations cells := locations.subset (fun _ member => List.mem_append_right _ member)
  obtain ⟨call⟩ := RuntimeCallInitializedEffects.ready fullSignature stored cellSeparate base.boundary base.members
    (by rw [base.boundary]; exact Nat.lt_of_lt_of_le dispatcherBelow (by simp))
    (fun cell member => (additional cell member).1.2.2)
    (fun cell member => (additional cell member).1.1)
    (fun cell member => (additional cell member).1.2.1)
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
  let ready : CallAllocationReady sharedCells cells (initial ++ suffix) parent request sharedState bytes
      dispatcherLocation creatorLocation dispatchValue := {
    base := base
    call := call
    inventory := inventory
    sharedMembers := fun cell member => List.mem_map_of_mem (included cell member)
    captured := ContractChildCallCorrespondence.initialized_context inventory initialized ⟨creatorValue, creatorFound⟩
      (StoreRetains.append initial suffix)
    callPassive := RuntimeCallInitializedEffects.call_passive unique cellSeparate baseMembers codeMembers
    dispatcherOutside := fun cell member => (additional cell member).1.2.2
    dispatcherRead := ((StoreRetains.append initial suffix).read dispatcherLocation dispatcherBelow).trans dispatcherFound }

  obtain ⟨callCodeReady⟩ := extra_ready .callCode fullSignature stored cellSeparate boundary baseMembers
    (fun cell member => by simpa only [call.dispatcherEqual] using (additional cell member).2.1)
  obtain ⟨delegateReady⟩ := extra_ready .delegateCall fullSignature stored cellSeparate boundary baseMembers
    (fun cell member => by simpa only [call.dispatcherEqual] using (additional cell member).2.2)
  have creatorMember : (⟨"createHandler", OptionalCell.cellType Creation.callbackType, creatorLocation⟩ : EffectSlot) ∈
      cells.map InitializedCell.effectSlot := by
    have present : ("createHandler", OptionalCell.cellType Creation.callbackType) ∈
        cells.map (fun cell => (cell.name, cell.type)) := by
      rw [fullSignature]
      simp [RuntimeExtendedInitializedEffects.slots, Effects.slots]
    obtain ⟨cell, member, same⟩ := List.mem_map.mp present
    have equal := creatorCells cell member (Prod.mk.inj same).1
    exact List.mem_map.mpr ⟨cell, member, by rw [equal]; rfl⟩
  apply continued extra suffix cells values valuesRelated stored fullSignature locations origins sharedOrigins creatorMember
  exact {base := ready, callCode := callCodeReady, delegateCall := delegateReady}

end Solcore.Frontend.RustHull.ChildFrameModeCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractChildCallInitialLinks
/-! Initial code links are derived from ordinary source-world lookups and the
compiler's byte-image order. No runtime cell relation is a public premise. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractChildCallCorrespondence

/-- Source accounts name their bytecode. The static image lookup records which
compiled catalog entry the actual initializer assigns to each linked account. -/
def InitialCatalogLinks (image : Option (List UInt8)) (catalog : List AccountRuntime.CodeDefinition)
    (anchors : List CatalogWorldCorrespondence.Anchor) (root : Core.Word) (world : StorageSemantics.World) : Prop :=
  ∀ anchor ∈ anchors, ∃ account,
    StorageSemantics.lookup anchor.address world = some account ∧
    account.code = some anchor.bytes ∧ anchor.address ≠ root ∧
    Contract.codeIdentity (image :: catalog.map (some ∘ AccountRuntime.CodeDefinition.bytes))
      (some anchor.bytes) = anchor.identity

theorem initial_links {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition}
    {anchors : List CatalogWorldCorrespondence.Anchor} (object : Contract.CompiledObject) (context : Contract.Context)
    (images : object.codeImages = image :: catalog.map (some ∘ AccountRuntime.CodeDefinition.bytes))
    (source : InitialCatalogLinks image catalog anchors (Contract.normalizeAddress context.address)
      ((StorageCorrespondence.canonical (object.initialWorld context)).map Prod.fst)) :
    CatalogWorldCorrespondence.Links anchors (StorageCorrespondence.canonical (object.initialWorld context)) := by
  intro anchor member
  obtain ⟨account, selected, code, different, identity⟩ := source anchor member
  refine ⟨account, ?_, code⟩
  have found := CatalogWorldCorrespondence.initialWorld_lookup object context selected different
  simpa only [images, code, identity] using found

end Solcore.Frontend.RustHull.ContractChildCallCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractRootCallInitialLinks
/-! Root reentry uses identity one from the actual public initializer. Other
accounts retain the image lookup policy, including aliases of the root image. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CatalogWorldCorrespondence
open Core StorageCorrespondence

/-- The first account is the current address, with the public storage, nonce
and code availability applied before canonical address normalization. -/
theorem initialWorld_root (object : Contract.CompiledObject) (context : Contract.Context) :
    ∃ account, lookup (Contract.normalizeAddress context.address)
        (canonical (object.initialWorld context)) =
        some (account, if context.selfCodeAvailable then 1 else 0) ∧
      account.code = (if context.selfCodeAvailable then object.codeImages.head?.getD none else some []) := by
  let current := {((context.world.find? (·.address == context.address)).getD
      {address := context.address}) with
    storage := context.storage, nonce := context.nonce
    code := if context.selfCodeAvailable then object.codeImages.head?.getD none else some []
    created := context.created}
  have address : current.address = context.address := by
    dsimp only [current]
    cases found : context.world.find? (·.address == context.address) with
    | none => rfl
    | some account =>
      have matched : (account.address == context.address) = true := List.find?_some (p := fun (entry : AccountState.Account) => entry.address == context.address) found
      exact beq_iff_eq.mp matched
  refine ⟨{current with address := Contract.normalizeAddress current.address}, ?_, rfl⟩
  change lookup (Contract.normalizeAddress context.address)
    (({current with address := Contract.normalizeAddress current.address},
      if current.address == context.address then (if context.selfCodeAvailable then 1 else 0)
      else Contract.codeIdentity object.codeImages current.code) :: _) = _
  simp only [lookup, address, beq_self_eq_true, ↓reduceIte]

/-- A supplied root image is assigned identity one without a catalog lookup. -/
theorem initialWorld_root_anchor (object : Contract.CompiledObject) (context : Contract.Context)
    {bytes : List UInt8}
    (available : context.selfCodeAvailable = true)
    (image : object.codeImages.head?.getD none = some bytes) :
    (Anchor.mk (Contract.normalizeAddress context.address) bytes 1).Holds
      (canonical (object.initialWorld context)) := by
  obtain ⟨account, found, code⟩ := initialWorld_root object context
  exact ⟨account, by simpa only [available, ↓reduceIte] using found,
    by simpa only [available, ↓reduceIte, image] using code⟩

theorem compiled_root_anchor {program : Program} {path : List String} {fuel : Nat}
    {bytes : List UInt8} {catalog : List AccountRuntime.CodeDefinition} {object : Contract.CompiledObject}
    (accepted : Contract.compileObject program path fuel (some bytes) catalog = .ok object)
    (context : Contract.Context) (available : context.selfCodeAvailable = true) :
    (Anchor.mk (Contract.normalizeAddress context.address) bytes 1).Holds
      (canonical (object.initialWorld context)) := by
  apply initialWorld_root_anchor object context available
  rw [compileObject_images accepted]
  rfl

end Solcore.Frontend.RustHull.CatalogWorldCorrespondence

namespace Solcore.Frontend.RustHull.ContractRootCallCorrespondence
open Core

/-- Source-side initial links permit the current root image and ordinary
catalog accounts. A non-root account may also carry identity one when its bytes
match the root image. Root code must actually be available in this context. -/
def InitialCatalogLinks (image : Option (List UInt8)) (catalog : List AccountRuntime.CodeDefinition)
    (anchors : List CatalogWorldCorrespondence.Anchor) (root : Word) (available : Bool)
    (world : StorageSemantics.World) : Prop :=
  ∀ anchor ∈ anchors,
    (anchor.address = root ∧ anchor.identity = 1 ∧ image = some anchor.bytes ∧ available = true) ∨
    (∃ account, StorageSemantics.lookup anchor.address world = some account ∧
      account.code = some anchor.bytes ∧ anchor.address ≠ root ∧
      Contract.codeIdentity (image :: catalog.map (some ∘ AccountRuntime.CodeDefinition.bytes))
        (some anchor.bytes) = anchor.identity)

theorem InitialCatalogLinks.of_catalog {image : Option (List UInt8)}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    {root : Word} {world : StorageSemantics.World}
    (related : ContractChildCallCorrespondence.InitialCatalogLinks image catalog anchors root world)
    (available : Bool) : InitialCatalogLinks image catalog anchors root available world :=
  fun anchor member => Or.inr (related anchor member)

theorem InitialCatalogLinks.root_cons {bytes : List UInt8}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    {root : Word} {world : StorageSemantics.World}
    (related : ContractChildCallCorrespondence.InitialCatalogLinks (some bytes) catalog anchors root world) :
    InitialCatalogLinks (some bytes) catalog (⟨root, bytes, 1⟩ :: anchors) root true world := by
  intro anchor member
  rcases List.mem_cons.mp member with rfl | member
  · exact .inl ⟨rfl, rfl, rfl, rfl⟩
  · exact .inr (related anchor member)

theorem initial_links {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition}
    {anchors : List CatalogWorldCorrespondence.Anchor} (object : Contract.CompiledObject) (context : Contract.Context)
    (images : object.codeImages = image :: catalog.map (some ∘ AccountRuntime.CodeDefinition.bytes))
    (source : InitialCatalogLinks image catalog anchors (Contract.normalizeAddress context.address)
      context.selfCodeAvailable ((StorageCorrespondence.canonical (object.initialWorld context)).map Prod.fst)) :
    CatalogWorldCorrespondence.Links anchors (StorageCorrespondence.canonical (object.initialWorld context)) := by
  intro anchor member
  rcases source anchor member with ⟨address, identity, image, available⟩ | other
  · have held := CatalogWorldCorrespondence.initialWorld_root_anchor object context available (by rw [images]; exact image)
    rcases anchor with ⟨ownAddress, bytes, ownIdentity⟩
    cases address
    cases identity
    exact held
  · obtain ⟨account, selected, code, different, identity⟩ := other
    refine ⟨account, ?_, code⟩
    have found := CatalogWorldCorrespondence.initialWorld_lookup object context selected different
    simpa only [images, code, identity] using found

/-- The condition is checked against the same normalized source accounts used
by public execution; it contains no Core store or execution assumption. -/
def InitialContextLinks (image : Option (List UInt8)) (catalog : List AccountRuntime.CodeDefinition)
    (object : Contract.CompiledObject) (context : Contract.Context)
    (anchors : List CatalogWorldCorrespondence.Anchor) : Prop :=
  let normalized := Contract.normalizeContext context
  InitialCatalogLinks image catalog anchors (Contract.normalizeAddress normalized.address)
    normalized.selfCodeAvailable ((StorageCorrespondence.canonical (object.initialWorld normalized)).map Prod.fst)

theorem initial_context_links {program : Program} {path : List String} {fuel : Nat}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {object : Contract.CompiledObject}
    {anchors : List CatalogWorldCorrespondence.Anchor}
    (accepted : Contract.compileObject program path fuel image catalog = .ok object)
    (context : Contract.Context) (source : InitialContextLinks image catalog object context anchors) :
    CatalogWorldCorrespondence.Links anchors
      (StorageCorrespondence.canonical (object.initialWorld (Contract.normalizeContext context))) :=
  initial_links object (Contract.normalizeContext context) (CatalogWorldCorrespondence.compileObject_images accepted) source

end Solcore.Frontend.RustHull.ContractRootCallCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.InitCatalogConnection
/-! The premise that links a source init catalog to the compiled catalog. The
source init templates are the compiled init definitions, in catalog order, with
the same program, object and init bytes; each runtime image a source deployment
may install is a runtime image of the compiled object; and the catalog is small
enough that the identities `index + 2` of its entries are distinct words. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.InitCatalogCorrespondence

/-- The compiled init definitions with their catalog indices, in catalog order,
as the actual `runInit` selects among them. -/
def initDefinitions (catalog : List AccountRuntime.CodeDefinition) : List (AccountRuntime.CodeDefinition × Nat) :=
  catalog.zipIdx.filter fun (definition, _) => definition.isInit

/-- The runtime images the actual installation identifies: the root image and
the catalog entries that are not init definitions. -/
def runtimeImages (image : Option (List UInt8)) (catalog : List AccountRuntime.CodeDefinition) :
    List (List UInt8) :=
  image.toList ++ (catalog.filter fun definition => !definition.isInit).map AccountRuntime.CodeDefinition.bytes

def InitCatalogConnection (initCatalog : ChildFrameSemantics.InitCatalog) (image : Option (List UInt8))
    (catalog : List AccountRuntime.CodeDefinition) : Prop :=
  initCatalog.templates.length = (initDefinitions catalog).length ∧
  (∀ (position : Nat) (source : ChildFrameSemantics.Code), initCatalog.templates[position]? = some source →
    ∃ (definition : AccountRuntime.CodeDefinition) (index : Nat),
      (initDefinitions catalog)[position]? = some (definition, index) ∧
      source.program = definition.program ∧
      AccountRuntime.select definition.program.objects definition.path = .ok source.body ∧
      source.bytes = definition.bytes ∧
      DerivationCorrespondence.ExecutableProgram (ContractCallModeCorrespondence.supported true) source.functions) ∧
  (∀ bytes ∈ initCatalog.runtimes, bytes ∈ runtimeImages image catalog) ∧
  catalog.length + 2 < Core.wordModulus

/-- A program that creates nothing links the empty init catalog to any catalog
without init definitions. -/
theorem InitCatalogConnection.empty {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition}
    (noInit : initDefinitions catalog = []) (small : catalog.length + 2 < Core.wordModulus) :
    InitCatalogConnection {} image catalog := by
  refine ⟨by simp [noInit], ?_, ?_, small⟩
  · intro position source found
    simp at found
  · intro bytes member
    simp at member

end Solcore.Frontend.RustHull.InitCatalogCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ModeChildCatalogExecutionCorrespondence
/-! Finite nested child execution uses the same compiled catalog identities.
Selected child programs may call the installed dispatcher; execution at the
next smaller height supplies the internal frame interface. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ModeChildCatalogExecutionCorrespondence
open Core Correspondence ScalarExecution CodeBuilder
open RuntimeCallEffectsCorrespondence (Layout sharedLocations)
open AccountCallCorrespondence

/-- All conditions concern source selection, compilation structure and runtime
identity representation. Child execution is derived separately below. -/
def CatalogConnection (sourceCatalog : ChildFrameSemantics.Catalog)
    (catalog : List AccountRuntime.CodeDefinition) (anchors : List CatalogWorldCorrespondence.Anchor) : Prop :=
  ∀ address source, ChildFrameSemantics.select sourceCatalog address = some source →
    ∃ index definition, catalog[index]? = some definition ∧ source.program = definition.program ∧
      AccountRuntime.select definition.program.objects definition.path = .ok source.body ∧
      source.bytes = definition.bytes ∧
      CatalogWorldCorrespondence.Anchor.mk address source.bytes (index + 2) ∈ anchors ∧
      Word.ofNatModulo (index + 2) ≠ Word.zero ∧
      (List.range (catalog.length + 1)).find?
        (fun candidate => Word.ofNatModulo (index + 2) == Word.ofNatModulo (candidate + 1)) = some (index + 1) ∧
      DerivationCorrespondence.ExecutableProgram (ContractCallModeCorrespondence.supported true) source.functions

theorem selected_frame {sourceCatalog : ChildFrameSemantics.Catalog}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    (connection : CatalogConnection sourceCatalog catalog anchors)
    {fuel : Nat} {others : List Core.Expr}
    (compiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    {captured environment : Environment} {values : List Value} {closure : Value} {depth : Nat} {functions : Code}
    (closures : CapturedClosures captured others values)
    (functionsRelated : CodeValue depth environment functions (bundleValues (closure :: values)))
    {address : Word} {source : ChildFrameSemantics.Code}
    (selected : ChildFrameSemantics.select sourceCatalog address = some source) :
    ∃ index expression value,
      CatalogWorldCorrespondence.Anchor.mk address source.bytes (index + 2) ∈ anchors ∧
      Word.ofNatModulo (index + 2) ≠ Word.zero ∧
      (List.range (others.length + 1)).find?
        (fun candidate => Word.ofNatModulo (index + 2) == Word.ofNatModulo (candidate + 1)) = some (index + 1) ∧
      AccountRuntime.compileFrame source.program source.body (RuntimeExtendedInitializedEffects.slots true) fuel = .ok expression ∧
      DerivationCorrespondence.ExecutableProgram (ContractCallModeCorrespondence.supported true) source.functions ∧
      CapturedClosure expression captured value ∧
      CodeValue depth environment (part (index + 1) (others.length + 1) functions) value := by
  obtain ⟨index, definition, found, program, body, _, anchored, nonzero, first, eligible⟩ := connection address source selected
  obtain ⟨code, expression, value, codeSelected, accepted, captured, referenced⟩ :=
    ContractCatalogCorrespondence.catalog_reference compiled closures functionsRelated found
  have same : code = source.body := Except.ok.inj (codeSelected.symm.trans body)
  subst code
  refine ⟨index, expression, value, anchored, nonzero, ?_, ?_, eligible, captured, referenced⟩
  · simpa only [compiled.length] using first
  · simpa only [program] using accepted

/-- Internal induction interface for one actual compiled frame invocation.
Every closure, reference and current shared read comes from the real object
capture and allocator; only the finite source derivation varies with height. -/
def FrameExecution (sourceCatalog : ChildFrameSemantics.Catalog)
    (catalog : List AccountRuntime.CodeDefinition) (anchors : List CatalogWorldCorrespondence.Anchor)
    (effects : Option (List UInt8) → Semantics.ExternalSemantics RuntimeCallModeSemantics.State) : Prop :=
  ∀ {source : ChildFrameSemantics.Code} {fuel : Nat} {compiled : Core.Expr} {others : List Core.Expr},
    AccountRuntime.compileFrame source.program source.body (RuntimeExtendedInitializedEffects.slots true) fuel = .ok compiled →
    DerivationCorrespondence.ExecutableProgram (ContractCallModeCorrespondence.supported true) source.functions →
    ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others →
    CatalogConnection sourceCatalog catalog anchors →
  ∀ {captured : Environment} {catalogValues : List Value} {rootClosure : Value},
    CapturedClosures captured others catalogValues →
  ∀ {images : List (Nat × List UInt8)} {sharedCells : List InitializedCell}
    {dispatcherLocation creatorLocation : Nat} {initial : Store},
    (capture : ObjectCallbackCapture (RuntimeExtendedInitializedEffects.slots true) (others.length + 1) images catalog
      (rootClosure :: catalogValues) sharedCells dispatcherLocation creatorLocation initial) →
  ∀ {depth : Nat} {environment : Environment} {frame dispatcher creator gas code size known function : Code} {closure : Value},
    CapturedClosure compiled captured closure →
    CodeValue depth environment function closure →
    (parent : RuntimeCallModeSemantics.State) → (request : AccountCallSemantics.Request) →
    (sharedState : AccountCallSemantics.Shared) →
  ∀ {accounts : StorageCorrespondence.Accounts}, accounts.map Prod.fst = sharedState.world →
    RuntimeReferences depth environment capture.shared sharedCells →
    sharedCells.map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse →
    InitializedCells sharedCells initial → CellLocations sharedCells →
    (∀ cell ∈ sharedCells, ChildFrameCorrespondence.Observed accounts
      (ChildFrameCorrespondence.Initial parent request sharedState source.bytes) source.bytes cell) →
    CodeValue depth environment creator (.cellRef (OptionalCell.cellType Creation.callbackType) creatorLocation) →
    (∃ value, initial.read? creatorLocation = some value) →
    (∀ cell ∈ sharedCells, cell.location ≠ creatorLocation) →
    CodeValue depth environment dispatcher
      (.cellRef (OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation) →
    (∀ cell ∈ sharedCells, cell.location ≠ dispatcherLocation) → creatorLocation ≠ dispatcherLocation →
    CodeValue depth environment frame (CallTransportCorrespondence.requestValue request) →
    CodeValue depth environment gas (optionalWordValue (some request.gas)) →
    CodeValue depth environment code (WordMapping.encode (Memory.packBytes source.bytes)) →
    CodeValue depth environment size (.word (Word.ofNatModulo source.bytes.length)) →
    CodeValue depth environment known (.bool true) →
  ∀ {locations : AccountCallCorrespondence.SharedLocations},
    AccountCallCorrespondence.SharedReferences depth environment capture.shared locations →
    RuntimeLinkedWorldCorrespondence.StateRel anchors sharedState.world locations.world initial →
  ∀ {createValue : Value}, initial.read? creatorLocation = some (.inRight .unit createValue) →
    CreationCorrespondence.HandlerClosure locations createValue →
  ∀ {status : Semantics.Result Semantics.Value} {finalSource : Semantics.State RuntimeCallModeSemantics.State}
    {response : Semantics.Result AccountCallSemantics.Response},
    Semantics.EvalFunction source.functions (effects (some source.bytes)) source.entry []
      ⟨[], ChildFrameSemantics.initial parent request sharedState source.bytes⟩ status finalSource →
    ChildResultSemantics.Respond
      (ChildFrameSemantics.completedStatus status finalSource.external.runtime.runtime.runtime.runtime.runtime)
      finalSource.external.runtime.runtime.runtime.runtime.runtime response →
    ∃ target final, Core.Evaluates environment initial
      (AccountRuntime.allocateFrame (RuntimeExtendedInitializedEffects.slots true) capture.shared frame dispatcher creator gas code size known
        (fun values => bind (apply function (packet values)) AccountRuntime.childResult) depth) target final ∧
      CallTransportCorrespondence.ResponseRel response target ∧
      AccountCallCorrespondence.LinkedSharedStateRel anchors locations (RuntimeCallModeSemantics.shared finalSource.external) final ∧
      AccountCallCorrespondence.SharedFrame locations initial final

end Solcore.Frontend.RustHull.ModeChildCatalogExecutionCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ModeChildCatalogRunCorrespondence
/-! A finite source child tree reaches the actual selected catalog closure.
The smaller-height frame theorem supplies execution, while refreshed captures
retain the real dispatcher for any nested call made by that child. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallModeCorrespondence

/-- Additional immutable callback observations strengthen the invocation
precondition without changing the selected code or its execution relation. -/
theorem ChildRunPreservation.strengthen {mode : AccountCallSemantics.Mode}
    {anchors : List CatalogWorldCorrespondence.Anchor}
    {locations : AccountCallCorrespondence.SharedLocations}
    {shared : AccountRuntime.References} {runFrame : CodeBuilder.Code → CodeBuilder.Code → CodeBuilder.Code}
    {children : AccountCallSemantics.Children} {valid stronger : Core.Store → Prop}
    {depth : Nat} {captured : Core.Environment}
    (preserved : ChildRunPreservation mode anchors locations shared runFrame children valid depth captured)
    (implies : ∀ store, stronger store → valid store) :
    ChildRunPreservation mode anchors locations shared runFrame children stronger depth captured := by
  intro source request state result finalState computed extra store extended precompiled references argument related ready
  exact preserved computed extra references argument related (implies store ready)

end Solcore.Frontend.RustHull.AccountCallModeCorrespondence

namespace Solcore.Frontend.RustHull.ModeChildCatalogExecutionCorrespondence
open Core Correspondence ScalarExecution CodeBuilder
open RuntimeCallEffectsCorrespondence (Layout sharedLocations)
open AccountCallCorrespondence hiding ChildRunPreservation childRequest_value
open AccountCallModeCorrespondence (ChildRunPreservation childRequest_value)

theorem child_runs_preserves {sourceCatalog : ChildFrameSemantics.Catalog}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    {effects : Option (List UInt8) → Semantics.ExternalSemantics RuntimeCallModeSemantics.State}
    (connection : CatalogConnection sourceCatalog catalog anchors)
    (frameExecution : FrameExecution sourceCatalog catalog anchors effects)
    {fuel : Nat} {others : List Core.Expr}
    (compiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    {captured : Environment} {values : List Value} {closure : Value}
    (closures : CapturedClosures captured others values)
    {images : List (Nat × List UInt8)} {cells : List InitializedCell} {creatorLocation : Nat}
    {layout : Layout} {initial : Store}
    (capture : ObjectCallbackCapture (RuntimeExtendedInitializedEffects.slots true) (others.length + 1) images catalog
      (closure :: values) cells layout.dispatcher creatorLocation initial)
    (inventory : NestedChildCallbackContextCorrespondence.Inventory layout cells creatorLocation)
    (create : RuntimeCallModeEffectsCorrespondence.CreateHandler layout) (createAt : create.location = creatorLocation)
    (mode : AccountCallSemantics.Mode) (parent : RuntimeCallModeSemantics.State)
    (ambient : ∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
      ContractEnvironmentCorrespondence.initializedValue parent.runtime.runtime.runtime.runtime.environment cell) :
    ChildRunPreservation mode anchors (sharedLocations layout) capture.shared
      (RuntimeCatalogDispatchCorrespondence.runFrame (RuntimeExtendedInitializedEffects.slots true)
        (others.length + 1) capture.functions capture.shared capture.dispatcher capture.creator)
      (ChildFrameModeSemantics.Children sourceCatalog effects parent)
      (RuntimeChildCallEffectsCorrespondence.childReady layout
        (create.context (NestedChildCallbackContextCorrespondence.context inventory capture.closure)))
      capture.depth capture.environment := by
  intro caller request initialShared response finalShared computed extra store extended precompiled sharedReferences argument related ready
  cases computed with
  | @executed _ caller request initialShared account source status finalSource response ordinary found selected known evaluated responded =>
    obtain ⟨index, expression, value, anchored, nonzero, first, accepted, eligible, capturedFrame, functionRelated⟩ :=
      selected_frame connection compiled closures capture.functionValues selected
    obtain ⟨accounts, actualAccount, sameWorld, links, worldRead, sourceFound, actualFound, code⟩ :=
      RuntimeLinkedWorldCorrespondence.selected related.linked anchored
    have sameAccount : actualAccount = account := Option.some.inj (sourceFound.symm.trans found)
    subst actualAccount
    let baseDepth := capture.depth + extra.length
    let baseEnvironment := extra ++ capture.environment
    let afterLookup := StorageCorrespondence.getStore accounts request.target initialShared.complete baseEnvironment store
    have retained : StoreRetains store afterLookup := StoreRetains.append _ _
    have afterReady := RuntimeChildCallEffectsCorrespondence.childReady_preserved
      (SharedFrame.ofRetains retained) ready
    obtain ⟨freshAccounts, creatorValue, freshWorld, _, stored, signature, separate, observed, creatorRead, creatorSeparate⟩ :=
      ChildCallbackContextCorrespondence.refresh_ready inventory.base afterReady.1 afterReady.2.1.1
        parent (ChildFrameModeSemantics.executionRequest mode caller request) initialShared source.bytes ambient (related.linked.retained retained) (related.shared.retained retained)
    let recordValue := StorageCorrespondence.record account (index + 2)
    let recordCode : Code := fun here => .var (here - baseDepth - 1)
    have recordRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment) recordCode recordValue :=
      CodeValue.bound baseDepth baseEnvironment recordValue
    have frameRelated := (childRequest_value argument).prepend [recordValue]
    have gasRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment)
        (present (part 5 8 (childRequest extended))) (optionalWordValue (some request.gas)) := by
      intro prefixValues current
      exact .inRight ((frameRelated.part (index := 5) rfl) prefixValues current)
    have codeRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment)
        (part 4 9 recordCode) (WordMapping.encode (Memory.packBytes source.bytes)) := by
      simpa only [StorageCorrespondence.record, known, Option.getD_some, List.length_cons, List.length_nil] using recordRelated.part (index := 4) rfl
    have sizeRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment)
        (part 5 9 recordCode) (.word (Word.ofNatModulo source.bytes.length)) := by
      simpa only [StorageCorrespondence.record, known, Option.getD_some, List.length_cons, List.length_nil] using recordRelated.part (index := 5) rfl
    have knownRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment)
        (part 6 9 recordCode) (.bool true) := by
      simpa only [StorageCorrespondence.record, known, Option.isSome_some, List.length_cons, List.length_nil] using recordRelated.part (index := 6) rfl
    have createRead : afterLookup.read? creatorLocation = some (.inRight .unit create.value) := by
      rw [← createAt]
      simpa only [prefixRead, create.below, ↓reduceIte] using afterReady.2.2
    have refreshedReferences := ChildFrameCorrespondence.refresh_references
      ((capture.references.prepend extra).prepend [recordValue]) afterLookup
    let refreshedCapture := NestedChildCallbackContextCorrespondence.refreshCapture capture afterLookup
      (NestedChildCallbackContextCorrespondence.dispatcher_read afterReady.2.1)
    have dispatcherSeparate : ∀ cell ∈ ChildFrameCorrespondence.refresh afterLookup cells,
        cell.location ≠ layout.dispatcher := by
      intro cell member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact inventory.dispatcherSeparate original present
    obtain ⟨target, final, invoked, resultRelated, finalRelated, frame⟩ :=
      frameExecution accepted eligible compiled connection closures refreshedCapture capturedFrame
        ((functionRelated.prepend extra).prepend [recordValue]) parent (ChildFrameModeSemantics.executionRequest mode caller request) initialShared freshWorld
        refreshedReferences signature stored separate observed
        ((capture.creatorValue.prepend extra).prepend [recordValue]) ⟨creatorValue, creatorRead⟩ creatorSeparate
        ((capture.dispatcherValue.prepend extra).prepend [recordValue]) dispatcherSeparate inventory.creatorDispatcher
        frameRelated gasRelated codeRelated sizeRelated knownRelated
        (sharedReferences.prepend [recordValue]) (related.linked.retained retained) createRead create.closure
        evaluated responded (dispatcher := capture.dispatcher)
    have selectedRun := RuntimeCatalogDispatchCorrespondence.runFrame_evaluates first recordRelated invoked
    refine ⟨target, final, ?_, resultRelated, finalRelated, (SharedFrame.ofRetains retained).trans frame⟩
    exact accountRun_child_evaluates sharedReferences
      ((argument.part (index := 0) rfl).part (index := 0) rfl) worldRead related.shared.complete
      ordinary actualFound nonzero selectedRun

/-- The refreshed proof inventory does not replace the installed dispatcher;
this wrapper refers to the closure constructed by the real object initializer. -/
theorem captured_child_runs_preserves {sourceCatalog : ChildFrameSemantics.Catalog}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    {effects : Option (List UInt8) → Semantics.ExternalSemantics RuntimeCallModeSemantics.State}
    (connection : CatalogConnection sourceCatalog catalog anchors)
    (frameExecution : FrameExecution sourceCatalog catalog anchors effects)
    {fuel : Nat} {others : List Core.Expr}
    (compiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    {captured : Environment} {values : List Value} {closure : Value}
    (closures : CapturedClosures captured others values)
    {images : List (Nat × List UInt8)} {cells : List InitializedCell} {creatorLocation : Nat}
    {layout : Layout} {initial : Store}
    (capture : ObjectCallbackCapture (RuntimeExtendedInitializedEffects.slots true) (others.length + 1) images catalog
      (closure :: values) cells layout.dispatcher creatorLocation initial)
    (inventory : NestedChildCallbackContextCorrespondence.Inventory layout cells creatorLocation)
    (sharedReferences : SharedReferences capture.depth capture.environment capture.shared (sharedLocations layout))
    (create : RuntimeCallModeEffectsCorrespondence.CreateHandler layout) (createAt : create.location = creatorLocation)
    (mode : AccountCallSemantics.Mode) (parent : RuntimeCallModeSemantics.State)
    (ambient : ∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
      ContractEnvironmentCorrespondence.initializedValue parent.runtime.runtime.runtime.runtime.environment cell) :
    let dispatcher := ContractCallCorrespondence.captured_dispatcher capture (sharedLocations layout) sharedReferences
    ChildRunPreservation mode anchors (sharedLocations layout) dispatcher.shared dispatcher.runFrame
      (ChildFrameModeSemantics.Children sourceCatalog effects parent)
      (RuntimeChildCallEffectsCorrespondence.childReady layout
        (create.context (NestedChildCallbackContextCorrespondence.context inventory capture.closure)))
      dispatcher.depth dispatcher.captured :=
  child_runs_preserves connection frameExecution compiled closures capture inventory create createAt mode parent ambient

end Solcore.Frontend.RustHull.ModeChildCatalogExecutionCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ModeChildFrameInvokeCorrespondence
/-! A callable child frame uses the actual allocator and installed dispatcher.
The callback interface is discharged by induction on the independent call tree. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ModeChildFrameCorrespondence
open Core Correspondence ScalarExecution CodeBuilder ChildFrameCorrespondence
open ModeChildCatalogExecutionCorrespondence (FrameExecution CatalogConnection)

/-- Internal callback interface, uniform over actual catalog captures and fresh
frame layouts. It is not a premise of the public execution theorem. -/
def CatalogCallbacks (sourceCatalog : ChildFrameSemantics.Catalog)
    (catalog : List AccountRuntime.CodeDefinition) (anchors : List CatalogWorldCorrespondence.Anchor)
    (children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children) : Prop :=
  ∀ {fuel : Nat} {others : List Core.Expr},
    ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others →
    CatalogConnection sourceCatalog catalog anchors →
  ∀ {captured : Environment} {catalogValues : List Value} {rootClosure : Value},
    CapturedClosures captured others catalogValues →
  ∀ {images : List (Nat × List UInt8)} {cells : List InitializedCell} {creator : Nat}
    {layout : RuntimeCallEffectsCorrespondence.Layout} {initial : Store},
    (capture : ObjectCallbackCapture (RuntimeExtendedInitializedEffects.slots true) (others.length + 1) images catalog
      (rootClosure :: catalogValues) cells layout.dispatcher creator initial) →
    (inventory : NestedChildCallbackContextCorrespondence.Inventory layout cells creator) →
    (references : AccountCallCorrespondence.SharedReferences capture.depth capture.environment capture.shared
      (RuntimeCallEffectsCorrespondence.sharedLocations layout)) →
    (create : RuntimeCallModeEffectsCorrespondence.CreateHandler layout) → create.location = creator →
    (mode : AccountCallSemantics.Mode) → (parent : RuntimeCallEffectsSemantics.State) →
    (∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
      ContractEnvironmentCorrespondence.initializedValue parent.runtime.runtime.runtime.runtime.environment cell) →
    let dispatcher := ContractCallCorrespondence.captured_dispatcher capture _ references
    AccountCallModeCorrespondence.ChildRunPreservation mode anchors (RuntimeCallEffectsCorrespondence.sharedLocations layout)
      dispatcher.shared dispatcher.runFrame (children parent)
      (RuntimeChildCallEffectsCorrespondence.childReady layout
        (create.context (NestedChildCallbackContextCorrespondence.context inventory capture.closure)))
      dispatcher.depth dispatcher.captured

theorem frame_execution_of_callbacks {sourceCatalog : ChildFrameSemantics.Catalog}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    {children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children}
    (callbacks : CatalogCallbacks sourceCatalog catalog anchors children) :
    FrameExecution sourceCatalog catalog anchors (RuntimeCallModeSemantics.effectsWith children) := by
  intro source fuel compiled others accepted eligible catalogCompiled connection captured catalogValues rootClosure catalogCaptured
    images sharedCells dispatcherLocation creatorLocation initial capture depth environment frame dispatcher creator gas code size known function closure
    closureRelated resolved parent request sharedState accounts world references signature initialized separate observed
    creatorRelated creatorFound creatorSeparate dispatcherRelated dispatcherSeparate creatorDispatcher
    frameRelated gasRelated codeRelated sizeRelated knownRelated locations sharedReferences linked createValue createRead createClosure
    status finalSource response evaluated responded
  obtain ⟨creatorValue, creatorRead⟩ := creatorFound
  apply ChildFrameModeCorrespondence.allocateModeCallFrame_initializes parent request sharedState source.bytes world references signature initialized separate observed
    creatorRelated creatorRead creatorSeparate dispatcherRelated capture.stored dispatcherSeparate creatorDispatcher
    frameRelated gasRelated codeRelated sizeRelated knownRelated
    (fun values => bind (apply function (packet values)) AccountRuntime.childResult)
    (fun target final => CallTransportCorrespondence.ResponseRel response target ∧
      AccountCallCorrespondence.LinkedSharedStateRel anchors locations (RuntimeCallEffectsSemantics.shared finalSource.external) final ∧
      AccountCallCorrespondence.SharedFrame locations initial final)
  intro extra suffix cells values valuesRelated stored cellsSignature allSeparate origins sharedOrigins creatorMember modeReady
  let ready := modeReady.base
  let inventory := ready.nestedInventory dispatcherSeparate creatorDispatcher
  let capture' := NestedChildCallbackContextCorrespondence.withDispatcher capture _ ready.call.dispatcherEqual
  have capturedReferences := ContractChildCallCorrespondence.inventory_references inventory.base capture'.references
  let dispatchCapture := ContractCallCorrespondence.captured_dispatcher capture' _ capturedReferences
  let callbackContext := NestedChildCallbackContextCorrespondence.context inventory capture.closure
  have locationsEqual : RuntimeCallEffectsCorrespondence.sharedLocations ready.call.layout = locations :=
    shared_references_unique (ContractChildCallCorrespondence.inventory_references inventory.base references) sharedReferences
  let childCreate : RuntimeCallModeEffectsCorrespondence.CreateHandler ready.call.layout := {
    location := creatorLocation
    below := inventory.creatorBelow
    outside := inventory.creatorOutside
    value := createValue
    closure := by rw [locationsEqual]; exact createClosure }
  let handlers := modeReady.handlers dispatchCapture childCreate
  have initialLinked : RuntimeLinkedWorldCorrespondence.StateRel anchors sharedState.world ready.call.layout.storage.world (initial ++ suffix) := by
    have same := congrArg AccountCallCorrespondence.SharedLocations.world locationsEqual
    change ready.call.layout.storage.world = locations.world at same
    rw [same]
    exact linked.retained (StoreRetains.append initial suffix)
  have childCreateRead : (initial ++ suffix).read? childCreate.location = some (.inRight .unit childCreate.value) := by
    change (initial ++ suffix).read? creatorLocation = some (.inRight .unit createValue)
    simpa only [Store.read?, List.getElem?_append_left (List.getElem?_eq_some_iff.mp createRead).1] using createRead
  have initialState := modeReady.related dispatchCapture childCreate childCreateRead callbackContext initialLinked
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
        (callbacks catalogCompiled connection catalogCaptured capture' inventory capturedReferences childCreate rfl
          operation.mode state.external ambient)
        (fun _ valid => ⟨valid.1, valid.2.1, valid.2.2.2.2⟩)
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
      (slot_present "callvalue" .word (by simp [RuntimeExtendedInitializedEffects.slots, Effects.slots]))
      ⟨creatorMember, slot_present "availableGas" (.sum .unit .word) (by simp [RuntimeExtendedInitializedEffects.slots, Effects.slots])⟩
      initialState
      (by simpa only [ready.call.baseEqual] using ready.base.passive) ready.callPassive bodyCallbacks evaluated
  have finalShared := ready.linked_shared_state state
  have retained := ready.parent_frame origins state
  rw [locationsEqual] at finalShared retained
  obtain ⟨target, final, resultRelated, executed, extractionRetains⟩ := bind_evaluates statusRelated represented responded called
  exact ⟨target, final, executed, resultRelated, finalShared.retained extractionRetains,
    retained.trans (AccountCallCorrespondence.SharedFrame.ofRetains extractionRetains)⟩

end Solcore.Frontend.RustHull.ModeChildFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ModeChildFrameCorrespondence
/-! Finite source call trees determine actual compiled child execution. The
induction counts source child frames independently of Core evaluation fuel. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ModeChildFrameCorrespondence
open ModeChildCatalogExecutionCorrespondence

theorem frame_execution (sourceCatalog : ChildFrameSemantics.Catalog) {initCatalog : ChildFrameSemantics.InitCatalog}
    (catalog : List AccountRuntime.CodeDefinition) (anchors : List CatalogWorldCorrespondence.Anchor)
    (height : Nat) : FrameExecution sourceCatalog catalog anchors (ChildFrameModeSemantics.effectsAt sourceCatalog initCatalog height) := by
  induction height with
  | zero =>
      apply frame_execution_of_callbacks
      intro fuel others compiled connection captured values closure closures images cells creator layout initial capture
        inventory references create createAt mode parent ambient
      dsimp only
      intro caller request shared response final impossible
      cases impossible
  | succ height induction =>
      apply frame_execution_of_callbacks
      intro fuel others compiled connection captured values closure closures images cells creator layout initial capture
        inventory references create createAt mode parent ambient
      exact captured_child_runs_preserves connection induction compiled closures capture inventory references create createAt
        mode parent ambient

end Solcore.Frontend.RustHull.ModeChildFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.NestedChildCatalogExecutionCorrespondence
/-! Finite nested child execution uses the same compiled catalog identities.
Selected child programs may call the installed dispatcher; execution at the
next smaller height supplies the internal frame interface. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.NestedChildCatalogExecutionCorrespondence
open Core Correspondence ScalarExecution CodeBuilder
open RuntimeCallEffectsCorrespondence (Layout sharedLocations)
open AccountCallCorrespondence

/-- All conditions concern source selection, compilation structure and runtime
identity representation. Child execution is derived separately below. -/
def CatalogConnection (sourceCatalog : ChildFrameSemantics.Catalog)
    (catalog : List AccountRuntime.CodeDefinition) (anchors : List CatalogWorldCorrespondence.Anchor) : Prop :=
  ∀ address source, ChildFrameSemantics.select sourceCatalog address = some source →
    ∃ index definition, catalog[index]? = some definition ∧ source.program = definition.program ∧
      AccountRuntime.select definition.program.objects definition.path = .ok source.body ∧
      source.bytes = definition.bytes ∧
      CatalogWorldCorrespondence.Anchor.mk address source.bytes (index + 2) ∈ anchors ∧
      Word.ofNatModulo (index + 2) ≠ Word.zero ∧
      (List.range (catalog.length + 1)).find?
        (fun candidate => Word.ofNatModulo (index + 2) == Word.ofNatModulo (candidate + 1)) = some (index + 1) ∧
      DerivationCorrespondence.ExecutableProgram (ContractChildCallCorrespondence.supported true) source.functions

theorem selected_frame {sourceCatalog : ChildFrameSemantics.Catalog}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    (connection : CatalogConnection sourceCatalog catalog anchors)
    {fuel : Nat} {others : List Core.Expr}
    (compiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    {captured environment : Environment} {values : List Value} {closure : Value} {depth : Nat} {functions : Code}
    (closures : CapturedClosures captured others values)
    (functionsRelated : CodeValue depth environment functions (bundleValues (closure :: values)))
    {address : Word} {source : ChildFrameSemantics.Code}
    (selected : ChildFrameSemantics.select sourceCatalog address = some source) :
    ∃ index expression value,
      CatalogWorldCorrespondence.Anchor.mk address source.bytes (index + 2) ∈ anchors ∧
      Word.ofNatModulo (index + 2) ≠ Word.zero ∧
      (List.range (others.length + 1)).find?
        (fun candidate => Word.ofNatModulo (index + 2) == Word.ofNatModulo (candidate + 1)) = some (index + 1) ∧
      AccountRuntime.compileFrame source.program source.body (RuntimeExtendedInitializedEffects.slots true) fuel = .ok expression ∧
      DerivationCorrespondence.ExecutableProgram (ContractChildCallCorrespondence.supported true) source.functions ∧
      CapturedClosure expression captured value ∧
      CodeValue depth environment (part (index + 1) (others.length + 1) functions) value := by
  obtain ⟨index, definition, found, program, body, _, anchored, nonzero, first, eligible⟩ := connection address source selected
  obtain ⟨code, expression, value, codeSelected, accepted, captured, referenced⟩ :=
    ContractCatalogCorrespondence.catalog_reference compiled closures functionsRelated found
  have same : code = source.body := Except.ok.inj (codeSelected.symm.trans body)
  subst code
  refine ⟨index, expression, value, anchored, nonzero, ?_, ?_, eligible, captured, referenced⟩
  · simpa only [compiled.length] using first
  · simpa only [program] using accepted

/-- Internal induction interface for one actual compiled frame invocation.
Every closure, reference and current shared read comes from the real object
capture and allocator; only the finite source derivation varies with height. -/
def FrameExecution (sourceCatalog : ChildFrameSemantics.Catalog)
    (catalog : List AccountRuntime.CodeDefinition) (anchors : List CatalogWorldCorrespondence.Anchor)
    (effects : Option (List UInt8) → Semantics.ExternalSemantics RuntimeCallEffectsSemantics.State) : Prop :=
  ∀ {source : ChildFrameSemantics.Code} {fuel : Nat} {compiled : Core.Expr} {others : List Core.Expr},
    AccountRuntime.compileFrame source.program source.body (RuntimeExtendedInitializedEffects.slots true) fuel = .ok compiled →
    DerivationCorrespondence.ExecutableProgram (ContractChildCallCorrespondence.supported true) source.functions →
    ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others →
    CatalogConnection sourceCatalog catalog anchors →
  ∀ {captured : Environment} {catalogValues : List Value} {rootClosure : Value},
    CapturedClosures captured others catalogValues →
  ∀ {images : List (Nat × List UInt8)} {sharedCells : List InitializedCell}
    {dispatcherLocation creatorLocation : Nat} {initial : Store},
    (capture : ObjectCallbackCapture (RuntimeExtendedInitializedEffects.slots true) (others.length + 1) images catalog
      (rootClosure :: catalogValues) sharedCells dispatcherLocation creatorLocation initial) →
  ∀ {depth : Nat} {environment : Environment} {frame dispatcher creator gas code size known function : Code} {closure : Value},
    CapturedClosure compiled captured closure →
    CodeValue depth environment function closure →
    (parent : RuntimeCallEffectsSemantics.State) → (request : AccountCallSemantics.Request) →
    (sharedState : AccountCallSemantics.Shared) →
  ∀ {accounts : StorageCorrespondence.Accounts}, accounts.map Prod.fst = sharedState.world →
    RuntimeReferences depth environment capture.shared sharedCells →
    sharedCells.map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse →
    InitializedCells sharedCells initial → CellLocations sharedCells →
    (∀ cell ∈ sharedCells, ChildFrameCorrespondence.Observed accounts
      (ChildFrameCorrespondence.Initial parent request sharedState source.bytes) source.bytes cell) →
    CodeValue depth environment creator (.cellRef (OptionalCell.cellType Creation.callbackType) creatorLocation) →
    (∃ value, initial.read? creatorLocation = some value) →
    (∀ cell ∈ sharedCells, cell.location ≠ creatorLocation) →
    CodeValue depth environment dispatcher
      (.cellRef (OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation) →
    (∀ cell ∈ sharedCells, cell.location ≠ dispatcherLocation) → creatorLocation ≠ dispatcherLocation →
    CodeValue depth environment frame (CallTransportCorrespondence.requestValue request) →
    CodeValue depth environment gas (optionalWordValue (some request.gas)) →
    CodeValue depth environment code (WordMapping.encode (Memory.packBytes source.bytes)) →
    CodeValue depth environment size (.word (Word.ofNatModulo source.bytes.length)) →
    CodeValue depth environment known (.bool true) →
  ∀ {locations : AccountCallCorrespondence.SharedLocations},
    AccountCallCorrespondence.SharedReferences depth environment capture.shared locations →
    RuntimeLinkedWorldCorrespondence.StateRel anchors sharedState.world locations.world initial →
  ∀ {status : Semantics.Result Semantics.Value} {finalSource : Semantics.State RuntimeCallEffectsSemantics.State}
    {response : Semantics.Result AccountCallSemantics.Response},
    Semantics.EvalFunction source.functions (effects (some source.bytes)) source.entry []
      ⟨[], ChildFrameSemantics.initial parent request sharedState source.bytes⟩ status finalSource →
    ChildResultSemantics.Respond
      (ChildFrameSemantics.completedStatus status finalSource.external.runtime.runtime.runtime.runtime.runtime)
      finalSource.external.runtime.runtime.runtime.runtime.runtime response →
    ∃ target final, Core.Evaluates environment initial
      (AccountRuntime.allocateFrame (RuntimeExtendedInitializedEffects.slots true) capture.shared frame dispatcher creator gas code size known
        (fun values => bind (apply function (packet values)) AccountRuntime.childResult) depth) target final ∧
      CallTransportCorrespondence.ResponseRel response target ∧
      AccountCallCorrespondence.LinkedSharedStateRel anchors locations (RuntimeCallEffectsSemantics.shared finalSource.external) final ∧
      AccountCallCorrespondence.SharedFrame locations initial final

end Solcore.Frontend.RustHull.NestedChildCatalogExecutionCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.NestedChildCatalogRunCorrespondence
/-! A finite source child tree reaches the actual selected catalog closure.
The smaller-height frame theorem supplies execution, while refreshed captures
retain the real dispatcher for any nested call made by that child. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.NestedChildCatalogExecutionCorrespondence
open Core Correspondence ScalarExecution CodeBuilder
open RuntimeCallEffectsCorrespondence (Layout sharedLocations)
open AccountCallCorrespondence

theorem child_runs_preserves {sourceCatalog : ChildFrameSemantics.Catalog}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    {effects : Option (List UInt8) → Semantics.ExternalSemantics RuntimeCallEffectsSemantics.State}
    (connection : CatalogConnection sourceCatalog catalog anchors)
    (frameExecution : FrameExecution sourceCatalog catalog anchors effects)
    {fuel : Nat} {others : List Core.Expr}
    (compiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    {captured : Environment} {values : List Value} {closure : Value}
    (closures : CapturedClosures captured others values)
    {images : List (Nat × List UInt8)} {cells : List InitializedCell} {creatorLocation : Nat}
    {layout : Layout} {initial : Store}
    (capture : ObjectCallbackCapture (RuntimeExtendedInitializedEffects.slots true) (others.length + 1) images catalog
      (closure :: values) cells layout.dispatcher creatorLocation initial)
    (inventory : NestedChildCallbackContextCorrespondence.Inventory layout cells creatorLocation)
    (parent : RuntimeCallEffectsSemantics.State)
    (ambient : ∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
      ContractEnvironmentCorrespondence.initializedValue parent.runtime.runtime.runtime.runtime.environment cell) :
    ChildRunPreservation anchors (sharedLocations layout) capture.shared
      (RuntimeCatalogDispatchCorrespondence.runFrame (RuntimeExtendedInitializedEffects.slots true)
        (others.length + 1) capture.functions capture.shared capture.dispatcher capture.creator)
      (ChildFrameSemantics.Children sourceCatalog effects parent)
      (RuntimeChildCallEffectsCorrespondence.childReady layout
        (NestedChildCallbackContextCorrespondence.context inventory capture.closure))
      capture.depth capture.environment := by
  intro caller request initialShared response finalShared computed extra store extended precompiled sharedReferences argument related ready
  cases computed with
  | @executed caller request initialShared account source status finalSource response ordinary found selected known evaluated responded =>
    obtain ⟨index, expression, value, anchored, nonzero, first, accepted, eligible, capturedFrame, functionRelated⟩ :=
      selected_frame connection compiled closures capture.functionValues selected
    obtain ⟨accounts, actualAccount, sameWorld, links, worldRead, sourceFound, actualFound, code⟩ :=
      RuntimeLinkedWorldCorrespondence.selected related.linked anchored
    have sameAccount : actualAccount = account := Option.some.inj (sourceFound.symm.trans found)
    subst actualAccount
    let baseDepth := capture.depth + extra.length
    let baseEnvironment := extra ++ capture.environment
    let afterLookup := StorageCorrespondence.getStore accounts request.target initialShared.complete baseEnvironment store
    have retained : StoreRetains store afterLookup := StoreRetains.append _ _
    have afterReady := RuntimeChildCallEffectsCorrespondence.childReady_preserved
      (SharedFrame.ofRetains retained) ready
    obtain ⟨freshAccounts, creatorValue, freshWorld, _, stored, signature, separate, observed, creatorRead, creatorSeparate⟩ :=
      ChildCallbackContextCorrespondence.refresh_ready inventory.base afterReady.1 afterReady.2.1
        parent request initialShared source.bytes ambient (related.linked.retained retained) (related.shared.retained retained)
    let recordValue := StorageCorrespondence.record account (index + 2)
    let recordCode : Code := fun here => .var (here - baseDepth - 1)
    have recordRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment) recordCode recordValue :=
      CodeValue.bound baseDepth baseEnvironment recordValue
    have frameRelated := (childRequest_value argument).prepend [recordValue]
    have gasRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment)
        (present (part 5 8 (childRequest extended))) (optionalWordValue (some request.gas)) := by
      intro prefixValues current
      exact .inRight ((frameRelated.part (index := 5) rfl) prefixValues current)
    have codeRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment)
        (part 4 9 recordCode) (WordMapping.encode (Memory.packBytes source.bytes)) := by
      simpa only [StorageCorrespondence.record, known, Option.getD_some, List.length_cons, List.length_nil] using recordRelated.part (index := 4) rfl
    have sizeRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment)
        (part 5 9 recordCode) (.word (Word.ofNatModulo source.bytes.length)) := by
      simpa only [StorageCorrespondence.record, known, Option.getD_some, List.length_cons, List.length_nil] using recordRelated.part (index := 5) rfl
    have knownRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment)
        (part 6 9 recordCode) (.bool true) := by
      simpa only [StorageCorrespondence.record, known, Option.isSome_some, List.length_cons, List.length_nil] using recordRelated.part (index := 6) rfl
    have refreshedReferences := ChildFrameCorrespondence.refresh_references
      ((capture.references.prepend extra).prepend [recordValue]) afterLookup
    let refreshedCapture := NestedChildCallbackContextCorrespondence.refreshCapture capture afterLookup
      (NestedChildCallbackContextCorrespondence.dispatcher_read afterReady.2)
    have dispatcherSeparate : ∀ cell ∈ ChildFrameCorrespondence.refresh afterLookup cells,
        cell.location ≠ layout.dispatcher := by
      intro cell member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact inventory.dispatcherSeparate original present
    obtain ⟨target, final, invoked, resultRelated, finalRelated, frame⟩ :=
      frameExecution accepted eligible compiled connection closures refreshedCapture capturedFrame
        ((functionRelated.prepend extra).prepend [recordValue]) parent request initialShared freshWorld
        refreshedReferences signature stored separate observed
        ((capture.creatorValue.prepend extra).prepend [recordValue]) ⟨creatorValue, creatorRead⟩ creatorSeparate
        ((capture.dispatcherValue.prepend extra).prepend [recordValue]) dispatcherSeparate inventory.creatorDispatcher
        frameRelated gasRelated codeRelated sizeRelated knownRelated
        (sharedReferences.prepend [recordValue]) (related.linked.retained retained) evaluated responded
        (dispatcher := capture.dispatcher)
    have selectedRun := RuntimeCatalogDispatchCorrespondence.runFrame_evaluates first recordRelated invoked
    refine ⟨target, final, ?_, resultRelated, finalRelated, (SharedFrame.ofRetains retained).trans frame⟩
    exact accountRun_child_evaluates sharedReferences
      ((argument.part (index := 0) rfl).part (index := 0) rfl) worldRead related.shared.complete
      ordinary actualFound nonzero selectedRun

/-- The refreshed proof inventory does not replace the installed dispatcher;
this wrapper refers to the closure constructed by the real object initializer. -/
theorem captured_child_runs_preserves {sourceCatalog : ChildFrameSemantics.Catalog}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    {effects : Option (List UInt8) → Semantics.ExternalSemantics RuntimeCallEffectsSemantics.State}
    (connection : CatalogConnection sourceCatalog catalog anchors)
    (frameExecution : FrameExecution sourceCatalog catalog anchors effects)
    {fuel : Nat} {others : List Core.Expr}
    (compiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    {captured : Environment} {values : List Value} {closure : Value}
    (closures : CapturedClosures captured others values)
    {images : List (Nat × List UInt8)} {cells : List InitializedCell} {creatorLocation : Nat}
    {layout : Layout} {initial : Store}
    (capture : ObjectCallbackCapture (RuntimeExtendedInitializedEffects.slots true) (others.length + 1) images catalog
      (closure :: values) cells layout.dispatcher creatorLocation initial)
    (inventory : NestedChildCallbackContextCorrespondence.Inventory layout cells creatorLocation)
    (sharedReferences : SharedReferences capture.depth capture.environment capture.shared (sharedLocations layout))
    (parent : RuntimeCallEffectsSemantics.State)
    (ambient : ∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
      ContractEnvironmentCorrespondence.initializedValue parent.runtime.runtime.runtime.runtime.environment cell) :
    let dispatcher := ContractCallCorrespondence.captured_dispatcher capture (sharedLocations layout) sharedReferences
    ChildRunPreservation anchors (sharedLocations layout) dispatcher.shared dispatcher.runFrame
      (ChildFrameSemantics.Children sourceCatalog effects parent)
      (RuntimeChildCallEffectsCorrespondence.childReady layout
        (NestedChildCallbackContextCorrespondence.context inventory capture.closure))
      dispatcher.depth dispatcher.captured :=
  child_runs_preserves connection frameExecution compiled closures capture inventory parent ambient

end Solcore.Frontend.RustHull.NestedChildCatalogExecutionCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.NestedChildFrameInvokeCorrespondence
/-! A callable child frame uses the actual allocator and installed dispatcher.
The callback interface is discharged by induction on the independent call tree. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.NestedChildFrameCorrespondence
open Core Correspondence ScalarExecution CodeBuilder ChildFrameCorrespondence
open NestedChildCatalogExecutionCorrespondence (FrameExecution CatalogConnection)

/-- Internal callback interface, uniform over actual catalog captures and fresh
frame layouts. It is not a premise of the public execution theorem. -/
def CatalogCallbacks (sourceCatalog : ChildFrameSemantics.Catalog)
    (catalog : List AccountRuntime.CodeDefinition) (anchors : List CatalogWorldCorrespondence.Anchor)
    (children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children) : Prop :=
  ∀ {fuel : Nat} {others : List Core.Expr},
    ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others →
    CatalogConnection sourceCatalog catalog anchors →
  ∀ {captured : Environment} {catalogValues : List Value} {rootClosure : Value},
    CapturedClosures captured others catalogValues →
  ∀ {images : List (Nat × List UInt8)} {cells : List InitializedCell} {creator : Nat}
    {layout : RuntimeCallEffectsCorrespondence.Layout} {initial : Store},
    (capture : ObjectCallbackCapture (RuntimeExtendedInitializedEffects.slots true) (others.length + 1) images catalog
      (rootClosure :: catalogValues) cells layout.dispatcher creator initial) →
    (inventory : NestedChildCallbackContextCorrespondence.Inventory layout cells creator) →
    (references : AccountCallCorrespondence.SharedReferences capture.depth capture.environment capture.shared
      (RuntimeCallEffectsCorrespondence.sharedLocations layout)) →
    (parent : RuntimeCallEffectsSemantics.State) →
    (∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
      ContractEnvironmentCorrespondence.initializedValue parent.runtime.runtime.runtime.runtime.environment cell) →
    let dispatcher := ContractCallCorrespondence.captured_dispatcher capture _ references
    AccountCallCorrespondence.ChildRunPreservation anchors (RuntimeCallEffectsCorrespondence.sharedLocations layout)
      dispatcher.shared dispatcher.runFrame (children parent)
      (RuntimeChildCallEffectsCorrespondence.childReady layout
        (NestedChildCallbackContextCorrespondence.context inventory capture.closure)) dispatcher.depth dispatcher.captured

theorem frame_execution_of_callbacks {sourceCatalog : ChildFrameSemantics.Catalog}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    {children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children}
    (callbacks : CatalogCallbacks sourceCatalog catalog anchors children) :
    FrameExecution sourceCatalog catalog anchors (RuntimeCallEffectsSemantics.effectsWith children) := by
  intro source fuel compiled others accepted eligible catalogCompiled connection captured catalogValues rootClosure catalogCaptured
    images sharedCells dispatcherLocation creatorLocation initial capture depth environment frame dispatcher creator gas code size known function closure
    closureRelated resolved parent request sharedState accounts world references signature initialized separate observed
    creatorRelated creatorFound creatorSeparate dispatcherRelated dispatcherSeparate creatorDispatcher
    frameRelated gasRelated codeRelated sizeRelated knownRelated locations sharedReferences linked status finalSource response evaluated responded
  obtain ⟨creatorValue, creatorRead⟩ := creatorFound
  apply allocateCallFrame_initializes parent request sharedState source.bytes world references signature initialized separate observed
    creatorRelated creatorRead creatorSeparate dispatcherRelated capture.stored dispatcherSeparate creatorDispatcher
    frameRelated gasRelated codeRelated sizeRelated knownRelated
    (fun values => bind (apply function (packet values)) AccountRuntime.childResult)
    (fun target final => CallTransportCorrespondence.ResponseRel response target ∧
      AccountCallCorrespondence.LinkedSharedStateRel anchors locations (RuntimeCallEffectsSemantics.shared finalSource.external) final ∧
      AccountCallCorrespondence.SharedFrame locations initial final)
  intro extra suffix cells values valuesRelated stored cellsSignature allSeparate origins sharedOrigins ready
  let inventory := ready.nestedInventory dispatcherSeparate creatorDispatcher
  let capture' := NestedChildCallbackContextCorrespondence.withDispatcher capture _ ready.call.dispatcherEqual
  have capturedReferences := ContractChildCallCorrespondence.inventory_references inventory.base capture'.references
  let dispatchCapture := ContractCallCorrespondence.captured_dispatcher capture' _ capturedReferences
  let handlers := ready.handlers dispatchCapture
  let callbackContext := NestedChildCallbackContextCorrespondence.context inventory capture.closure
  have initialBase := ready.related dispatchCapture
  have locationsEqual : RuntimeCallEffectsCorrespondence.sharedLocations ready.call.layout = locations :=
    shared_references_unique (ContractChildCallCorrespondence.inventory_references inventory.base references) sharedReferences
  have initialLinked : RuntimeLinkedWorldCorrespondence.StateRel anchors sharedState.world ready.call.layout.storage.world (initial ++ suffix) := by
    have same := congrArg AccountCallCorrespondence.SharedLocations.world locationsEqual
    change ready.call.layout.storage.world = locations.world at same
    rw [same]
    exact linked.retained (StoreRetains.append initial suffix)
  have initialState := RuntimeChildCallEffectsCorrespondence.of_base initialBase initialLinked
    (ready.nestedCaptured dispatcherSeparate creatorDispatcher)
  let slots := cells.map InitializedCell.effectSlot
  have slotTypes : RuntimeChildCallEffectsFrameCorrespondence.slotTypes slots = RuntimeExtendedInitializedEffects.slots true := by
    simpa only [RuntimeChildCallEffectsFrameCorrespondence.slotTypes, RuntimeReturnDataEffectsFrameCorrespondence.slotTypes,
      RuntimeLogEffectsFrameCorrespondence.slotTypes, MemoryFrameCorrespondence.slotTypes, slots, List.map_map,
      Function.comp_def, InitializedCell.effectSlot] using cellsSignature
  have environmentRelated := initialized_environment cells (RuntimeExtendedInitializedEffects.initialized_unique cellsSignature)
    (Value.unit :: bundleValues (cells.map InitializedCell.reference) :: captured)
  have runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (RuntimeChildCallEffectsFrameCorrespondence.slotTypes slots)) Renaming.id
      ((cells.map InitializedCell.reference).reverse ++ Value.unit :: bundleValues (cells.map InitializedCell.reference) :: captured) := by
    simpa only [RuntimeChildCallEffectsFrameCorrespondence.slotTypes, RuntimeReturnDataEffectsFrameCorrespondence.slotTypes,
      RuntimeLogEffectsFrameCorrespondence.slotTypes, MemoryFrameCorrespondence.slotTypes, slots, List.map_map,
      Function.comp_def, InitializedCell.effectSlot] using environmentRelated
  have member : ∀ slot ∈ RuntimeCallInitializedEffects.baseSlots ready.call.layout.toReturnDataLayout, slot ∈ slots := by
    simpa only [ready.call.baseEqual] using ready.base.members
  have callCodes : ∀ imageCells, ready.call.layout.toReturnDataLayout.codeCells = some imageCells →
      (⟨"code", WordMapping.type, imageCells.code⟩ : EffectSlot) ∈ slots ∧
      (⟨"codeKnown", .bool, imageCells.known⟩ : EffectSlot) ∈ slots := by
    rw [ready.call.baseEqual]
    exact ready.base.codes
  have bodyCallbacks : ∀ {world state current},
      StateRel (RuntimeChildCallEffectsCorrespondence.model ready.call.layout
        (prefixRead ready.call.layout.boundary (initial ++ suffix)) slots (some source.bytes) handlers anchors callbackContext)
        world state current →
      RuntimeChildCallEffectsCorrespondence.CallbackPreservation ready.call.layout handlers anchors callbackContext children state.external := by
    intro world state current related
    have base := RuntimeChildCallEffectsCorrespondence.base_related related
    have ambient := ChildCallbackContextCorrespondence.parent_observed inventory.base ready.sharedMembers base related.external.2.2.1.2.1
    apply RuntimeChildCallEffectsCorrespondence.callback_preserves
    · exact RuntimeCallEffectsCorrespondence.source_eq base
    · exact callbacks catalogCompiled connection catalogCaptured capture' inventory capturedReferences state.external ambient
  obtain ⟨extension, statusValue, accounts', bodyStore, represented, statusRelated, called, state, _⟩ :=
    RuntimeChildCallEffectsFrameCorrespondence.compileFrame_call_preserves_observed (withCode := true)
      (by simpa only [slotTypes] using accepted)
      (by simpa only [ContractChildCallCorrespondence.supported_actual slotTypes, ChildFrameSemantics.Code.functions,
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
      ready.call.depthMember ready.call.handlerMember initialState
      (by simpa only [ready.call.baseEqual] using ready.base.passive) ready.callPassive bodyCallbacks evaluated
  have finalShared := ready.linked_shared_state state
  have retained := ready.parent_frame origins state
  rw [locationsEqual] at finalShared retained
  obtain ⟨target, final, resultRelated, executed, extractionRetains⟩ := bind_evaluates statusRelated represented responded called
  exact ⟨target, final, executed, resultRelated, finalShared.retained extractionRetains,
    retained.trans (AccountCallCorrespondence.SharedFrame.ofRetains extractionRetains)⟩

end Solcore.Frontend.RustHull.NestedChildFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.NestedChildFrameCorrespondence
/-! Finite source call trees determine actual compiled child execution. The
induction counts source child frames independently of Core evaluation fuel. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.NestedChildFrameCorrespondence
open NestedChildCatalogExecutionCorrespondence

theorem frame_execution (sourceCatalog : ChildFrameSemantics.Catalog)
    (catalog : List AccountRuntime.CodeDefinition) (anchors : List CatalogWorldCorrespondence.Anchor)
    (height : Nat) : FrameExecution sourceCatalog catalog anchors (ChildFrameSemantics.effectsAt sourceCatalog height) := by
  induction height with
  | zero =>
      apply frame_execution_of_callbacks
      intro fuel others compiled connection captured values closure closures images cells creator layout initial capture
        inventory references parent ambient
      dsimp only
      intro caller request shared response final impossible
      cases impossible
  | succ height induction =>
      apply frame_execution_of_callbacks
      intro fuel others compiled connection captured values closure closures images cells creator layout initial capture
        inventory references parent ambient
      exact captured_child_runs_preserves connection induction compiled closures capture inventory references parent ambient

end Solcore.Frontend.RustHull.NestedChildFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RootChildCatalogExecutionCorrespondence
/-! Root reentry selects the actual packet-head closure. Its compilation and
capture are structural inputs to the finite-height frame induction, alongside
compiled catalog entries; none assumes that the root executes correctly. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RootChildCatalogExecutionCorrespondence
open Core Correspondence ScalarExecution CodeBuilder

/-- The real root frame, compiled and captured in the same environment as the
catalog closures. This evidence is unchanged when shared runtime cells change. -/
def RootFrame (rootSource : ChildFrameSemantics.Code) (fuel : Nat)
    (captured : Environment) (closure : Value) : Prop :=
  ∃ expression,
    AccountRuntime.compileFrame rootSource.program rootSource.body (RuntimeExtendedInitializedEffects.slots true) fuel = .ok expression ∧
    DerivationCorrespondence.ExecutableProgram (ContractCallModeCorrespondence.supported true) rootSource.functions ∧
    CapturedClosure expression captured closure

/-- A source selection either refers to the root's executable identity one,
or to one of the actual catalog identities after it. Both branches retain the
selected address's exact byte image through the same account anchor. -/
def CatalogConnection (rootSource : ChildFrameSemantics.Code) (sourceCatalog : ChildFrameSemantics.Catalog)
    (catalog : List AccountRuntime.CodeDefinition) (anchors : List CatalogWorldCorrespondence.Anchor) : Prop :=
  ∀ address source, ChildFrameSemantics.select sourceCatalog address = some source →
    (source = rootSource ∧ CatalogWorldCorrespondence.Anchor.mk address rootSource.bytes 1 ∈ anchors) ∨
    ∃ index definition, catalog[index]? = some definition ∧ source.program = definition.program ∧
      AccountRuntime.select definition.program.objects definition.path = .ok source.body ∧
      source.bytes = definition.bytes ∧
      CatalogWorldCorrespondence.Anchor.mk address source.bytes (index + 2) ∈ anchors ∧
      Word.ofNatModulo (index + 2) ≠ Word.zero ∧
      (List.range (catalog.length + 1)).find?
        (fun candidate => Word.ofNatModulo (index + 2) == Word.ofNatModulo (candidate + 1)) = some (index + 1) ∧
      DerivationCorrespondence.ExecutableProgram (ContractCallModeCorrespondence.supported true) source.functions

/-- Existing catalog-only links remain valid without adding a root entry. -/
theorem CatalogConnection.of_catalog {rootSource : ChildFrameSemantics.Code}
    {sourceCatalog : ChildFrameSemantics.Catalog} {catalog : List AccountRuntime.CodeDefinition}
    {anchors : List CatalogWorldCorrespondence.Anchor}
    (connected : ModeChildCatalogExecutionCorrespondence.CatalogConnection sourceCatalog catalog anchors) :
    CatalogConnection rootSource sourceCatalog catalog anchors :=
  fun address source selected => .inr (connected address source selected)

theorem selected_frame {rootSource : ChildFrameSemantics.Code} {sourceCatalog : ChildFrameSemantics.Catalog}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    (connection : CatalogConnection rootSource sourceCatalog catalog anchors)
    {fuel : Nat} {others : List Core.Expr}
    (compiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    {captured environment : Environment} {values : List Value} {closure : Value} {depth : Nat} {functions : Code}
    (closures : CapturedClosures captured others values)
    (root : RootFrame rootSource fuel captured closure)
    (functionsRelated : CodeValue depth environment functions (bundleValues (closure :: values)))
    {address : Word} {source : ChildFrameSemantics.Code}
    (selected : ChildFrameSemantics.select sourceCatalog address = some source) :
    ∃ index expression value,
      CatalogWorldCorrespondence.Anchor.mk address source.bytes (index + 1) ∈ anchors ∧
      Word.ofNatModulo (index + 1) ≠ Word.zero ∧
      (List.range (others.length + 1)).find?
        (fun candidate => Word.ofNatModulo (index + 1) == Word.ofNatModulo (candidate + 1)) = some index ∧
      AccountRuntime.compileFrame source.program source.body (RuntimeExtendedInitializedEffects.slots true) fuel = .ok expression ∧
      DerivationCorrespondence.ExecutableProgram (ContractCallModeCorrespondence.supported true) source.functions ∧
      CapturedClosure expression captured value ∧
      CodeValue depth environment (part index (others.length + 1) functions) value := by
  rcases connection address source selected with ⟨rfl, anchored⟩ | linked
  · obtain ⟨expression, accepted, eligible, capturedRoot⟩ := root
    refine ⟨0, expression, closure, anchored, ?_, ?_, accepted, eligible, capturedRoot,
      ContractCatalogCorrespondence.entry_reference closures functionsRelated⟩
    · decide +kernel
    · simp only [List.range_succ_eq_map, List.find?_cons, beq_self_eq_true]
  · obtain ⟨index, definition, found, program, body, _, anchored, nonzero, first, eligible⟩ := linked
    obtain ⟨code, expression, value, codeSelected, accepted, capturedFrame, referenced⟩ :=
      ContractCatalogCorrespondence.catalog_reference compiled closures functionsRelated found
    have same : code = source.body := Except.ok.inj (codeSelected.symm.trans body)
    subst code
    refine ⟨index + 1, expression, value, anchored, nonzero, ?_, ?_, eligible, capturedFrame, referenced⟩
    · simpa only [compiled.length] using first
    · simpa only [program] using accepted

/-- Internal induction interface for one actual compiled frame invocation.
Every closure, reference and current shared read comes from the real object
capture and allocator; only the finite source derivation varies with height. -/
def FrameExecution (rootSource : ChildFrameSemantics.Code) (sourceCatalog : ChildFrameSemantics.Catalog)
    (catalog : List AccountRuntime.CodeDefinition) (anchors : List CatalogWorldCorrespondence.Anchor)
    (effects : Option (List UInt8) → Semantics.ExternalSemantics RuntimeCallModeSemantics.State) : Prop :=
  ∀ {source : ChildFrameSemantics.Code} {fuel : Nat} {compiled : Core.Expr} {others : List Core.Expr},
    AccountRuntime.compileFrame source.program source.body (RuntimeExtendedInitializedEffects.slots true) fuel = .ok compiled →
    DerivationCorrespondence.ExecutableProgram (ContractCallModeCorrespondence.supported true) source.functions →
    ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others →
    CatalogConnection rootSource sourceCatalog catalog anchors →
  ∀ {captured : Environment} {catalogValues : List Value} {rootClosure : Value},
    CapturedClosures captured others catalogValues →
    RootFrame rootSource fuel captured rootClosure →
  ∀ {images : List (Nat × List UInt8)} {sharedCells : List InitializedCell}
    {dispatcherLocation creatorLocation : Nat} {initial : Store},
    (capture : ObjectCallbackCapture (RuntimeExtendedInitializedEffects.slots true) (others.length + 1) images catalog
      (rootClosure :: catalogValues) sharedCells dispatcherLocation creatorLocation initial) →
  ∀ {depth : Nat} {environment : Environment} {frame dispatcher creator gas code size known function : Code} {closure : Value},
    CapturedClosure compiled captured closure →
    CodeValue depth environment function closure →
    (parent : RuntimeCallModeSemantics.State) → (request : AccountCallSemantics.Request) →
    (sharedState : AccountCallSemantics.Shared) →
  ∀ {accounts : StorageCorrespondence.Accounts}, accounts.map Prod.fst = sharedState.world →
    RuntimeReferences depth environment capture.shared sharedCells →
    sharedCells.map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse →
    InitializedCells sharedCells initial → CellLocations sharedCells →
    (∀ cell ∈ sharedCells, ChildFrameCorrespondence.Observed accounts
      (ChildFrameCorrespondence.Initial parent request sharedState source.bytes) source.bytes cell) →
    CodeValue depth environment creator (.cellRef (OptionalCell.cellType Creation.callbackType) creatorLocation) →
    (∃ value, initial.read? creatorLocation = some value) →
    (∀ cell ∈ sharedCells, cell.location ≠ creatorLocation) →
    CodeValue depth environment dispatcher
      (.cellRef (OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation) →
    (∀ cell ∈ sharedCells, cell.location ≠ dispatcherLocation) → creatorLocation ≠ dispatcherLocation →
    CodeValue depth environment frame (CallTransportCorrespondence.requestValue request) →
    CodeValue depth environment gas (optionalWordValue (some request.gas)) →
    CodeValue depth environment code (WordMapping.encode (Memory.packBytes source.bytes)) →
    CodeValue depth environment size (.word (Word.ofNatModulo source.bytes.length)) →
    CodeValue depth environment known (.bool true) →
  ∀ {locations : AccountCallCorrespondence.SharedLocations},
    AccountCallCorrespondence.SharedReferences depth environment capture.shared locations →
    RuntimeLinkedWorldCorrespondence.StateRel anchors sharedState.world locations.world initial →
  ∀ {createValue : Value}, initial.read? creatorLocation = some (.inRight .unit createValue) →
    CreationCorrespondence.HandlerClosure locations createValue →
  ∀ {status : Semantics.Result Semantics.Value} {finalSource : Semantics.State RuntimeCallModeSemantics.State}
    {response : Semantics.Result AccountCallSemantics.Response},
    Semantics.EvalFunction source.functions (effects (some source.bytes)) source.entry []
      ⟨[], ChildFrameSemantics.initial parent request sharedState source.bytes⟩ status finalSource →
    ChildResultSemantics.Respond
      (ChildFrameSemantics.completedStatus status finalSource.external.runtime.runtime.runtime.runtime.runtime)
      finalSource.external.runtime.runtime.runtime.runtime.runtime response →
    ∃ target final, Core.Evaluates environment initial
      (AccountRuntime.allocateFrame (RuntimeExtendedInitializedEffects.slots true) capture.shared frame dispatcher creator gas code size known
        (fun values => bind (apply function (packet values)) AccountRuntime.childResult) depth) target final ∧
      CallTransportCorrespondence.ResponseRel response target ∧
      AccountCallCorrespondence.LinkedSharedStateRel anchors locations (RuntimeCallModeSemantics.shared finalSource.external) final ∧
      AccountCallCorrespondence.SharedFrame locations initial final


end Solcore.Frontend.RustHull.RootChildCatalogExecutionCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RootChildCatalogRunCorrespondence
/-! Source child execution selects either the original root closure or a
catalog closure. Refreshing mutable shared values preserves the structural
root evidence and the actual dispatcher, including delegated execution modes. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RootChildCatalogExecutionCorrespondence
open Core Correspondence ScalarExecution CodeBuilder
open RuntimeCallEffectsCorrespondence (Layout sharedLocations)
open AccountCallCorrespondence hiding ChildRunPreservation childRequest_value
open AccountCallModeCorrespondence (ChildRunPreservation childRequest_value)

theorem child_runs_preserves {rootSource : ChildFrameSemantics.Code} {sourceCatalog : ChildFrameSemantics.Catalog}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    {effects : Option (List UInt8) → Semantics.ExternalSemantics RuntimeCallModeSemantics.State}
    (connection : CatalogConnection rootSource sourceCatalog catalog anchors)
    (frameExecution : FrameExecution rootSource sourceCatalog catalog anchors effects)
    {fuel : Nat} {others : List Core.Expr}
    (compiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    {captured : Environment} {values : List Value} {closure : Value}
    (closures : CapturedClosures captured others values)
    (root : RootFrame rootSource fuel captured closure)
    {images : List (Nat × List UInt8)} {cells : List InitializedCell} {creatorLocation : Nat}
    {layout : Layout} {initial : Store}
    (capture : ObjectCallbackCapture (RuntimeExtendedInitializedEffects.slots true) (others.length + 1) images catalog
      (closure :: values) cells layout.dispatcher creatorLocation initial)
    (inventory : NestedChildCallbackContextCorrespondence.Inventory layout cells creatorLocation)
    (create : RuntimeCallModeEffectsCorrespondence.CreateHandler layout) (createAt : create.location = creatorLocation)
    (mode : AccountCallSemantics.Mode) (parent : RuntimeCallModeSemantics.State)
    (ambient : ∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
      ContractEnvironmentCorrespondence.initializedValue parent.runtime.runtime.runtime.runtime.environment cell) :
    ChildRunPreservation mode anchors (sharedLocations layout) capture.shared
      (RuntimeCatalogDispatchCorrespondence.runFrame (RuntimeExtendedInitializedEffects.slots true)
        (others.length + 1) capture.functions capture.shared capture.dispatcher capture.creator)
      (ChildFrameModeSemantics.Children sourceCatalog effects parent)
      (RuntimeChildCallEffectsCorrespondence.childReady layout
        (create.context (NestedChildCallbackContextCorrespondence.context inventory capture.closure)))
      capture.depth capture.environment := by
  intro caller request initialShared response finalShared computed extra store extended precompiled sharedReferences argument related ready
  cases computed with
  | @executed _ caller request initialShared account source status finalSource response ordinary found selected known evaluated responded =>
    obtain ⟨index, expression, value, anchored, nonzero, first, accepted, eligible, capturedFrame, functionRelated⟩ :=
      selected_frame connection compiled closures root capture.functionValues selected
    obtain ⟨accounts, actualAccount, sameWorld, links, worldRead, sourceFound, actualFound, code⟩ :=
      RuntimeLinkedWorldCorrespondence.selected related.linked anchored
    have sameAccount : actualAccount = account := Option.some.inj (sourceFound.symm.trans found)
    subst actualAccount
    let baseDepth := capture.depth + extra.length
    let baseEnvironment := extra ++ capture.environment
    let afterLookup := StorageCorrespondence.getStore accounts request.target initialShared.complete baseEnvironment store
    have retained : StoreRetains store afterLookup := StoreRetains.append _ _
    have afterReady := RuntimeChildCallEffectsCorrespondence.childReady_preserved
      (SharedFrame.ofRetains retained) ready
    obtain ⟨freshAccounts, creatorValue, freshWorld, _, stored, signature, separate, observed, creatorRead, creatorSeparate⟩ :=
      ChildCallbackContextCorrespondence.refresh_ready inventory.base afterReady.1 afterReady.2.1.1
        parent (ChildFrameModeSemantics.executionRequest mode caller request) initialShared source.bytes ambient (related.linked.retained retained) (related.shared.retained retained)
    let recordValue := StorageCorrespondence.record account (index + 1)
    let recordCode : Code := fun here => .var (here - baseDepth - 1)
    have recordRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment) recordCode recordValue :=
      CodeValue.bound baseDepth baseEnvironment recordValue
    have frameRelated := (childRequest_value argument).prepend [recordValue]
    have gasRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment)
        (present (part 5 8 (childRequest extended))) (optionalWordValue (some request.gas)) := by
      intro prefixValues current
      exact .inRight ((frameRelated.part (index := 5) rfl) prefixValues current)
    have codeRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment)
        (part 4 9 recordCode) (WordMapping.encode (Memory.packBytes source.bytes)) := by
      simpa only [StorageCorrespondence.record, known, Option.getD_some, List.length_cons, List.length_nil] using recordRelated.part (index := 4) rfl
    have sizeRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment)
        (part 5 9 recordCode) (.word (Word.ofNatModulo source.bytes.length)) := by
      simpa only [StorageCorrespondence.record, known, Option.getD_some, List.length_cons, List.length_nil] using recordRelated.part (index := 5) rfl
    have knownRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment)
        (part 6 9 recordCode) (.bool true) := by
      simpa only [StorageCorrespondence.record, known, Option.isSome_some, List.length_cons, List.length_nil] using recordRelated.part (index := 6) rfl
    have createRead : afterLookup.read? creatorLocation = some (.inRight .unit create.value) := by
      rw [← createAt]
      simpa only [prefixRead, create.below, ↓reduceIte] using afterReady.2.2
    have refreshedReferences := ChildFrameCorrespondence.refresh_references
      ((capture.references.prepend extra).prepend [recordValue]) afterLookup
    let refreshedCapture := NestedChildCallbackContextCorrespondence.refreshCapture capture afterLookup
      (NestedChildCallbackContextCorrespondence.dispatcher_read afterReady.2.1)
    have dispatcherSeparate : ∀ cell ∈ ChildFrameCorrespondence.refresh afterLookup cells,
        cell.location ≠ layout.dispatcher := by
      intro cell member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact inventory.dispatcherSeparate original present
    obtain ⟨target, final, invoked, resultRelated, finalRelated, frame⟩ :=
      frameExecution accepted eligible compiled connection closures root refreshedCapture capturedFrame
        ((functionRelated.prepend extra).prepend [recordValue]) parent (ChildFrameModeSemantics.executionRequest mode caller request) initialShared freshWorld
        refreshedReferences signature stored separate observed
        ((capture.creatorValue.prepend extra).prepend [recordValue]) ⟨creatorValue, creatorRead⟩ creatorSeparate
        ((capture.dispatcherValue.prepend extra).prepend [recordValue]) dispatcherSeparate inventory.creatorDispatcher
        frameRelated gasRelated codeRelated sizeRelated knownRelated
        (sharedReferences.prepend [recordValue]) (related.linked.retained retained) createRead create.closure
        evaluated responded (dispatcher := capture.dispatcher)
    have selectedRun := RuntimeCatalogDispatchCorrespondence.runFrame_evaluates first recordRelated invoked
    refine ⟨target, final, ?_, resultRelated, finalRelated, (SharedFrame.ofRetains retained).trans frame⟩
    exact accountRun_child_evaluates sharedReferences
      ((argument.part (index := 0) rfl).part (index := 0) rfl) worldRead related.shared.complete
      ordinary actualFound nonzero selectedRun

/-- The refreshed proof inventory does not replace the installed dispatcher;
this wrapper refers to the closure constructed by the real object initializer. -/
theorem captured_child_runs_preserves {rootSource : ChildFrameSemantics.Code} {sourceCatalog : ChildFrameSemantics.Catalog}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    {effects : Option (List UInt8) → Semantics.ExternalSemantics RuntimeCallModeSemantics.State}
    (connection : CatalogConnection rootSource sourceCatalog catalog anchors)
    (frameExecution : FrameExecution rootSource sourceCatalog catalog anchors effects)
    {fuel : Nat} {others : List Core.Expr}
    (compiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    {captured : Environment} {values : List Value} {closure : Value}
    (closures : CapturedClosures captured others values)
    (root : RootFrame rootSource fuel captured closure)
    {images : List (Nat × List UInt8)} {cells : List InitializedCell} {creatorLocation : Nat}
    {layout : Layout} {initial : Store}
    (capture : ObjectCallbackCapture (RuntimeExtendedInitializedEffects.slots true) (others.length + 1) images catalog
      (closure :: values) cells layout.dispatcher creatorLocation initial)
    (inventory : NestedChildCallbackContextCorrespondence.Inventory layout cells creatorLocation)
    (sharedReferences : SharedReferences capture.depth capture.environment capture.shared (sharedLocations layout))
    (create : RuntimeCallModeEffectsCorrespondence.CreateHandler layout) (createAt : create.location = creatorLocation)
    (mode : AccountCallSemantics.Mode) (parent : RuntimeCallModeSemantics.State)
    (ambient : ∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
      ContractEnvironmentCorrespondence.initializedValue parent.runtime.runtime.runtime.runtime.environment cell) :
    let dispatcher := ContractCallCorrespondence.captured_dispatcher capture (sharedLocations layout) sharedReferences
    ChildRunPreservation mode anchors (sharedLocations layout) dispatcher.shared dispatcher.runFrame
      (ChildFrameModeSemantics.Children sourceCatalog effects parent)
      (RuntimeChildCallEffectsCorrespondence.childReady layout
        (create.context (NestedChildCallbackContextCorrespondence.context inventory capture.closure)))
      dispatcher.depth dispatcher.captured :=
  child_runs_preserves connection frameExecution compiled closures root capture inventory create createAt mode parent ambient

end Solcore.Frontend.RustHull.RootChildCatalogExecutionCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RootChildFrameInvokeCorrespondence
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
    (create : RuntimeCallModeEffectsCorrespondence.CreateHandler layout) → create.location = creator →
    (mode : AccountCallSemantics.Mode) → (parent : RuntimeCallEffectsSemantics.State) →
    (∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
      ContractEnvironmentCorrespondence.initializedValue parent.runtime.runtime.runtime.runtime.environment cell) →
    let dispatcher := ContractCallCorrespondence.captured_dispatcher capture _ references
    AccountCallModeCorrespondence.ChildRunPreservation mode anchors (RuntimeCallEffectsCorrespondence.sharedLocations layout)
      dispatcher.shared dispatcher.runFrame (children parent)
      (RuntimeChildCallEffectsCorrespondence.childReady layout
        (create.context (NestedChildCallbackContextCorrespondence.context inventory capture.closure)))
      dispatcher.depth dispatcher.captured

theorem frame_execution_of_callbacks {rootSource : ChildFrameSemantics.Code} {sourceCatalog : ChildFrameSemantics.Catalog}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    {children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children}
    (callbacks : CatalogCallbacks rootSource sourceCatalog catalog anchors children) :
    FrameExecution rootSource sourceCatalog catalog anchors (RuntimeCallModeSemantics.effectsWith children) := by
  intro source fuel compiled others accepted eligible catalogCompiled connection captured catalogValues rootClosure catalogCaptured rootCaptured
    images sharedCells dispatcherLocation creatorLocation initial capture depth environment frame dispatcher creator gas code size known function closure
    closureRelated resolved parent request sharedState accounts world references signature initialized separate observed
    creatorRelated creatorFound creatorSeparate dispatcherRelated dispatcherSeparate creatorDispatcher
    frameRelated gasRelated codeRelated sizeRelated knownRelated locations sharedReferences linked createValue createRead createClosure
    status finalSource response evaluated responded
  obtain ⟨creatorValue, creatorRead⟩ := creatorFound
  apply ChildFrameModeCorrespondence.allocateModeCallFrame_initializes parent request sharedState source.bytes world references signature initialized separate observed
    creatorRelated creatorRead creatorSeparate dispatcherRelated capture.stored dispatcherSeparate creatorDispatcher
    frameRelated gasRelated codeRelated sizeRelated knownRelated
    (fun values => bind (apply function (packet values)) AccountRuntime.childResult)
    (fun target final => CallTransportCorrespondence.ResponseRel response target ∧
      AccountCallCorrespondence.LinkedSharedStateRel anchors locations (RuntimeCallEffectsSemantics.shared finalSource.external) final ∧
      AccountCallCorrespondence.SharedFrame locations initial final)
  intro extra suffix cells values valuesRelated stored cellsSignature allSeparate origins sharedOrigins creatorMember modeReady
  let ready := modeReady.base
  let inventory := ready.nestedInventory dispatcherSeparate creatorDispatcher
  let capture' := NestedChildCallbackContextCorrespondence.withDispatcher capture _ ready.call.dispatcherEqual
  have capturedReferences := ContractChildCallCorrespondence.inventory_references inventory.base capture'.references
  let dispatchCapture := ContractCallCorrespondence.captured_dispatcher capture' _ capturedReferences
  let callbackContext := NestedChildCallbackContextCorrespondence.context inventory capture.closure
  have locationsEqual : RuntimeCallEffectsCorrespondence.sharedLocations ready.call.layout = locations :=
    shared_references_unique (ContractChildCallCorrespondence.inventory_references inventory.base references) sharedReferences
  let childCreate : RuntimeCallModeEffectsCorrespondence.CreateHandler ready.call.layout := {
    location := creatorLocation
    below := inventory.creatorBelow
    outside := inventory.creatorOutside
    value := createValue
    closure := by rw [locationsEqual]; exact createClosure }
  let handlers := modeReady.handlers dispatchCapture childCreate
  have initialLinked : RuntimeLinkedWorldCorrespondence.StateRel anchors sharedState.world ready.call.layout.storage.world (initial ++ suffix) := by
    have same := congrArg AccountCallCorrespondence.SharedLocations.world locationsEqual
    change ready.call.layout.storage.world = locations.world at same
    rw [same]
    exact linked.retained (StoreRetains.append initial suffix)
  have childCreateRead : (initial ++ suffix).read? childCreate.location = some (.inRight .unit childCreate.value) := by
    change (initial ++ suffix).read? creatorLocation = some (.inRight .unit createValue)
    simpa only [Store.read?, List.getElem?_append_left (List.getElem?_eq_some_iff.mp createRead).1] using createRead
  have initialState := modeReady.related dispatchCapture childCreate childCreateRead callbackContext initialLinked
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
        (callbacks catalogCompiled connection catalogCaptured rootCaptured capture' inventory capturedReferences childCreate rfl
          operation.mode state.external ambient)
        (fun _ valid => ⟨valid.1, valid.2.1, valid.2.2.2.2⟩)
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
      (slot_present "callvalue" .word (by simp [RuntimeExtendedInitializedEffects.slots, Effects.slots]))
      ⟨creatorMember, slot_present "availableGas" (.sum .unit .word) (by simp [RuntimeExtendedInitializedEffects.slots, Effects.slots])⟩
      initialState
      (by simpa only [ready.call.baseEqual] using ready.base.passive) ready.callPassive bodyCallbacks evaluated
  have finalShared := ready.linked_shared_state state
  have retained := ready.parent_frame origins state
  rw [locationsEqual] at finalShared retained
  obtain ⟨target, final, resultRelated, executed, extractionRetains⟩ := bind_evaluates statusRelated represented responded called
  exact ⟨target, final, executed, resultRelated, finalShared.retained extractionRetains,
    retained.trans (AccountCallCorrespondence.SharedFrame.ofRetains extractionRetains)⟩

end Solcore.Frontend.RustHull.RootChildFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RootChildFrameCorrespondence
/-! Finite source call trees determine actual compiled child execution. The
induction counts source child frames independently of Core evaluation fuel. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RootChildFrameCorrespondence
open RootChildCatalogExecutionCorrespondence

theorem frame_execution (rootSource : ChildFrameSemantics.Code) (sourceCatalog : ChildFrameSemantics.Catalog)
    {initCatalog : ChildFrameSemantics.InitCatalog}
    (catalog : List AccountRuntime.CodeDefinition) (anchors : List CatalogWorldCorrespondence.Anchor)
    (height : Nat) : FrameExecution rootSource sourceCatalog catalog anchors (ChildFrameModeSemantics.effectsAt sourceCatalog initCatalog height) := by
  induction height with
  | zero =>
      apply frame_execution_of_callbacks
      intro fuel others compiled connection captured values closure closures rootCaptured images cells creator layout initial capture
        inventory references create createAt mode parent ambient
      dsimp only
      intro caller request shared response final impossible
      cases impossible
  | succ height induction =>
      apply frame_execution_of_callbacks
      intro fuel others compiled connection captured values closure closures rootCaptured images cells creator layout initial capture
        inventory references create createAt mode parent ambient
      exact captured_child_runs_preserves connection induction compiled closures rootCaptured capture inventory references create createAt
        mode parent ambient

end Solcore.Frontend.RustHull.RootChildFrameCorrespondence
end
