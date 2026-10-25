import Solcore.Frontend.RustHull.ChildFrameCallStateFrameCorrespondence
import Solcore.Frontend.RustHull.RuntimeCallModeStateCorrespondence
import Solcore.Frontend.RustHull.ChildFrameModeSemantics

/-! Fresh frame allocation captures the execution address in every call-mode
handler. Their concrete cells remain outside the mutable frame resources. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildFrameModeCorrespondence
open Core Correspondence ScalarExecution CodeBuilder ChildFrameCorrespondence
open RuntimeCallModeEffectsCorrespondence (ExtraHandler ModeHandlers)

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
      (RuntimeCallEffectsCorrespondence.sharedLocations ready.base.call.layout) dispatchValue) :
    ModeHandlers ready.base.call.layout where
  ordinary := ready.base.handlers dispatch
  callCode := ready.callCode.handler
  delegateCall := ready.delegateCall.handler

theorem ModeAllocationReady.captured {sharedCells cells : List InitializedCell} {store : Store}
    {parent : RuntimeCallModeSemantics.State} {request : AccountCallSemantics.Request}
    {shared : AccountCallSemantics.Shared} {bytes : List UInt8}
    {dispatcher creator : Nat} {dispatchValue : Value}
    (ready : ModeAllocationReady sharedCells cells store parent request shared bytes dispatcher creator dispatchValue)
    (dispatch : AccountCallCorrespondence.DispatcherClosure
      (RuntimeCallEffectsCorrespondence.sharedLocations ready.base.call.layout) dispatchValue)
    (context : RuntimeChildCallEffectsCorrespondence.Context ready.base.call.layout)
    (valid : context.valid (prefixRead ready.base.call.layout.boundary store)) :
    ((ready.handlers dispatch).context context).valid (prefixRead ready.base.call.layout.boundary store) := by
  refine ⟨valid, ?_, ?_⟩
  · simpa only [ModeAllocationReady.handlers, prefixRead, ready.callCode.handler.below, ↓reduceIte] using ready.callCode.read
  · simpa only [ModeAllocationReady.handlers, prefixRead, ready.delegateCall.handler.below, ↓reduceIte] using ready.delegateCall.read

theorem ModeAllocationReady.related {sharedCells cells : List InitializedCell} {store : Store}
    {parent : RuntimeCallModeSemantics.State} {request : AccountCallSemantics.Request}
    {shared : AccountCallSemantics.Shared} {bytes : List UInt8}
    {dispatcher creator : Nat} {dispatchValue : Value}
    (ready : ModeAllocationReady sharedCells cells store parent request shared bytes dispatcher creator dispatchValue)
    (dispatch : AccountCallCorrespondence.DispatcherClosure
      (RuntimeCallEffectsCorrespondence.sharedLocations ready.base.call.layout) dispatchValue)
    {anchors : RuntimeChildCallEffectsCorrespondence.Anchors}
    (context : RuntimeChildCallEffectsCorrespondence.Context ready.base.call.layout)
    (linked : RuntimeLinkedWorldCorrespondence.StateRel anchors shared.world ready.base.call.layout.storage.world store)
    (valid : context.valid (prefixRead ready.base.call.layout.boundary store)) :
    StateRel (RuntimeCallModeEffectsCorrespondence.model ready.base.call.layout
      (prefixRead ready.base.call.layout.boundary store) (cells.map InitializedCell.effectSlot)
      (some bytes) (ready.handlers dispatch) anchors context) []
      ⟨[], ChildFrameSemantics.initial parent request shared bytes⟩ store :=
  RuntimeChildCallEffectsCorrespondence.of_base (ready.base.related dispatch) linked (ready.captured dispatch context valid)

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
  apply allocateFrame_initializes_extra parent request sharedState bytes world references signature initialized separate
    observed creatorRelated creatorFound creatorSeparate frameRelated gasRelated codeRelated sizeRelated knownRelated
    property fresh sharedExtra creatorExtra continuation observes
  intro extra suffix cells values valuesRelated stored fullSignature locations origins sharedOrigins additional base
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
  apply continued extra suffix cells values valuesRelated stored fullSignature locations origins sharedOrigins
  exact {base := ready, callCode := callCodeReady, delegateCall := delegateReady}

end Solcore.Frontend.RustHull.ChildFrameModeCorrespondence
