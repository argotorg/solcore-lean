import Solcore.Frontend.RustHull.RuntimeInstalledCallbacksCorrespondence
import Solcore.Frontend.RustHull.AccountCallHandlersCorrespondence
import Solcore.Frontend.RustHull.ContractReturnDataRuntimeFacts

/-! The actual frame initializer captures the dispatcher reference and source
address used by later calls. Shared callback provenance comes from the actual
object allocator. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractCallCorrespondence
open Correspondence ScalarExecution CodeBuilder AccountCallCorrespondence

def initializedHandler (source : Core.Word) (dispatcherLocation : Nat) (cell : InitializedCell) : Prop :=
  cell.name = "callHandler" → ∃ value, cell.value = .inRight .unit value ∧
    Nonempty (CallHandlerClosure source dispatcherLocation value)

theorem fresh_handler_observation {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {frame dispatcher gas code codeSize codeKnown : Code} {shared : AccountRuntime.References}
    {values : List Core.Value} {gasValue codeValue sizeValue knownValue : Core.Value}
    {source : Core.Word} {dispatcherLocation : Nat}
    (frameRelated : CodeValue depth environment frame (bundleValues values)) (length : values.length = 8)
    (address : values[0]? = some (.word source))
    (dispatcherRelated : CodeValue depth environment dispatcher
      (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation))
    (gasRelated : CodeValue depth environment gas gasValue)
    (codeRelated : CodeValue depth environment code codeValue)
    (sizeRelated : CodeValue depth environment codeSize sizeValue)
    (knownRelated : CodeValue depth environment codeKnown knownValue) :
    FrameInitializersValid depth environment store frame dispatcher gas code codeSize codeKnown shared
      (initializedHandler source dispatcherLocation) := by
  intro extra suffix name type _
  by_cases named : name = "callHandler"
  · subst name
    have lambda : LambdaCode (AccountRuntime.frameCallHandler 0 frame dispatcher) := by
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
    · exact .inRight (captured.evaluates (store ++ suffix))
    · simpa only [length] using (frameRelated.part address).prepend extra
  · obtain ⟨value, evaluated⟩ := frameInitializers_ready frameRelated length gasRelated codeRelated sizeRelated knownRelated
      extra name (store ++ suffix)
    exact ⟨value, evaluated, fun impossible => False.elim (named impossible)⟩

theorem shared_handler_observation {context : Code} {cells : List InitializedCell} {values : List Core.Value}
    (source : Core.Word) (dispatcherLocation : Nat)
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip values).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse) :
    ∀ cell ∈ cells, initializedHandler source dispatcherLocation cell := by
  intro cell member named
  have present := shared_description_member description member
  change cell.name = "callHandler" at named
  rw [named] at present
  simp [sharedSlotTypes, Ambient.slots] at present

theorem creator_handler_observation (source : Core.Word) (dispatcherLocation location : Nat) (value : Core.Value) :
    initializedHandler source dispatcherLocation (ContractRuntimeEffectsCorrespondence.creatorCell location value) := by
  intro impossible
  simp [ContractRuntimeEffectsCorrespondence.creatorCell] at impossible

theorem fresh_dispatcher_separate {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {frame dispatcher gas code codeSize codeKnown : Code} {shared : AccountRuntime.References}
    {values : List Core.Value} {gasValue codeValue sizeValue knownValue : Core.Value}
    {dispatcherLocation : Nat} (dispatcherBelow : dispatcherLocation < store.length)
    (frameRelated : CodeValue depth environment frame (bundleValues values)) (length : values.length = 8)
    (gasRelated : CodeValue depth environment gas gasValue)
    (codeRelated : CodeValue depth environment code codeValue)
    (sizeRelated : CodeValue depth environment codeSize sizeValue)
    (knownRelated : CodeValue depth environment codeKnown knownValue) :
    FrameInitializersValid depth environment store frame dispatcher gas code codeSize codeKnown shared
      (fun cell => cell.location ≠ dispatcherLocation) := by
  apply frameInitializers_valid frameRelated length gasRelated codeRelated sizeRelated knownRelated
  intro name type location value _ after _
  change location ≠ dispatcherLocation
  omega

def initializedDepth (callDepth : Core.Word) (cell : InitializedCell) : Prop :=
  cell.name = "callDepth" → cell.value = .word callDepth

theorem fresh_depth_observation {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {frame dispatcher gas code codeSize codeKnown : Code} {shared : AccountRuntime.References}
    {values : List Core.Value} {gasValue codeValue sizeValue knownValue : Core.Value} {callDepth : Core.Word}
    (frameRelated : CodeValue depth environment frame (bundleValues values)) (length : values.length = 8)
    (depthValue : values[4]? = some (.word callDepth))
    (gasRelated : CodeValue depth environment gas gasValue)
    (codeRelated : CodeValue depth environment code codeValue)
    (sizeRelated : CodeValue depth environment codeSize sizeValue)
    (knownRelated : CodeValue depth environment codeKnown knownValue) :
    FrameInitializersValid depth environment store frame dispatcher gas code codeSize codeKnown shared
      (initializedDepth callDepth) := by
  apply frameInitializers_valid frameRelated length gasRelated codeRelated sizeRelated knownRelated
  intro name type location value _ _ observed named
  change name = "callDepth" at named
  subst name
  exact observed _ depthValue

theorem shared_depth_observation {context : Code} {cells : List InitializedCell} {values : List Core.Value}
    (callDepth : Core.Word)
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip values).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse) :
    ∀ cell ∈ cells, initializedDepth callDepth cell := by
  intro cell member named
  have present := shared_description_member description member
  change cell.name = "callDepth" at named
  rw [named] at present
  simp [sharedSlotTypes, Ambient.slots] at present

theorem creator_depth_observation (callDepth : Core.Word) (location : Nat) (value : Core.Value) :
    initializedDepth callDepth (ContractRuntimeEffectsCorrespondence.creatorCell location value) := by
  intro impossible
  simp [ContractRuntimeEffectsCorrespondence.creatorCell] at impossible

def dispatchSharedNames : List String := ["world", "logs", "logSize", "balances", "worldComplete"]

def sharedOrigin (sharedCells : List InitializedCell) (cell : InitializedCell) : Prop :=
  cell.name ∈ dispatchSharedNames → cell ∈ sharedCells

theorem fresh_shared_origin {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {frame dispatcher gas code codeSize codeKnown : Code} {shared : AccountRuntime.References}
    {values : List Core.Value} {gasValue codeValue sizeValue knownValue : Core.Value}
    {sharedCells : List InitializedCell}
    (references : RuntimeReferences depth environment shared sharedCells)
    (present : ∀ name ∈ dispatchSharedNames, name ∈ sharedCells.map InitializedCell.name)
    (frameRelated : CodeValue depth environment frame (bundleValues values)) (length : values.length = 8)
    (gasRelated : CodeValue depth environment gas gasValue)
    (codeRelated : CodeValue depth environment code codeValue)
    (sizeRelated : CodeValue depth environment codeSize sizeValue)
    (knownRelated : CodeValue depth environment codeKnown knownValue) :
    FrameInitializersValid depth environment store frame dispatcher gas code codeSize codeKnown shared
      (sharedOrigin sharedCells) := by
  apply frameInitializers_valid frameRelated length gasRelated codeRelated sizeRelated knownRelated
  intro name type location value absent _ _ named
  have included := present name named
  rw [← references.names] at included
  obtain ⟨entry, member, same⟩ := List.mem_map.mp included
  exact False.elim (List.find?_eq_none.mp absent entry member (by simp only [same, beq_self_eq_true]))

theorem creator_shared_origin (sharedCells : List InitializedCell) (location : Nat) (value : Core.Value) :
    sharedOrigin sharedCells (ContractRuntimeEffectsCorrespondence.creatorCell location value) := by
  intro impossible
  simp [ContractRuntimeEffectsCorrespondence.creatorCell, dispatchSharedNames] at impossible

private theorem same_named_cell {cells : List InitializedCell}
    (unique : (cells.map InitializedCell.name).Nodup)
    {left right : InitializedCell} (leftMember : left ∈ cells) (rightMember : right ∈ cells)
    (named : left.name = right.name) : left = right := by
  obtain ⟨leftIndex, leftFound⟩ := List.mem_iff_getElem?.mp leftMember
  obtain ⟨rightIndex, rightFound⟩ := List.mem_iff_getElem?.mp rightMember
  have leftName : (cells.map InitializedCell.name)[leftIndex]? = some left.name := by
    simp only [List.getElem?_map, leftFound, Option.map_some]
  have rightName : (cells.map InitializedCell.name)[rightIndex]? = some left.name := by
    simp only [List.getElem?_map, rightFound, Option.map_some, named]
  have same := (List.getElem?_inj (List.getElem?_eq_some_iff.mp leftName).1 unique).mp (leftName.trans rightName.symm)
  subst rightIndex
  exact Option.some.inj (leftFound.symm.trans rightFound)

theorem reference_cell {depth : Nat} {environment : Core.Environment}
    {references : AccountRuntime.References} {cells : List InitializedCell}
    (related : RuntimeReferences depth environment references cells)
    (unique : (cells.map InitializedCell.name).Nodup)
    {cell : InitializedCell} (member : cell ∈ cells) :
    CodeValue depth environment (AccountRuntime.reference references cell.name) cell.reference := by
  obtain ⟨actual, actualMember, named, actualRelated⟩ := related.reference (List.mem_map_of_mem member)
  have same := same_named_cell unique actualMember member named
  exact same ▸ actualRelated

theorem named_slot_location {cells : List InitializedCell}
    (unique : (cells.map InitializedCell.name).Nodup) {left right : EffectSlot}
    (leftMember : left ∈ cells.map InitializedCell.effectSlot)
    (rightMember : right ∈ cells.map InitializedCell.effectSlot) (named : left.name = right.name) :
    left.location = right.location := by
  obtain ⟨leftCell, leftPresent, leftEqual⟩ := List.mem_map.mp leftMember
  obtain ⟨rightCell, rightPresent, rightEqual⟩ := List.mem_map.mp rightMember
  subst left
  subst right
  exact congrArg InitializedCell.location (same_named_cell unique leftPresent rightPresent named)

/-- Named shared cells identify the same locations in the frame and in the
captured dispatch closure. -/
structure SharedCells (cells : List InitializedCell) (locations : SharedLocations) : Prop where
  world : ∃ cell ∈ cells, cell.name = "world" ∧ cell.reference = .cellRef AccountState.type locations.world
  logs : ∃ cell ∈ cells, cell.name = "logs" ∧ cell.reference = .cellRef Core.WordMapping.type locations.logs
  logSize : ∃ cell ∈ cells, cell.name = "logSize" ∧ cell.reference = .cellRef .word locations.logSize
  balances : ∃ cell ∈ cells, cell.name = "balances" ∧ cell.reference = .cellRef Core.WordMapping.type locations.balances
  complete : ∃ cell ∈ cells, cell.name = "worldComplete" ∧ cell.reference = .cellRef .bool locations.complete

theorem SharedCells.references {cells : List InitializedCell} {locations : SharedLocations}
    (selected : SharedCells cells locations) (unique : (cells.map InitializedCell.name).Nodup)
    {depth : Nat} {environment : Core.Environment} {references : AccountRuntime.References}
    (related : RuntimeReferences depth environment references cells) :
    SharedReferences depth environment references locations := by
  have namedReference : ∀ name type location,
      (∃ cell ∈ cells, cell.name = name ∧ cell.reference = .cellRef type location) →
      CodeValue depth environment (AccountRuntime.reference references name) (.cellRef type location) := by
    intro name type location selected
    obtain ⟨cell, member, named, atLocation⟩ := selected
    simpa only [named, atLocation] using reference_cell related unique member
  exact ⟨namedReference _ _ _ selected.world, namedReference _ _ _ selected.logs,
    namedReference _ _ _ selected.logSize, namedReference _ _ _ selected.balances,
    namedReference _ _ _ selected.complete⟩

theorem effectSlots_distinct {cells : List InitializedCell} (separate : CellLocations cells)
    {selected : List EffectSlot} (included : ∀ slot ∈ selected, slot ∈ cells.map InitializedCell.effectSlot)
    (unique : (selected.map EffectSlot.name).Nodup) : (selected.map EffectSlot.location).Nodup := by
  induction selected with
  | nil => exact List.nodup_nil
  | cons head rest ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      apply List.nodup_cons.mpr
      constructor
      · intro inside
        obtain ⟨other, member, same⟩ := List.mem_map.mp inside
        obtain ⟨left, leftMember, leftSame⟩ := List.mem_map.mp (included head (.head _))
        obtain ⟨right, rightMember, rightSame⟩ := List.mem_map.mp (included other (.tail _ member))
        have locations : right.location = left.location := by
          change right.effectSlot.location = left.effectSlot.location
          rw [leftSame, rightSame]
          exact same
        have names := separate right rightMember left leftMember locations
        apply absent
        refine List.mem_map.mpr ⟨other, member, ?_⟩
        change other.name = head.name
        rw [← leftSame, ← rightSame]
        exact names
      · exact ih (fun slot member => included slot (.tail _ member)) tailUnique

theorem separate_dispatcher {cells : List InitializedCell} (separate : CellLocations cells)
    {location : Nat} (outside : ∀ cell ∈ cells, cell.location ≠ location) (value : Core.Value) :
    CellLocations (⟨"$dispatcher", Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType, location, value⟩ :: cells) := by
  intro left leftMember right rightMember same
  cases leftMember with
  | head =>
      cases rightMember with
      | head => rfl
      | tail _ member => exact False.elim (outside right member same.symm)
  | tail _ member =>
      cases rightMember with
      | head => exact False.elim (outside left member same)
      | tail _ member' => exact separate left member right member' same

def captured_dispatcher {slots : List (String × Core.Ty)} {count : Nat}
    {images : List (Nat × List UInt8)} {catalog : List AccountRuntime.CodeDefinition}
    {functionsValue : List Core.Value} {cells : List InitializedCell}
    {dispatcherLocation creatorLocation : Nat} {store : Core.Store}
    (capture : ObjectCallbackCapture slots count images catalog functionsValue cells dispatcherLocation creatorLocation store)
    (locations : SharedLocations)
    (references : SharedReferences capture.depth capture.environment capture.shared locations) :
    DispatcherClosure locations capture.closure :=
  { depth := capture.depth
    captured := capture.environment
    shared := capture.shared
    runFrame := _
    closure := capture.captured
    references := references }

end Solcore.Frontend.RustHull.ContractCallCorrespondence
