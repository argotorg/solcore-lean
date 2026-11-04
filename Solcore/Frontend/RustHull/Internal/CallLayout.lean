import Solcore.Frontend.RustHull.Semantics.Frames
import Solcore.Frontend.RustHull.Internal.AccountLayers
import Solcore.Frontend.RustHull.Internal.RuntimeObjects
import Solcore.Frontend.RustHull.Internal.AccountCalls
import Solcore.Frontend.RustHull.ContractCodeTheorems
import Solcore.Frontend.RustHull.Semantics.Layers

/-!
# Call layout

The layout and state relation of the call layer, and the effects a call supports. It stays apart
from `Internal/CallStates`: `call_fixed_separation` unfolds `Layout` millions of times, and that
costs a quarter more heartbeats, past the limit, when `Layout` is declared in the same file.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCallModeSupported
/-! Message calls, account destruction and creation extend the executable subset
without changing the selection of existing return-data and runtime builtins. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallModeEffectsCorrespondence
open Correspondence

def supported (slots : List EffectSlot) (withCode : Bool) (name : String) : Prop :=
  RuntimeReturnDataEffectsCorrespondence.supported slots withCode name ∨ name = "call" ∨ name = "staticcall" ∨ name = "callcode" ∨ name = "delegatecall" ∨ name = "selfdestruct" ∨ name = "create" ∨ name = "create2"

theorem primitive_none {slots : List EffectSlot} {withCode : Bool} {name : String}
    (enabled : supported slots withCode name) (type : Ty) (arguments : List Semantics.Value) :
    Semantics.primitive? name type arguments = none := by
  rcases enabled with runtime | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact RuntimeReturnDataEffectsCorrespondence.primitive_none runtime type arguments
  all_goals rfl

private theorem code_call_unsupported {image : Option (List UInt8)} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : RuntimeCodeEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (newName : name = "call" ∨ name = "staticcall" ∨ name = "callcode" ∨ name = "delegatecall" ∨ name = "selfdestruct" ∨
      name = "create" ∨ name = "create2")
    (computed : RuntimeCodeEffectsSemantics.Builtin image name type arguments initial result final) : False := by
  cases computed with
  | copy computed =>
      obtain ⟨operation, named⟩ := computed.named
      rcases newName with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases operation <;>
        simp [CodeImageSemantics.Operation.name] at named
  | runtime computed =>
      cases computed with
      | observation computed =>
          obtain ⟨operation, named⟩ := computed.named
          rcases newName with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases operation <;>
            simp [AccountObservationSemantics.Operation.name] at named
      | runtime computed =>
          cases computed with
          | hash computed =>
              cases computed
              simp at newName
          | runtime computed =>
              cases computed with
              | copy computed =>
                  cases computed <;> simp at newName
              | runtime computed =>
                  cases computed with
                  | termination computed =>
                      have missing : TerminationSemantics.builtin name type arguments initial.runtime.runtime.runtime = none := by
                        rcases newName with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
                      rw [missing] at computed
                      contradiction
                  | runtime computed =>
                      cases computed with
                      | logs computed =>
                          cases computed with
                          | log operation _ _ _ _ _ _ =>
                              rcases newName with named | named | named | named | named | named | named <;> cases operation <;>
                                simp [LogsSemantics.Operation.name] at named
                      | runtime computed =>
                          have missing : RuntimeEnvironmentEffectsSemantics.builtin name type arguments initial.runtime.runtime = none := by
                            rcases newName with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
                          rw [missing] at computed
                          contradiction


private theorem runtime_call_unsupported {image : Option (List UInt8)} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : RuntimeReturnDataEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (newName : name = "call" ∨ name = "staticcall" ∨ name = "callcode" ∨ name = "delegatecall" ∨ name = "selfdestruct" ∨
      name = "create" ∨ name = "create2")
    (computed : RuntimeReturnDataEffectsSemantics.Builtin image name type arguments initial result final) : False := by
  cases computed with
  | runtime computed => exact code_call_unsupported newName computed
  | copy computed => cases computed; simp at newName
  | guard computed => cases computed; simp at newName

theorem runtime_enabled {slots : List EffectSlot} {withCode : Bool} {image : Option (List UInt8)}
    {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : RuntimeReturnDataEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (enabled : supported slots withCode name)
    (computed : RuntimeReturnDataEffectsSemantics.Builtin image name type arguments initial result final) :
    RuntimeReturnDataEffectsCorrespondence.supported slots withCode name := by
  rcases enabled with runtime | called
  · exact runtime
  · exact False.elim (runtime_call_unsupported called computed)

end Solcore.Frontend.RustHull.RuntimeCallModeEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractCallModeSupported
/-! The public effect subset includes message calls, account destruction and
creation attempts. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractCallModeCorrespondence
open Correspondence

def supported (withCode : Bool) (name : String) : Prop :=
  ContractReturnDataCorrespondence.supported withCode name ∨ name = "call" ∨ name = "staticcall" ∨ name = "callcode" ∨ name = "delegatecall" ∨ name = "selfdestruct" ∨ name = "create" ∨ name = "create2"

theorem supported_actual {slots : List EffectSlot} {withCode : Bool}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = RuntimeExtendedInitializedEffects.slots withCode) :
    RuntimeCallModeEffectsCorrespondence.supported slots withCode = supported withCode := by
  funext name
  apply propext
  simp only [RuntimeCallModeEffectsCorrespondence.supported, supported,
    ContractReturnDataCorrespondence.supported_actual signature]

end Solcore.Frontend.RustHull.ContractCallModeCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractCallRuntimeFacts
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCallStateCorrespondence
/-! Calls can change balances and caller return data while retaining their
installed closures. The resource relation records concrete optional-cell
contents and captured runtime handlers, rather than assuming callback execution. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
open Correspondence

structure Layout extends toReturnDataLayout : RuntimeReturnDataEffectsCorrespondence.Layout where
  callDepth : Nat
  callHandler : Nat
  dispatcher : Nat
  depthBelow : callDepth < boundary
  handlerBelow : callHandler < boundary
  dispatcherBelow : dispatcher < boundary
  callDistinct : (balances :: returnData :: returnDataSize :: callDepth :: callHandler :: dispatcher ::
    logs :: logSize :: memory :: storage.all).Nodup

def sharedLocations (layout : Layout) : AccountCallCorrespondence.SharedLocations :=
  ⟨layout.storage.world, layout.logs, layout.logSize, layout.balances, layout.storage.complete⟩

structure Handlers (layout : Layout) where
  source : Core.Word
  dispatchValue : Core.Value
  handlerValue : Core.Value
  dispatch : AccountCallCorrespondence.DispatcherClosure (sharedLocations layout) dispatchValue
  handler : AccountCallCorrespondence.CallHandlerClosure source layout.dispatcher handlerValue

def patched (layout : Layout) (baseline : Nat → Option Core.Value)
    (state : RuntimeCallEffectsSemantics.State) (location : Nat) : Option Core.Value :=
  if location = layout.balances then some (Core.WordMapping.encode state.runtime.runtime.balances) else baseline location

def mutable (layout : Layout) : List Nat :=
  layout.balances :: layout.returnData :: layout.returnDataSize :: RuntimeLogEffectsCorrespondence.mutable layout.toLogLayout

structure Resources (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot)
    (image : Option (List UInt8)) (handlers : Handlers layout) (state : RuntimeCallEffectsSemantics.State)
    (read : Nat → Option Core.Value) : Prop where
  runtime : RuntimeReturnDataEffectsCorrespondence.Resources layout.toReturnDataLayout (patched layout baseline state) slots image state.runtime read
  depth : read layout.callDepth = some (.word state.callDepth)
  handler : read layout.callHandler = some (.inRight .unit handlers.handlerValue)
  dispatcher : read layout.dispatcher = some (.inRight .unit handlers.dispatchValue)
  source : read layout.storage.address = some (.word handlers.source)

def model (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot)
    (image : Option (List UInt8)) (handlers : Handlers layout) : StateModel RuntimeCallEffectsSemantics.State :=
  StateModel.cutoff layout.boundary (Resources layout baseline slots image handlers)

def sourceRuntime (state : Semantics.State RuntimeCallEffectsSemantics.State) :
    Semantics.State RuntimeReturnDataEffectsSemantics.State := ⟨state.heap, state.external.runtime⟩

theorem runtime_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image handlers) world state store) :
    StateRel (RuntimeReturnDataEffectsCorrespondence.model layout.toReturnDataLayout (patched layout baseline state.external) slots image)
      world (sourceRuntime state) store :=
  ⟨related.toHeapRel, related.external.1, related.external.2.1, related.external.2.2.runtime⟩

theorem account_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image handlers) world state store) :
    StateRel (RuntimeAccountEffectsCorrespondence.model layout.toAccountLayout
      (RuntimeReturnDataEffectsCorrespondence.patched layout.toReturnDataLayout
        (patched layout baseline state.external) state.external.runtime) slots)
      world (RuntimeReturnDataEffectsCorrespondence.sourceRuntime (sourceRuntime state)) store :=
  RuntimeReturnDataEffectsCorrespondence.account_related (runtime_related related)

theorem call_separation (layout : Layout) :
    ∀ location ∈ [layout.callDepth, layout.callHandler, layout.dispatcher, layout.storage.address], location ∉ mutable layout := by
  have distinct := layout.callDistinct
  simp only [StorageBuiltinCorrespondence.Locations.all, List.nodup_cons, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, not_or] at distinct
  intro location member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals simp only [mutable, RuntimeLogEffectsCorrespondence.mutable, RuntimeEffectsCorrespondence.mutable,
    StorageBuiltinCorrespondence.Locations.mutable, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false, not_or]
  all_goals simp_all [ne_comm]

theorem returnData_other {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {world : World} {state : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    {store : Core.Store}
    (related : StateRel (RuntimeReturnDataEffectsCorrespondence.model layout.toReturnDataLayout baseline slots image) world state store)
    {location : Nat} (outside : location ∉ layout.returnData :: layout.returnDataSize :: RuntimeLogEffectsCorrespondence.mutable layout.toLogLayout) :
    prefixRead layout.boundary store location = baseline location := by
  have separate : location ≠ layout.returnData ∧ location ≠ layout.returnDataSize ∧ location ∉ RuntimeLogEffectsCorrespondence.mutable layout.toLogLayout := by
    simpa only [List.mem_cons, not_or] using outside
  have separateSize := separate.2
  simpa only [RuntimeReturnDataEffectsCorrespondence.patched, separate.1, separateSize.1, ↓reduceIte]
    using RuntimeLogEffectsCorrespondence.other_related
      (RuntimeAccountEffectsCorrespondence.runtime_related (RuntimeReturnDataEffectsCorrespondence.account_related related)) separateSize.2

theorem other_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image handlers) world state store)
    {location : Nat} (outside : location ∉ mutable layout) :
    prefixRead layout.boundary store location = baseline location := by
  have separate : location ≠ layout.balances ∧ location ∉ layout.returnData :: layout.returnDataSize :: RuntimeLogEffectsCorrespondence.mutable layout.toLogLayout := by
    simpa only [mutable, List.mem_cons, not_or] using outside
  simpa only [patched, separate.1, ↓reduceIte] using returnData_other (runtime_related related) separate.2

theorem runtime_updated {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {initial final : Core.Store}
    {runtime : RuntimeReturnDataEffectsSemantics.State}
    (before : StateRel (model layout baseline slots image handlers) world state initial)
    (after : StateRel (RuntimeReturnDataEffectsCorrespondence.model layout.toReturnDataLayout
      (patched layout baseline state.external) slots image) world {sourceRuntime state with external := runtime} final)
    (balances : runtime.runtime.balances = state.external.runtime.runtime.balances) :
    StateRel (model layout baseline slots image handlers) world {state with external := {state.external with runtime := runtime}} final := by
  have patchEqual : patched layout baseline {state.external with runtime := runtime} = patched layout baseline state.external := by
    funext location
    simp only [patched, balances]
  have retained (location : Nat) (member : location ∈ [layout.callDepth, layout.callHandler, layout.dispatcher, layout.storage.address]) :
      prefixRead layout.boundary final location = prefixRead layout.boundary initial location := by
    have separated : location ≠ layout.balances ∧ location ∉ layout.returnData :: layout.returnDataSize :: RuntimeLogEffectsCorrespondence.mutable layout.toLogLayout := by
      simpa only [mutable, List.mem_cons, not_or] using call_separation layout location member
    rw [returnData_other after separated.2, other_related before (call_separation layout location member)]
    simp only [patched, separated.1, ↓reduceIte]
  refine ⟨after.toHeapRel, after.external.1, after.external.2.1, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [patchEqual]
    exact after.external.2.2
  · rw [retained _ (by simp)]
    exact before.external.2.2.depth
  · rw [retained _ (by simp)]
    exact before.external.2.2.handler
  · rw [retained _ (by simp)]
    exact before.external.2.2.dispatcher
  · rw [retained _ (by simp)]
    exact before.external.2.2.source

theorem depth_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image handlers) world state store) :
    store.read? layout.callDepth = some (.word state.external.callDepth) := by
  simpa only [prefixRead, layout.depthBelow, ↓reduceIte] using related.external.2.2.depth

theorem installed {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image handlers) world state store) :
    Nonempty (AccountCallCorrespondence.InstalledHandlers (sharedLocations layout)
      state.external.runtime.runtime.runtime.runtime.runtime.storage.address layout.callHandler layout.dispatcher store) := by
  have old := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related
    (RuntimeLogEffectsCorrespondence.runtime_related
    (RuntimeAccountEffectsCorrespondence.runtime_related (account_related related))))
  have sourceRead : store.read? layout.storage.address = some (.word handlers.source) := by
    simpa only [prefixRead, layout.below layout.storage.address (by simp [StorageBuiltinCorrespondence.Locations.all]), ↓reduceIte]
      using related.external.2.2.source
  have sourceEqual : state.external.runtime.runtime.runtime.runtime.runtime.storage.address = handlers.source :=
    Core.Value.word.inj (Option.some.inj (old.address.symm.trans sourceRead))
  rw [sourceEqual]
  refine ⟨⟨handlers.dispatchValue, handlers.handlerValue, handlers.dispatch, handlers.handler, ?_, ?_⟩⟩
  · simpa only [prefixRead, layout.dispatcherBelow, ↓reduceIte] using related.external.2.2.dispatcher
  · simpa only [prefixRead, layout.handlerBelow, ↓reduceIte] using related.external.2.2.handler

theorem initial_state {layout : Layout} {slots : List EffectSlot} {state : RuntimeCallEffectsSemantics.State}
    {store : Core.Store} {image : Option (List UInt8)} {handlers : Handlers layout}
    (runtime : StateRel (RuntimeReturnDataEffectsCorrespondence.model layout.toReturnDataLayout
      (prefixRead layout.boundary store) slots image) [] ⟨[], state.runtime⟩ store)
    (depth : store.read? layout.callDepth = some (.word state.callDepth))
    (dispatchRead : store.read? layout.dispatcher = some (.inRight .unit handlers.dispatchValue))
    (handlerRead : store.read? layout.callHandler = some (.inRight .unit handlers.handlerValue))
    (source : state.runtime.runtime.runtime.runtime.runtime.storage.address = handlers.source) :
    StateRel (model layout (prefixRead layout.boundary store) slots image handlers) [] ⟨[], state⟩ store := by
  have account := RuntimeReturnDataEffectsCorrespondence.account_related runtime
  have balances := RuntimeAccountEffectsCorrespondence.balances_related account
  change store.read? layout.balances = some (Core.WordMapping.encode state.runtime.runtime.balances) at balances
  have patchEqual : patched layout (prefixRead layout.boundary store) state = prefixRead layout.boundary store := by
    funext location
    unfold patched
    split
    · subst location
      simpa only [prefixRead, layout.balancesBelow, ↓reduceIte] using balances.symm
    · rfl
  refine ⟨runtime.toHeapRel, runtime.external.1, runtime.external.2.1, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [patchEqual]
    exact runtime.external.2.2
  · simpa only [prefixRead, layout.depthBelow, ↓reduceIte] using depth
  · simpa only [prefixRead, layout.handlerBelow, ↓reduceIte] using handlerRead
  · simpa only [prefixRead, layout.dispatcherBelow, ↓reduceIte] using dispatchRead
  · have storage := RuntimeEffectsCorrespondence.storage_related
      (RuntimeEnvironmentEffectsCorrespondence.runtime_related
      (RuntimeLogEffectsCorrespondence.runtime_related (RuntimeAccountEffectsCorrespondence.runtime_related account)))
    have found := storage.address
    change store.read? layout.storage.address = some (.word state.runtime.runtime.runtime.runtime.runtime.storage.address) at found
    simpa only [prefixRead, layout.below layout.storage.address (by simp [StorageBuiltinCorrespondence.Locations.all]), ↓reduceIte, source] using found

end Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCallSupported
/-! Call names extend the executable subset without changing the selection of
existing return-data and runtime builtins. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
open Correspondence

def supported (slots : List EffectSlot) (withCode : Bool) (name : String) : Prop :=
  RuntimeReturnDataEffectsCorrespondence.supported slots withCode name ∨ name = "call" ∨ name = "staticcall"

theorem primitive_none {slots : List EffectSlot} {withCode : Bool} {name : String}
    (enabled : supported slots withCode name) (type : Ty) (arguments : List Semantics.Value) :
    Semantics.primitive? name type arguments = none := by
  rcases enabled with runtime | rfl | rfl
  · exact RuntimeReturnDataEffectsCorrespondence.primitive_none runtime type arguments
  · rfl
  · rfl

private theorem code_call_unsupported {image : Option (List UInt8)} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : RuntimeCodeEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (newName : name = "call" ∨ name = "staticcall")
    (computed : RuntimeCodeEffectsSemantics.Builtin image name type arguments initial result final) : False := by
  cases computed with
  | copy computed =>
      obtain ⟨operation, named⟩ := computed.named
      rcases newName with rfl | rfl <;> cases operation <;>
        simp [CodeImageSemantics.Operation.name] at named
  | runtime computed =>
      cases computed with
      | observation computed =>
          obtain ⟨operation, named⟩ := computed.named
          rcases newName with rfl | rfl <;> cases operation <;>
            simp [AccountObservationSemantics.Operation.name] at named
      | runtime computed =>
          cases computed with
          | hash computed =>
              cases computed
              simp at newName
          | runtime computed =>
              cases computed with
              | copy computed =>
                  cases computed <;> simp at newName
              | runtime computed =>
                  cases computed with
                  | termination computed =>
                      have missing : TerminationSemantics.builtin name type arguments initial.runtime.runtime.runtime = none := by
                        rcases newName with rfl | rfl <;> rfl
                      rw [missing] at computed
                      contradiction
                  | runtime computed =>
                      cases computed with
                      | logs computed =>
                          cases computed with
                          | log operation _ _ _ _ _ _ =>
                              rcases newName with named | named <;> cases operation <;>
                                simp [LogsSemantics.Operation.name] at named
                      | runtime computed =>
                          have missing : RuntimeEnvironmentEffectsSemantics.builtin name type arguments initial.runtime.runtime = none := by
                            rcases newName with rfl | rfl <;> rfl
                          rw [missing] at computed
                          contradiction


private theorem runtime_call_unsupported {image : Option (List UInt8)} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : RuntimeReturnDataEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (newName : name = "call" ∨ name = "staticcall")
    (computed : RuntimeReturnDataEffectsSemantics.Builtin image name type arguments initial result final) : False := by
  cases computed with
  | runtime computed => exact code_call_unsupported newName computed
  | copy computed => cases computed; simp at newName
  | guard computed => cases computed; simp at newName

theorem runtime_enabled {slots : List EffectSlot} {withCode : Bool} {image : Option (List UInt8)}
    {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : RuntimeReturnDataEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (enabled : supported slots withCode name)
    (computed : RuntimeReturnDataEffectsSemantics.Builtin image name type arguments initial result final) :
    RuntimeReturnDataEffectsCorrespondence.supported slots withCode name := by
  rcases enabled with runtime | called | staticCall
  · exact runtime
  · exact False.elim (runtime_call_unsupported (.inl called) computed)
  · exact False.elim (runtime_call_unsupported (.inr staticCall) computed)

end Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
end
