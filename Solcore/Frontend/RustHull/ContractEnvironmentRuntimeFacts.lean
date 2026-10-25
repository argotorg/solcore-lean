import Solcore.Frontend.RustHull.RuntimeEnvironmentEffectsFrameCorrespondence
import Solcore.Frontend.RustHull.ContractMemoryExecutionCorrespondence
import Solcore.Frontend.RustHull.RuntimeInitializedEffects

/-! Public input values establish every environment observation in the actual
shared and fresh frame cells. The property composes with memory/storage cell
properties before allocation and yields the environment relation afterwards. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractEnvironmentCorrespondence
open Correspondence ScalarExecution CodeBuilder

def contextEnvironment (context : Contract.Context) (codeBytes : Option (List UInt8) := none) :
    EnvironmentSemantics.State where
  direct := fun operation => match operation with
    | .address => context.address
    | .caller => context.caller
    | .callvalue => context.value
    | .calldataSize => Core.Word.ofNatModulo context.calldata.length
    | .returnDataSize => Core.Word.zero
  ambient := fun operation => match operation with
    | .origin => context.ambient.origin
    | .gasprice => context.ambient.gasprice
    | .coinbase => context.ambient.coinbase
    | .timestamp => context.ambient.timestamp
    | .number => context.ambient.number
    | .prevrandao => context.ambient.prevrandao
    | .gaslimit => context.ambient.gaslimit
    | .chainid => context.ambient.chainid
    | .basefee => context.ambient.basefee
    | .blobbasefee => context.ambient.blobbasefee
  gas := context.availableGas
  codeSize := Core.Word.ofNatModulo (codeBytes.getD []).length
  codeKnown := codeBytes.isSome
  calldata := Contract.calldataEntries context.calldata
  blockHashes := context.ambient.blockHashes
  blobHashes := context.ambient.blobHashes.map Ambient.blobEntries

def initializedValue (state : EnvironmentSemantics.State) (cell : InitializedCell) : Prop :=
  ∀ value, EnvironmentBuiltinCorrespondence.observation state cell.name cell.type = some value → cell.value = value

theorem initialized_related {state : EnvironmentSemantics.State} {cells : List InitializedCell} {store : Core.Store}
    (initialized : InitializedCells cells store)
    (observed : ∀ cell ∈ cells, initializedValue state cell) :
    EnvironmentBuiltinCorrespondence.StateRel (cells.map InitializedCell.effectSlot) state store := by
  intro slot member value specified
  obtain ⟨cell, cellMember, rfl⟩ := List.mem_map.mp member
  exact (initialized cell cellMember).trans (congrArg some (observed cell cellMember value specified))

theorem initialized_passive {state : RuntimeEffectsSemantics.State} {cells : List InitializedCell} {store : Core.Store}
    (ready : RuntimeInitializedEffects.StateReady cells store state) (separate : CellLocations cells) :
    RuntimeEnvironmentEffectsCorrespondence.Passive
      (RuntimeEffectsCorrespondence.initialLayout ready.memoryRelated ready.storageRelated ready.distinct)
      (cells.map InitializedCell.effectSlot) := by
  apply RuntimeEnvironmentEffectsCorrespondence.Passive.of_names _ ready.memoryMember ready.worldMember
    ready.sizeMember ready.exitMember ready.offsetMember ready.returnSizeMember
  intro first firstMember second secondMember same
  obtain ⟨firstCell, firstCellMember, rfl⟩ := List.mem_map.mp firstMember
  obtain ⟨secondCell, secondCellMember, rfl⟩ := List.mem_map.mp secondMember
  by_cases named : firstCell.name = secondCell.name
  · exact named
  · exact False.elim (separate.different firstCellMember secondCellMember named same)

private theorem available_iff {slots : List EffectSlot} {operation : EnvironmentSemantics.Operation} :
    EnvironmentBuiltinCorrespondence.Available slots operation ↔
      ∀ name type, (name, type) ∈ EnvironmentBuiltinCorrespondence.inputs operation →
        (name, type) ∈ slots.map (fun slot => (slot.name, slot.type)) := by
  constructor
  · intro available name type member
    obtain ⟨location, found⟩ := available name type member
    exact List.mem_map.mpr ⟨⟨name, type, location⟩, found, rfl⟩
  · intro available name type member
    obtain ⟨slot, slotMember, same⟩ := List.mem_map.mp (available name type member)
    obtain ⟨named, typed⟩ := Prod.mk.inj same
    exact ⟨slot.location, by simpa only [← named, ← typed] using slotMember⟩

theorem available_effects {slots : List EffectSlot}
    (shape : slots.map (fun slot => (slot.name, slot.type)) = Effects.slots)
    (operation : EnvironmentSemantics.Operation) :
    EnvironmentBuiltinCorrespondence.Available slots operation ↔ operation ≠ .codeSize := by
  rw [available_iff, shape]
  cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
  all_goals simp [EnvironmentBuiltinCorrespondence.inputs, EnvironmentSemantics.Direct.slot,
    EnvironmentSemantics.Direct.name, EnvironmentSemantics.AmbientWord.name, Effects.slots, Ambient.slots,
    EnvironmentBuiltinCorrespondence.optionalWord, EnvironmentBuiltinCorrespondence.optionalHashes,
    Ambient.optionalWord, Ambient.optionalHashes, or_imp]
  case codeSize => exact ⟨"codeSize", .word, by simp⟩
  case blockHash =>
    intro name type
    constructor <;> intro named typed <;> subst name <;> subst type <;> simp

theorem shared_initialized_value {contextCode : Code} {cells : List InitializedCell}
    {accounts : StorageCorrespondence.Accounts} {complete : Bool} {balances : StorageSemantics.Words}
    (context : Contract.Context) (codeBytes : Option (List UInt8))
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip
        (ContractMemoryCorrespondence.sharedValues accounts complete balances (ambientValues context.ambient))).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse) :
    ∀ cell ∈ cells, initializedValue (contextEnvironment context codeBytes) cell := by
  intro cell member expected specified
  have namedMember : cell.name ∈ sharedSlotTypes.map Prod.fst :=
    List.mem_map.mpr ⟨(cell.name, cell.type), shared_description_member description member, rfl⟩
  unfold EnvironmentBuiltinCorrespondence.observation at specified
  split at specified
  all_goals first
    | contradiction
    | (cases specified; exact shared_description_value description member (index := 5) rfl rfl ‹cell.name = "origin"›)
    | (cases specified; exact shared_description_value description member (index := 6) rfl rfl ‹cell.name = "gasprice"›)
    | (cases specified; exact shared_description_value description member (index := 7) rfl rfl ‹cell.name = "coinbase"›)
    | (cases specified; exact shared_description_value description member (index := 8) rfl rfl ‹cell.name = "timestamp"›)
    | (cases specified; exact shared_description_value description member (index := 9) rfl rfl ‹cell.name = "number"›)
    | (cases specified; exact shared_description_value description member (index := 10) rfl rfl ‹cell.name = "prevrandao"›)
    | (cases specified; exact shared_description_value description member (index := 11) rfl rfl ‹cell.name = "gaslimit"›)
    | (cases specified; exact shared_description_value description member (index := 12) rfl rfl ‹cell.name = "chainid"›)
    | (cases specified; exact shared_description_value description member (index := 13) rfl rfl ‹cell.name = "basefee"›)
    | (cases specified; exact shared_description_value description member (index := 14) rfl rfl ‹cell.name = "blobbasefee"›)
    | (simp_all [sharedSlotTypes, Ambient.slots])
  all_goals obtain ⟨_, rfl⟩ := specified
  all_goals first
    | exact shared_description_value description member (index := 15) rfl rfl ‹cell.name = "blockHashes"›
    | exact shared_description_value description member (index := 16) rfl rfl ‹cell.name = "blobHashes"›

private theorem shared_present {depth : Nat} {environment : Core.Environment} {contextCode : Code}
    {shared : AccountRuntime.References} {cells : List InitializedCell}
    {accounts : StorageCorrespondence.Accounts} {complete : Bool} {balances : StorageSemantics.Words}
    {context : Contract.Context}
    (references : RuntimeReferences depth environment shared cells)
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip
        (ContractMemoryCorrespondence.sharedValues accounts complete balances (ambientValues context.ambient))).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse)
    {name : String} (member : name ∈ sharedSlotTypes.map Prod.fst) :
    shared.find? (·.1 == name) ≠ none := by
  obtain ⟨index, named⟩ := List.mem_iff_getElem?.mp member
  let values := ContractMemoryCorrespondence.sharedValues accounts complete balances (ambientValues context.ambient)
  have bound : index < values.length := by
    have bound := (List.getElem?_eq_some_iff.mp named).1
    simpa only [values, ContractMemoryCorrespondence.sharedValues, ambientValues, sharedSlotTypes,
      Ambient.slots, List.length_map, List.length_append, List.length_cons, List.length_nil] using bound
  exact ContractMemoryCorrespondence.shared_name_present references description named (List.getElem?_eq_getElem bound)

theorem fresh_initializers_observation {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {frame dispatcher gas code codeSize codeKnown contextCode : Code}
    {shared : AccountRuntime.References} {cells : List InitializedCell}
    {accounts : StorageCorrespondence.Accounts} {complete : Bool} {balances : StorageSemantics.Words}
    (context : Contract.Context)
    (frameRelated : CodeValue depth environment frame
      (bundleValues (ContractMemoryCorrespondence.requestValues context)))
    (gasRelated : CodeValue depth environment gas (optionalWordValue context.availableGas))
    (codeRelated : CodeValue depth environment code (Core.WordMapping.encode []))
    (sizeRelated : CodeValue depth environment codeSize (.word (Core.Word.ofNatModulo 0)))
    (knownRelated : CodeValue depth environment codeKnown (.bool false))
    (references : RuntimeReferences depth environment shared cells)
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip
        (ContractMemoryCorrespondence.sharedValues accounts complete balances (ambientValues context.ambient))).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse) :
    FrameInitializersValid depth environment store frame dispatcher gas code codeSize codeKnown shared
      (initializedValue (contextEnvironment context)) := by
  apply frameInitializers_valid frameRelated rfl gasRelated codeRelated sizeRelated knownRelated
  intro name type location value absent _ known expected specified
  have notShared : name ∉ sharedSlotTypes.map Prod.fst :=
    fun member => shared_present references description member absent
  change EnvironmentBuiltinCorrespondence.observation (contextEnvironment context) name type = some expected at specified
  change value = expected
  unfold EnvironmentBuiltinCorrespondence.observation at specified
  split at specified
  all_goals first
    | contradiction
    | (cases specified; exact known _ (by simp [frameExpected, contextEnvironment,
        ContractMemoryCorrespondence.requestValues, *] <;> rfl))
    | (simp_all [sharedSlotTypes, Ambient.slots])
  obtain ⟨_, rfl⟩ := specified
  exact known _ rfl

theorem creator_observation {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {creator : Code} {location : Nat} {value : Core.Value} {slots : List (String × Core.Ty)}
    (related : CodeValue depth environment creator (.cellRef (Core.OptionalCell.cellType Creation.callbackType) location))
    (stored : store.read? location = some value)
    (typed : ∀ type, ("createHandler", type) ∈ slots → type = Core.OptionalCell.cellType Creation.callbackType)
    (state : EnvironmentSemantics.State) :
    FrameCreatorValid depth environment store slots creator (initializedValue state) := by
  intro type member
  cases typed type member
  refine ⟨⟨"createHandler", _, location, value⟩, rfl, rfl, related, stored, ?_⟩
  intro expected impossible
  cases impossible

end Solcore.Frontend.RustHull.ContractEnvironmentCorrespondence
