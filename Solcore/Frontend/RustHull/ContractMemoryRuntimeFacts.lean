import Solcore.Frontend.RustHull.ContractMemoryCorrespondence
import Solcore.Frontend.RustHull.RuntimeEnvironmentCorrespondence
import Solcore.Frontend.RustHull.RuntimeReferenceFacts

/-! Concrete initialized observations used by the public memory theorem.
Shared and fresh runtime cells are distinguished by their actual allocation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractMemoryCorrespondence
open Correspondence ScalarExecution CodeBuilder

def passiveExpected (accounts : StorageCorrespondence.Accounts) (address : Core.Word) (complete : Bool)
    (balances : StorageSemantics.Words) : String → Option Core.Value
  | "world" => some (StorageCorrespondence.world accounts)
  | "worldComplete" => some (.bool complete)
  | "address" => some (.word address)
  | "exit" | "returnOffset" | "returnSize" | "logSize" => some (.word (Core.Word.ofNatModulo 0))
  | "logs" => some (Core.WordMapping.encode [])
  | "balances" => some (Core.WordMapping.encode balances)
  | _ => none

def initializedObservation (base : Nat) (accounts : StorageCorrespondence.Accounts) (address : Core.Word)
    (complete : Bool) (balances : StorageSemantics.Words) (cell : InitializedCell) : Prop :=
  (∀ value, passiveExpected accounts address complete balances cell.name = some value → cell.value = value) ∧
  (cell.name ≠ "memory" → cell.name ≠ "memorySize" → cell.location ≠ base ∧ cell.location ≠ base + 1)

theorem initializedObservation_memory (store : Core.Store) (accounts : StorageCorrespondence.Accounts)
    (address : Core.Word) (complete : Bool) (balances : StorageSemantics.Words) :
    initializedObservation store.length accounts address complete balances (initialMemoryCell store) := by
  constructor
  · intro value impossible; cases impossible
  · intro impossible; exact False.elim (impossible rfl)

theorem initializedObservation_size (store : Core.Store) (accounts : StorageCorrespondence.Accounts)
    (address : Core.Word) (complete : Bool) (balances : StorageSemantics.Words) :
    initializedObservation store.length accounts address complete balances (initialSizeCell store) := by
  constructor
  · intro value impossible; cases impossible
  · intro _ impossible; exact False.elim (impossible rfl)

theorem initializedObservation_passive {base : Nat} {cells : List InitializedCell} {store : Core.Store}
    {accounts : StorageCorrespondence.Accounts} {address : Core.Word} {complete : Bool} {balances : StorageSemantics.Words}
    {memory : MemorySemantics.State}
    (memoryRelated : MemoryCorrespondence.StateRel base (base + 1) memory store)
    (initialized : InitializedCells cells store)
    (observed : ∀ cell ∈ cells, initializedObservation base accounts address complete balances cell)
    {name : String} {value : Core.Value}
    (member : name ∈ cells.map InitializedCell.name)
    (expected : passiveExpected accounts address complete balances name = some value) :
    MemoryFrameCorrespondence.PassiveCell (MemoryEffectCorrespondence.initialLayout memoryRelated)
      (cells.map InitializedCell.effectSlot) store name value := by
  obtain ⟨cell, member, named⟩ := List.mem_map.mp member
  have specified : cell.value = value := (observed cell member).1 value (by simpa only [named] using expected)
  have memory : cell.name ≠ "memory" := by
    intro same
    rw [← named, same] at expected
    cases expected
  have size : cell.name ≠ "memorySize" := by
    intro same
    rw [← named, same] at expected
    cases expected
  have separated := (observed cell member).2 memory size
  exact ⟨cell.effectSlot, List.mem_map.mpr ⟨cell, member, rfl⟩, named, separated.1, separated.2,
    initialized.location_bound member, by simpa only [InitializedCell.effectSlot, specified] using initialized cell member⟩

theorem snapshot_expected (memory : MemorySemantics.State) (accounts : StorageCorrespondence.Accounts)
    (address : Core.Word) (complete : Bool) (balances : StorageSemantics.Words)
    (name : String) (member : name ∈ frameSnapshotNames) (notMemory : name ≠ "memory") :
    passiveExpected accounts address complete balances name = some (snapshotValues memory accounts balances name) := by
  simp only [frameSnapshotNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | exact False.elim (notMemory rfl)

def sharedValues (accounts : StorageCorrespondence.Accounts) (complete : Bool)
    (balances : StorageSemantics.Words) (ambient : List Core.Value) : List Core.Value :=
  [StorageCorrespondence.world accounts, .bool complete, Core.WordMapping.encode [],
    .word (Core.Word.ofNatModulo 0), Core.WordMapping.encode balances] ++ ambient

theorem shared_initialized_observation {context : Code} {cells : List InitializedCell} {store : Core.Store}
    {accounts : StorageCorrespondence.Accounts} {address : Core.Word} {complete : Bool}
    {balances : StorageSemantics.Words} {ambient : List Core.Value}
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip (sharedValues accounts complete balances ambient)).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse)
    (initialized : InitializedCells cells store) :
    ∀ cell ∈ cells, initializedObservation store.length accounts address complete balances cell := by
  intro cell member
  refine ⟨?_, ?_⟩
  · intro value expected
    have namedMember : cell.name ∈ sharedSlotTypes.map Prod.fst :=
      List.mem_map.mpr ⟨(cell.name, cell.type), shared_description_member description member, rfl⟩
    unfold passiveExpected at expected
    split at expected <;> first
      | contradiction
      | (cases expected; exact shared_description_value description member (index := 0) rfl rfl ‹cell.name = "world"›)
      | (cases expected; exact shared_description_value description member (index := 1) rfl rfl ‹cell.name = "worldComplete"›)
      | (cases expected; exact shared_description_value description member (index := 2) rfl rfl ‹cell.name = "logs"›)
      | (cases expected; exact shared_description_value description member (index := 3) rfl rfl ‹cell.name = "logSize"›)
      | (cases expected; exact shared_description_value description member (index := 4) rfl rfl ‹cell.name = "balances"›)
      | (simp_all [sharedSlotTypes, Ambient.slots])
  · intro _ _
    have below := initialized.location_bound member
    exact ⟨Nat.ne_of_lt below, by omega⟩

theorem shared_name_present {depth : Nat} {environment : Core.Environment} {context : Code}
    {shared : AccountRuntime.References} {cells : List InitializedCell}
    {initialValues : List Core.Value}
    (related : RuntimeReferences depth environment shared cells)
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip initialValues).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse)
    {index : Nat} {name : String} {value : Core.Value}
    (knownName : (sharedSlotTypes.map Prod.fst)[index]? = some name)
    (knownValue : initialValues[index]? = some value) : shared.find? (·.1 == name) ≠ none := by
  intro absent
  obtain ⟨cell, member, named, _⟩ := shared_description_cell description knownName knownValue
  have nameMember : name ∈ shared.map Prod.fst := by
    rw [related.names]
    exact List.mem_map.mpr ⟨cell, member, named⟩
  obtain ⟨entry, member, named⟩ := List.mem_map.mp nameMember
  exact List.find?_eq_none.mp absent entry member (by simpa only [beq_iff_eq] using named)

theorem fresh_initializers_observation {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {frame dispatcher gas code codeSize codeKnown context : Code} {values : List Core.Value}
    {gasValue codeValue sizeValue knownValue : Core.Value}
    {shared : AccountRuntime.References} {cells : List InitializedCell}
    {accounts : StorageCorrespondence.Accounts} {address : Core.Word} {complete : Bool}
    {balances : StorageSemantics.Words} {ambient : List Core.Value}
    (frameRelated : CodeValue depth environment frame (bundleValues values)) (length : values.length = 8)
    (addressFound : values[0]? = some (.word address))
    (gasRelated : CodeValue depth environment gas gasValue)
    (codeRelated : CodeValue depth environment code codeValue)
    (sizeRelated : CodeValue depth environment codeSize sizeValue)
    (knownRelated : CodeValue depth environment codeKnown knownValue)
    (references : RuntimeReferences depth environment shared cells)
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip (sharedValues accounts complete balances ambient)).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse) :
    FrameInitializersValid depth environment
      (store ++ [Core.WordMapping.encode [], .word (Core.Word.ofNatModulo 0)])
      frame dispatcher gas code codeSize codeKnown shared
      (initializedObservation store.length accounts address complete balances) := by
  apply frameInitializers_valid frameRelated length gasRelated codeRelated sizeRelated knownRelated
  intro name type location value absent below known
  refine ⟨?_, ?_⟩
  · intro expected specified
    change passiveExpected accounts address complete balances name = some expected at specified
    change value = expected
    unfold passiveExpected at specified
    split at specified <;> first
      | contradiction
      | (exact False.elim (shared_name_present references description (index := 0) rfl rfl absent))
      | (exact False.elim (shared_name_present references description (index := 1) rfl rfl absent))
      | (exact False.elim (shared_name_present references description (index := 2) rfl rfl absent))
      | (exact False.elim (shared_name_present references description (index := 3) rfl rfl absent))
      | (exact False.elim (shared_name_present references description (index := 4) rfl rfl absent))
      | (cases specified; exact known _ addressFound)
      | (cases specified; exact known _ rfl)
  · intro _ _
    simp only [List.length_append, List.length_cons, List.length_nil] at below
    change location ≠ store.length ∧ location ≠ store.length + 1
    exact ⟨by omega, by omega⟩

theorem creator_observation {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {creator : Code} {location : Nat} {value : Core.Value} {slots : List (String × Core.Ty)}
    (related : CodeValue depth environment creator
      (.cellRef (Core.OptionalCell.cellType Creation.callbackType) location))
    (stored : store.read? location = some value)
    (typed : ∀ type, ("createHandler", type) ∈ slots → type = Core.OptionalCell.cellType Creation.callbackType)
    (accounts : StorageCorrespondence.Accounts) (address : Core.Word) (complete : Bool)
    (balances : StorageSemantics.Words) :
    FrameCreatorValid depth environment store slots creator
      (initializedObservation store.length accounts address complete balances) := by
  intro type member
  cases typed type member
  refine ⟨⟨"createHandler", _, location, value⟩, rfl, rfl, related, stored, ?_⟩
  refine ⟨?_, ?_⟩
  · intro expected impossible; cases impossible
  · intro _ _
    have below := (List.getElem?_eq_some_iff.mp stored).1
    change location ≠ store.length ∧ location ≠ store.length + 1
    exact ⟨Nat.ne_of_lt below, by omega⟩

end Solcore.Frontend.RustHull.ContractMemoryCorrespondence
