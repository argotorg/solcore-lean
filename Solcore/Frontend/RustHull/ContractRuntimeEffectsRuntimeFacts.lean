import Solcore.Frontend.RustHull.ContractRuntimeEffectsCorrespondence
import Solcore.Frontend.RustHull.ContractMemoryExecutionCorrespondence
import Solcore.Frontend.RustHull.RuntimeInitializedEffects

/-! The shared references and fresh frame initializers establish the concrete
initial memory, storage and unchanged snapshot fields for public execution. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractRuntimeEffectsCorrespondence
open Correspondence ScalarExecution CodeBuilder

def initialState (accounts : StorageCorrespondence.Accounts) (address : Core.Word)
    (complete isStatic : Bool) : RuntimeEffectsSemantics.State :=
  ⟨⟨[], Core.Word.ofNatModulo 0⟩, {world := accounts.map Prod.fst, address := address, complete := complete, isStatic := isStatic}⟩

def contextInitialState (object : Contract.CompiledObject) (context : Contract.Context) : RuntimeEffectsSemantics.State :=
  initialState (StorageCorrespondence.canonical (object.initialWorld context)) context.address context.completeWorld context.isStatic

def initializedValue (accounts : StorageCorrespondence.Accounts) (address : Core.Word)
    (complete isStatic : Bool) (balances : StorageSemantics.Words) (cell : InitializedCell) : Prop :=
  RuntimeInitializedEffects.Observed accounts (initialState accounts address complete isStatic) cell ∧
  (∀ name ∈ RuntimeEffectsFrameCorrespondence.passiveSnapshotNames, cell.name = name → cell.value = passiveValues balances name)

def initializedObservation (accounts : StorageCorrespondence.Accounts) (address : Core.Word)
    (complete isStatic : Bool) (balances : StorageSemantics.Words) (worldLocation balancesLocation : Nat)
    (cell : InitializedCell) : Prop :=
  initializedValue accounts address complete isStatic balances cell ∧
  (cell.name = "world" → cell.location = worldLocation) ∧
  (cell.name = "balances" → cell.location = balancesLocation)

theorem shared_initialized_value {context : Code} {cells : List InitializedCell}
    {accounts : StorageCorrespondence.Accounts} {address : Core.Word} {complete isStatic : Bool}
    {balances : StorageSemantics.Words} {ambient : List Core.Value}
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip (ContractMemoryCorrespondence.sharedValues accounts complete balances ambient)).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse) :
    ∀ cell ∈ cells, initializedValue accounts address complete isStatic balances cell := by
  intro cell member
  constructor
  · intro value expected
    have namedMember : cell.name ∈ sharedSlotTypes.map Prod.fst :=
      List.mem_map.mpr ⟨(cell.name, cell.type), shared_description_member description member, rfl⟩
    unfold RuntimeInitializedEffects.expected at expected
    split at expected <;> first
      | contradiction
      | (cases expected; exact shared_description_value description member (index := 0) rfl rfl ‹cell.name = "world"›)
      | (cases expected; exact shared_description_value description member (index := 1) rfl rfl ‹cell.name = "worldComplete"›)
      | (simp_all [sharedSlotTypes, Ambient.slots])
  · intro name present named
    simp only [RuntimeEffectsFrameCorrespondence.passiveSnapshotNames, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl
    · exact shared_description_value description member (index := 2) rfl rfl named
    · exact shared_description_value description member (index := 3) rfl rfl named
    · exact shared_description_value description member (index := 4) rfl rfl named

theorem fresh_initializers_observation {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {frame dispatcher gas code codeSize codeKnown context : Code} {values : List Core.Value}
    {gasValue codeValue sizeValue knownValue : Core.Value}
    {shared : AccountRuntime.References} {cells : List InitializedCell}
    {accounts : StorageCorrespondence.Accounts} {address : Core.Word} {complete isStatic : Bool}
    {balances : StorageSemantics.Words} {ambient : List Core.Value} {worldLocation balancesLocation : Nat}
    (frameRelated : CodeValue depth environment frame (bundleValues values)) (length : values.length = 8)
    (addressFound : values[0]? = some (.word address)) (staticFound : values[3]? = some (.bool isStatic))
    (gasRelated : CodeValue depth environment gas gasValue)
    (codeRelated : CodeValue depth environment code codeValue)
    (sizeRelated : CodeValue depth environment codeSize sizeValue)
    (knownRelated : CodeValue depth environment codeKnown knownValue)
    (references : RuntimeReferences depth environment shared cells)
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip (ContractMemoryCorrespondence.sharedValues accounts complete balances ambient)).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse) :
    FrameInitializersValid depth environment store frame dispatcher gas code codeSize codeKnown shared
      (initializedObservation accounts address complete isStatic balances worldLocation balancesLocation) := by
  apply frameInitializers_valid frameRelated length gasRelated codeRelated sizeRelated knownRelated
  intro name type location value absent _ known
  have absentWorld : name ≠ "world" := by
    intro same
    exact ContractMemoryCorrespondence.shared_name_present references description (index := 0) rfl rfl (same ▸ absent)
  have absentComplete : name ≠ "worldComplete" := by
    intro same
    exact ContractMemoryCorrespondence.shared_name_present references description (index := 1) rfl rfl (same ▸ absent)
  have absentLogs : name ≠ "logs" := by
    intro same
    exact ContractMemoryCorrespondence.shared_name_present references description (index := 2) rfl rfl (same ▸ absent)
  have absentLogSize : name ≠ "logSize" := by
    intro same
    exact ContractMemoryCorrespondence.shared_name_present references description (index := 3) rfl rfl (same ▸ absent)
  have absentBalances : name ≠ "balances" := by
    intro same
    exact ContractMemoryCorrespondence.shared_name_present references description (index := 4) rfl rfl (same ▸ absent)
  refine ⟨⟨?_, ?_⟩, fun same => False.elim (absentWorld same), fun same => False.elim (absentBalances same)⟩
  · intro expected specified
    change RuntimeInitializedEffects.expected accounts (initialState accounts address complete isStatic) name = some expected at specified
    change value = expected
    unfold RuntimeInitializedEffects.expected at specified
    split at specified <;> first
      | contradiction
      | (cases specified; exact known _ addressFound)
      | (cases specified; exact known _ staticFound)
      | (cases specified; exact known _ rfl)
  · intro selected present named
    simp only [RuntimeEffectsFrameCorrespondence.passiveSnapshotNames, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl
    · exact False.elim (absentLogs named)
    · exact False.elim (absentLogSize named)
    · exact False.elim (absentBalances named)

theorem shared_initializers_valid {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {context : Code} {shared : AccountRuntime.References} {cells known : List InitializedCell}
    {accounts : StorageCorrespondence.Accounts} {address : Core.Word} {complete isStatic : Bool}
    {balances : StorageSemantics.Words} {ambient : List Core.Value} {worldLocation balancesLocation : Nat}
    (references : RuntimeReferences depth environment shared cells)
    (initialized : InitializedCells cells store)
    (included : ∀ cell ∈ cells, cell ∈ known)
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip (ContractMemoryCorrespondence.sharedValues accounts complete balances ambient)).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse)
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type worldLocation))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type balancesLocation)) :
    FrameSharedValid depth environment store Effects.slots shared
      (fun cell => initializedObservation accounts address complete isStatic balances worldLocation balancesLocation cell ∧ cell ∈ known) := by
  intro slot slotMember foundName reference found
  obtain ⟨cell, member, named, related⟩ := references.find found
  have typed := sharedSlotTypes_compatible (List.mem_append_left _ slotMember)
    (shared_description_member description member) named
  refine ⟨cell, named, typed, related, initialized cell member, ⟨⟨shared_initialized_value description cell member, ?_, ?_⟩, included cell member⟩⟩
  · intro worldName
    have slotName : slot.1 = "world" := named.symm.trans worldName
    have selected : CodeValue depth environment (AccountRuntime.reference shared "world") cell.reference := by
      simpa only [AccountRuntime.reference, ← slotName, found, Option.map_some, Option.getD_some] using related
    exact (Core.Value.cellRef.inj (Core.evaluation_deterministic
      (selected.evaluates store) (worldReference.evaluates store)).1).2
  · intro balancesName
    have slotName : slot.1 = "balances" := named.symm.trans balancesName
    have selected : CodeValue depth environment (AccountRuntime.reference shared "balances") cell.reference := by
      simpa only [AccountRuntime.reference, ← slotName, found, Option.map_some, Option.getD_some] using related
    exact (Core.Value.cellRef.inj (Core.evaluation_deterministic
      (selected.evaluates store) (balancesReference.evaluates store)).1).2

def creatorCell (location : Nat) (value : Core.Value) : InitializedCell :=
  ⟨"createHandler", Core.OptionalCell.cellType Creation.callbackType, location, value⟩

theorem creator_initialized_valid {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {creator : Code} {location : Nat} {value : Core.Value} {known : List InitializedCell}
    (related : CodeValue depth environment creator (.cellRef (Core.OptionalCell.cellType Creation.callbackType) location))
    (stored : store.read? location = some value) (member : creatorCell location value ∈ known)
    (accounts : StorageCorrespondence.Accounts) (address : Core.Word) (complete isStatic : Bool)
    (balances : StorageSemantics.Words) (worldLocation balancesLocation : Nat) :
    FrameCreatorValid depth environment store Effects.slots creator
      (fun cell => initializedObservation accounts address complete isStatic balances worldLocation balancesLocation cell ∧ cell ∈ known) := by
  intro type present
  have typed : ∀ slot ∈ Effects.slots, slot.1 = "createHandler" → slot.2 = Core.OptionalCell.cellType Creation.callbackType := by decide
  cases typed ("createHandler", type) present rfl
  refine ⟨creatorCell location value, rfl, rfl, related, stored, ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, member⟩⟩
  · intro expected impossible; cases impossible
  · intro name present named
    simp only [RuntimeEffectsFrameCorrespondence.passiveSnapshotNames, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl <;> simp [creatorCell] at named
  · intro impossible; simp [creatorCell] at impossible
  · intro impossible; simp [creatorCell] at impossible

theorem known_initialized {cells : List InitializedCell} {store : Core.Store} {location : Nat} {value : Core.Value}
    (initialized : InitializedCells cells store) (stored : store.read? location = some value) :
    InitializedCells (cells ++ [creatorCell location value]) store := by
  intro cell member
  rcases List.mem_append.mp member with member | member
  · exact initialized cell member
  · have same := List.mem_singleton.mp member
    subst cell
    exact stored

theorem known_separate {cells : List InitializedCell} {location : Nat} {value : Core.Value}
    (separate : CellLocations cells) (below : ∀ cell ∈ cells, cell.location < location) :
    CellLocations (cells ++ [creatorCell location value]) := by
  intro left member right member' same
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member' with member' | member'
    · exact separate left member right member' same
    · have rightEq := List.mem_singleton.mp member'
      subst right
      exact False.elim ((Nat.ne_of_lt (below left member)) same)
  · have leftEq := List.mem_singleton.mp member
    subst left
    rcases List.mem_append.mp member' with member' | member'
    · exact False.elim ((Nat.ne_of_lt (below right member')) same.symm)
    · have rightEq := List.mem_singleton.mp member'
      subst right
      rfl

end Solcore.Frontend.RustHull.ContractRuntimeEffectsCorrespondence
