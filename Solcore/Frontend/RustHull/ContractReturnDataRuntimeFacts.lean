import Solcore.Frontend.RustHull.ContractExtendedEnvironmentRuntimeFacts
import Solcore.Frontend.RustHull.ContractExtendedRuntimeInitializationCorrespondence

/-! The actual frame allocator starts with empty return data. Its size follows
from the existing environment observation, for either ordinary or code slots. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractReturnDataCorrespondence
open Correspondence ScalarExecution CodeBuilder RuntimeInitializedEffects

def initializedReturnData (cell : InitializedCell) : Prop :=
  cell.name = "returnData" → cell.value = Core.WordMapping.encode []

theorem fresh_returnData_observation {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {frame dispatcher gas code codeSize codeKnown : Code} {shared : AccountRuntime.References}
    {values : List Core.Value} {gasValue codeValue sizeValue knownValue : Core.Value}
    (frameRelated : CodeValue depth environment frame (bundleValues values)) (length : values.length = 8)
    (gasRelated : CodeValue depth environment gas gasValue)
    (codeRelated : CodeValue depth environment code codeValue)
    (sizeRelated : CodeValue depth environment codeSize sizeValue)
    (knownRelated : CodeValue depth environment codeKnown knownValue) :
    FrameInitializersValid depth environment store frame dispatcher gas code codeSize codeKnown shared
      initializedReturnData := by
  apply frameInitializers_valid frameRelated length gasRelated codeRelated sizeRelated knownRelated
  intro name type location value _ _ observed named
  change name = "returnData" at named
  subst name
  exact observed _ rfl

theorem shared_returnData_observation {context : Code} {cells : List InitializedCell} {values : List Core.Value}
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip values).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse) :
    ∀ cell ∈ cells, initializedReturnData cell := by
  intro cell member named
  have present := shared_description_member description member
  change cell.name = "returnData" at named
  rw [named] at present
  simp [sharedSlotTypes, Ambient.slots] at present

theorem creator_returnData_observation (location : Nat) (value : Core.Value) :
    initializedReturnData (ContractRuntimeEffectsCorrespondence.creatorCell location value) := by
  intro impossible
  simp [ContractRuntimeEffectsCorrespondence.creatorCell] at impossible

/-- The size observation uses the actual cell type, so additional slots need
not satisfy a separate global name-uniqueness assumption. -/
theorem initialized_returnDataSize {context : Contract.Context} {image : Option (List UInt8)}
    {cell : InitializedCell}
    (observed : ContractEnvironmentCorrespondence.initializedValue
      (ContractEnvironmentCorrespondence.contextEnvironment context image) cell)
    (named : cell.name = "returnDataSize") (typed : cell.type = .word) :
    cell.value = .word Core.Word.zero := by
  apply observed
  simp only [named, typed, EnvironmentBuiltinCorrespondence.observation,
    ContractEnvironmentCorrespondence.contextEnvironment]

/-- The ordinary prefix provides a typed cell even when arbitrary extra slots
follow it. The value is read from the actual initialized store. -/
theorem observe_base {cells : List InitializedCell} {store : Core.Store} {extra : List (String × Core.Ty)}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots ++ extra)
    (initialized : InitializedCells cells store)
    {name : String} {type : Core.Ty} {value : Core.Value}
    (member : (name, type) ∈ Effects.slots)
    (observed : ∀ cell ∈ cells, cell.name = name → cell.type = type → cell.value = value) :
    Nonempty (Cell cells store name type value) := by
  have present := List.mem_append_left extra member
  rw [← signature] at present
  obtain ⟨cell, cellMember, same⟩ := List.mem_map.mp present
  obtain ⟨named, typed⟩ := Prod.mk.inj same
  exact ⟨cell, cellMember, named, typed,
    by simpa only [observed cell cellMember named typed] using initialized cell cellMember⟩

theorem data_cell {cells : List InitializedCell} {store : Core.Store} {extra : List (String × Core.Ty)}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots ++ extra)
    (initialized : InitializedCells cells store)
    (observed : ∀ cell ∈ cells, initializedReturnData cell) :
    Nonempty (Cell cells store "returnData" Core.WordMapping.type (Core.WordMapping.encode [])) :=
  observe_base signature initialized (by simp [Effects.slots])
    (fun cell member named _ => observed cell member named)

theorem size_cell {cells : List InitializedCell} {store : Core.Store} {extra : List (String × Core.Ty)}
    {context : Contract.Context} {image : Option (List UInt8)}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots ++ extra)
    (initialized : InitializedCells cells store)
    (observed : ∀ cell ∈ cells, ContractEnvironmentCorrespondence.initializedValue
      (ContractEnvironmentCorrespondence.contextEnvironment context image) cell) :
    Nonempty (Cell cells store "returnDataSize" .word (.word Core.Word.zero)) :=
  observe_base signature initialized (by simp [Effects.slots])
    (fun cell member named typed => initialized_returnDataSize (observed cell member) named typed)

/-- The two actual cells are separated by their allocated names. -/
theorem cells_distinct {cells : List InitializedCell} {store : Core.Store}
    {words : MemorySemantics.Entries} {size : Core.Word}
    (separate : CellLocations cells)
    (data : Cell cells store "returnData" Core.WordMapping.type (Core.WordMapping.encode words))
    (length : Cell cells store "returnDataSize" .word (.word size)) :
    data.cell.location ≠ length.cell.location :=
  separate.different data.member length.member (by simp only [data.named, length.named]; decide)

end Solcore.Frontend.RustHull.ContractReturnDataCorrespondence
