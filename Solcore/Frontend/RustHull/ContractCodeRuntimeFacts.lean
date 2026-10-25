import Solcore.Frontend.RustHull.ContractExtendedEnvironmentRuntimeFacts
import Solcore.Frontend.RustHull.ContractExtendedRuntimeInitializationCorrespondence

/-! The packed code image is a fresh immutable frame cell. Shared cells and
the creator callback cannot be mistaken for that image cell. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractCodeCorrespondence
open Correspondence ScalarExecution CodeBuilder

def initializedCode (image : Option (List UInt8)) (cell : InitializedCell) : Prop :=
  cell.name = "code" → cell.value = Core.WordMapping.encode (Memory.packBytes (image.getD []))

theorem fresh_code_observation {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {frame dispatcher gas code codeSize codeKnown : Code} {shared : AccountRuntime.References}
    {values : List Core.Value} {gasValue sizeValue knownValue : Core.Value} (image : Option (List UInt8))
    (frameRelated : CodeValue depth environment frame (bundleValues values)) (length : values.length = 8)
    (gasRelated : CodeValue depth environment gas gasValue)
    (codeRelated : CodeValue depth environment code (Core.WordMapping.encode (Memory.packBytes (image.getD []))))
    (sizeRelated : CodeValue depth environment codeSize sizeValue)
    (knownRelated : CodeValue depth environment codeKnown knownValue) :
    FrameInitializersValid depth environment store frame dispatcher gas code codeSize codeKnown shared (initializedCode image) := by
  apply frameInitializers_valid frameRelated length gasRelated codeRelated sizeRelated knownRelated
  intro name type location value _ _ observed named
  change name = "code" at named
  subst name
  exact observed _ rfl

theorem shared_code_observation {context : Code} {cells : List InitializedCell} {values : List Core.Value}
    (image : Option (List UInt8))
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip values).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse) :
    ∀ cell ∈ cells, initializedCode image cell := by
  intro cell member named
  have present := shared_description_member description member
  change cell.name = "code" at named
  rw [named] at present
  simp [sharedSlotTypes, Ambient.slots] at present

theorem creator_code_observation (image : Option (List UInt8)) (location : Nat) (value : Core.Value) :
    initializedCode image (ContractRuntimeEffectsCorrespondence.creatorCell location value) := by
  intro impossible
  simp [ContractRuntimeEffectsCorrespondence.creatorCell] at impossible

end Solcore.Frontend.RustHull.ContractCodeCorrespondence
