import Solcore.Frontend.RustHull.ContractEnvironmentRuntimeFacts

/-! A supplied code image initializes the same independent environment
observations as its actual packed bytes, size and availability flag. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractEnvironmentCorrespondence
open Correspondence ScalarExecution CodeBuilder

private theorem shared_present_extended {depth : Nat} {environment : Core.Environment} {contextCode : Code}
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

theorem fresh_initializers_observation_image {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {frame dispatcher gas code codeSize codeKnown contextCode : Code}
    {shared : AccountRuntime.References} {cells : List InitializedCell}
    {accounts : StorageCorrespondence.Accounts} {complete : Bool} {balances : StorageSemantics.Words}
    (context : Contract.Context) (codeBytes : Option (List UInt8))
    (frameRelated : CodeValue depth environment frame
      (bundleValues (ContractMemoryCorrespondence.requestValues context)))
    (gasRelated : CodeValue depth environment gas (optionalWordValue context.availableGas))
    (codeRelated : CodeValue depth environment code (Core.WordMapping.encode (Memory.packBytes (codeBytes.getD []))))
    (sizeRelated : CodeValue depth environment codeSize (.word (Core.Word.ofNatModulo (codeBytes.getD []).length)))
    (knownRelated : CodeValue depth environment codeKnown (.bool codeBytes.isSome))
    (references : RuntimeReferences depth environment shared cells)
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip
        (ContractMemoryCorrespondence.sharedValues accounts complete balances (ambientValues context.ambient))).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse) :
    FrameInitializersValid depth environment store frame dispatcher gas code codeSize codeKnown shared
      (initializedValue (contextEnvironment context codeBytes)) := by
  apply frameInitializers_valid frameRelated rfl gasRelated codeRelated sizeRelated knownRelated
  intro name type location value absent _ known expected specified
  have notShared : name ∉ sharedSlotTypes.map Prod.fst :=
    fun member => shared_present_extended references description member absent
  change EnvironmentBuiltinCorrespondence.observation (contextEnvironment context codeBytes) name type = some expected at specified
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


end Solcore.Frontend.RustHull.ContractEnvironmentCorrespondence
