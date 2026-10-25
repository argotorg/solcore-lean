import Solcore.Frontend.RustHull.ChildFrameSemantics
import Solcore.Frontend.RustHull.ContractReturnDataInitializedExecution
import Solcore.Frontend.RustHull.RuntimeCallInitializedResources

/-! Child-frame observations follow the actual request and fresh allocator.
Shared observations describe the current parent state, including earlier logs
and storage writes, rather than a fresh transaction context. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildFrameCorrespondence
open Core Correspondence ScalarExecution CodeBuilder

abbrev Initial (parent : RuntimeCallEffectsSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8) :=
  (ChildFrameSemantics.initial parent request shared bytes).runtime

structure Observed (accounts : StorageCorrespondence.Accounts)
    (state : RuntimeReturnDataEffectsSemantics.State) (bytes : List UInt8) (cell : InitializedCell) : Prop where
  runtime : RuntimeInitializedEffects.Observed accounts state.runtime.runtime.runtime.runtime cell
  environment : ContractEnvironmentCorrespondence.initializedValue state.runtime.runtime.runtime.environment cell
  code : ContractCodeCorrespondence.initializedCode (some bytes) cell
  known : cell.name = "codeKnown" → cell.value = .bool true
  data : ContractReturnDataCorrespondence.initializedReturnData cell
  logs : cell.name = "logs" → cell.value = WordMapping.encode state.runtime.runtime.words
  logSize : cell.name = "logSize" → cell.value = .word state.runtime.runtime.cursor
  balances : cell.name = "balances" → cell.value = WordMapping.encode state.runtime.balances

theorem absent_shared_name {shared : AccountRuntime.References} {name : String}
    (names : shared.map Prod.fst = (sharedSlotTypes.map Prod.fst).reverse)
    (absent : shared.find? (·.1 == name) = none) : name ∉ sharedSlotTypes.map Prod.fst := by
  intro member
  have present : name ∈ shared.map Prod.fst := by rw [names]; exact List.mem_reverse.mpr member
  obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp present
  have rejected := List.find?_eq_none.mp absent entry entryMember
  simp only [same, beq_self_eq_true] at rejected
  contradiction

theorem fresh_observed {depth : Nat} {environment : Environment} {store : Store}
    {frame dispatcher gas code size known : Code} {shared : AccountRuntime.References}
    (parent : RuntimeCallEffectsSemantics.State) (request : AccountCallSemantics.Request)
    (sharedState : AccountCallSemantics.Shared) (bytes : List UInt8) (accounts : StorageCorrespondence.Accounts)
    (names : shared.map Prod.fst = (sharedSlotTypes.map Prod.fst).reverse)
    (frameRelated : CodeValue depth environment frame (CallTransportCorrespondence.requestValue request))
    (gasRelated : CodeValue depth environment gas (optionalWordValue (some request.gas)))
    (codeRelated : CodeValue depth environment code (WordMapping.encode (Memory.packBytes bytes)))
    (sizeRelated : CodeValue depth environment size (.word (Word.ofNatModulo bytes.length)))
    (knownRelated : CodeValue depth environment known (.bool true)) :
    FrameInitializersValid depth environment store frame dispatcher gas code size known shared
      (Observed accounts (Initial parent request sharedState bytes) bytes) := by
  apply frameInitializers_valid frameRelated rfl gasRelated codeRelated sizeRelated knownRelated
  intro name type location value absent _ observed
  have notShared := absent_shared_name names absent
  have sharedNames : ∀ selected ∈ ["world", "worldComplete", "logs", "logSize", "balances"], name ≠ selected := by
    intro selected member same
    apply notShared
    rw [same]
    simpa only [sharedSlotTypes, Ambient.slots, List.map_cons, List.map_nil, List.map_append,
      List.mem_cons, List.mem_append, List.not_mem_nil, or_false] using
      (List.mem_append_left (Ambient.slots.map Prod.fst) member)
  constructor
  · intro expected specified
    change RuntimeInitializedEffects.expected accounts
      (Initial parent request sharedState bytes).runtime.runtime.runtime.runtime name = some expected at specified
    change value = expected
    unfold RuntimeInitializedEffects.expected at specified
    split at specified <;> first
      | contradiction
      | (cases specified; exact observed _ rfl)
      | exact False.elim (sharedNames _ (by simp) ‹name = _›)
  · intro expected specified
    change EnvironmentBuiltinCorrespondence.observation
      (Initial parent request sharedState bytes).runtime.runtime.runtime.environment name type = some expected at specified
    change value = expected
    unfold EnvironmentBuiltinCorrespondence.observation at specified
    split at specified
    all_goals first
      | contradiction
      | (cases specified; exact observed _ (by simp [frameExpected, Initial, ChildFrameSemantics.initial, *] <;> rfl))
      | (simp_all [sharedSlotTypes, Ambient.slots])
    obtain ⟨_, rfl⟩ := specified
    exact observed _ rfl
  · intro named
    change name = "code" at named
    subst name
    exact observed _ rfl
  · intro named
    change name = "codeKnown" at named
    subst name
    exact observed _ rfl
  · intro named
    change name = "returnData" at named
    subst name
    exact observed _ rfl
  · exact fun named => False.elim (sharedNames _ (by simp) named)
  · exact fun named => False.elim (sharedNames _ (by simp) named)
  · exact fun named => False.elim (sharedNames _ (by simp) named)

theorem creator_observed (accounts : StorageCorrespondence.Accounts)
    (state : RuntimeReturnDataEffectsSemantics.State) (bytes : List UInt8) (location : Nat) (value : Value) :
    Observed accounts state bytes (ContractRuntimeEffectsCorrespondence.creatorCell location value) := by
  constructor
  · intro expected impossible; cases impossible
  · intro expected impossible; cases impossible
  · exact ContractCodeCorrespondence.creator_code_observation (some bytes) location value
  · intro impossible; simp [ContractRuntimeEffectsCorrespondence.creatorCell] at impossible
  · exact ContractReturnDataCorrespondence.creator_returnData_observation location value
  · intro impossible; simp [ContractRuntimeEffectsCorrespondence.creatorCell] at impossible
  · intro impossible; simp [ContractRuntimeEffectsCorrespondence.creatorCell] at impossible
  · intro impossible; simp [ContractRuntimeEffectsCorrespondence.creatorCell] at impossible

end Solcore.Frontend.RustHull.ChildFrameCorrespondence
