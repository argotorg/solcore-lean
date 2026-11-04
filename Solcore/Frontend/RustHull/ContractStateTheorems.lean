import Solcore.Frontend.RustHull.Internal.RuntimeObjects
import Solcore.Frontend.RustHull.Internal.EffectLayers
import Solcore.Frontend.RustHull.Internal.TerminationLayers
import Solcore.Frontend.RustHull.Internal.AccountLayers

/-!
# Hull contract meaning preservation: state effects

The public contract theorems for memory, storage, environment, logs, termination, copies, hashing
and account observation. The `prepare_resumes_exact` theorem of each layer connects an independent
derivation to `Contract.prepare`, `Contract.runWithReceipt` and every chain of
`Contract.resumeWithReceipt`. Main theorems: `ContractMemoryCorrespondence.prepare_resumes_exact`,
`ContractRuntimeEffectsCorrespondence.prepare_resumes_exact`,
`ContractEnvironmentCorrespondence.prepare_resumes_exact`,
`ContractLogCorrespondence.prepare_resumes_exact`,
`ContractFullCorrespondence.prepare_resumes_exact`,
`ContractCopyCorrespondence.prepare_resumes_exact`,
`ContractHashCorrespondence.prepare_resumes_exact`,
`ContractAccountCorrespondence.prepare_resumes_exact`.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractMemoryRuntimeFacts
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractMemoryExecutionCorrespondence
/-! The actual public object expression executes source memory derivations
from its own context and allocation, then exports the corresponding message. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractMemoryCorrespondence
open Correspondence ScalarExecution CodeBuilder

def requestCode (context : Code) : Code :=
  packet [part 4 12 context, part 3 12 context, part 2 12 context, part 8 12 context,
    number 0, number 0, part 0 12 context, part 1 12 context]

def requestValues (context : Contract.Context) : List Core.Value :=
  [.word context.address, .word context.caller, .word context.value, .bool context.isStatic,
   .word (Core.Word.ofNatModulo 0), .word (Core.Word.ofNatModulo 0),
   Core.WordMapping.encode (Contract.calldataEntries context.calldata), .word (Core.Word.ofNatModulo context.calldata.length)]

def contextSharedValues (compiled : Contract.CompiledObject) (context : Contract.Context) : List Core.Value :=
  [StorageCorrespondence.world (StorageCorrespondence.canonical (compiled.initialWorld context)), .bool context.completeWorld,
   Core.WordMapping.encode [], .word (Core.Word.ofNatModulo 0),
   Core.WordMapping.encode (Core.WordMapping.insertEntries context.address context.balance context.accounts)] ++
   ambientValues context.ambient

theorem request_related {depth : Nat} {environment : Core.Environment} {contextCode : Code}
    (compiled : Contract.CompiledObject) (context : Contract.Context)
    (related : CodeValue depth environment contextCode (bundleValues (contextValues compiled context))) :
    CodeValue depth environment (requestCode contextCode) (bundleValues (requestValues context)) := by
  apply CodeValue.packet
  exact .cons (related.part (index := 4) rfl)
    (.cons (related.part (index := 3) rfl) (.cons (related.part (index := 2) rfl)
    (.cons (related.part (index := 8) rfl) (.cons (CodeValue.number 0 depth environment)
    (.cons (CodeValue.number 0 depth environment) (.cons (related.part (index := 0) rfl)
    (.cons (related.part (index := 1) rfl) .nil)))))))

theorem sharedValues_related {depth : Nat} {environment : Core.Environment} {contextCode : Code}
    (compiled : Contract.CompiledObject) (context : Contract.Context)
    (related : CodeValue depth environment contextCode (bundleValues (contextValues compiled context))) :
    CodeValues depth environment ((AccountRuntime.sharedInitializers contextCode).map (·.2.2))
      (contextSharedValues compiled context) :=
  sharedInitializers_values related rfl rfl (by rfl) (by rfl) (by rfl) (by rfl)

theorem objectFrame_evaluates_ready {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code Effects.slots fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram MemoryEffectCorrespondence.supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment captured : Core.Environment} {initial : Core.Store}
    {context functions dispatcher creator : Code} {shared : AccountRuntime.References}
    {closure : Core.Value} (closureRelated : CapturedClosure compiled captured closure)
    (functionsRelated : CodeValue depth environment functions closure)
    {contextValues : List Core.Value}
    (contextRelated : CodeValue depth environment context (bundleValues contextValues))
    (contextLength : contextValues.length = 12)
    (accounts : StorageCorrespondence.Accounts) (address : Core.Word) (complete : Bool) (balances : StorageSemantics.Words)
    (addressValue : contextValues[4]? = some (.word address))
    (deployingValue : contextValues[11]? = some (.bool false))
    (initializers : FrameInitializersValid depth environment
      (initial ++ [Core.WordMapping.encode [], .word (Core.Word.ofNatModulo 0)])
      (requestCode context) dispatcher (part 5 12 context) (constant (Core.WordMapping.literal []))
      (number 0) (CodeBuilder.boolean false) shared
      (initializedObservation initial.length accounts address complete balances))
    (sharedReady : FrameSharedValid depth environment initial Effects.slots.tail.tail shared
      (initializedObservation initial.length accounts address complete balances))
    (creatorReady : FrameCreatorValid depth environment initial Effects.slots.tail.tail creator
      (initializedObservation initial.length accounts address complete balances))
    (memoryAbsent : shared.find? (·.1 == "memory") = none)
    (sizeAbsent : shared.find? (·.1 == "memorySize") = none)
    {worldLocation balancesLocation : Nat}
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type worldLocation))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type balancesLocation))
    (worldFound : initial.read? worldLocation = some (StorageCorrespondence.world accounts))
    (balancesFound : initial.read? balancesLocation = some (Core.WordMapping.encode balances))
    {finalSource : Semantics.State MemorySemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) MemorySemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], ⟨[], Core.Word.ofNatModulo 0⟩⟩ sourceResult finalSource) :
    ∃ final, Core.Evaluates environment initial
      (AccountRuntime.objectFrame Effects.slots 1 [] none context functions shared dispatcher creator depth)
      (messageValue sourceResult finalSource.external accounts address complete balances) final := by
  obtain ⟨extra, suffix, references, cells, referenceValues, initialized, names, observations, memoryInitial, continued⟩ :=
    allocateFrame_memory_validates initializers sharedReady creatorReady memoryAbsent sizeAbsent
      (initializedObservation_memory initial accounts address complete balances)
      (initializedObservation_size initial accounts address complete balances)
  let allCells := initialMemoryCell initial :: initialSizeCell initial :: cells
  have allNames : allCells.map (fun cell => (cell.name, cell.type)) = Effects.slots := by
    change ("memory", Core.WordMapping.type) :: ("memorySize", Core.Ty.word) :: cells.map (fun cell => (cell.name, cell.type)) = _
    rw [names]
    rfl
  have plainNames : allCells.map InitializedCell.name = Effects.slots.map Prod.fst := by
    simpa only [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) allNames
  let slots := allCells.map InitializedCell.effectSlot
  have slotTypes : MemoryFrameCorrespondence.slotTypes slots = Effects.slots := by
    simpa only [MemoryFrameCorrespondence.slotTypes, slots, List.map_map, Function.comp_def, InitializedCell.effectSlot] using allNames
  have environmentRelated := initialized_environment allCells (initialized_effects_unique allNames)
    (Core.Value.unit :: bundleValues (allCells.map InitializedCell.reference) :: captured)
  have runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (MemoryFrameCorrespondence.slotTypes slots)) Core.Renaming.id
      ((allCells.map InitializedCell.reference).reverse ++ Core.Value.unit :: bundleValues (allCells.map InitializedCell.reference) :: captured) := by
    simpa only [slots, MemoryFrameCorrespondence.slotTypes, List.map_map, Function.comp_def, InitializedCell.effectSlot] using environmentRelated
  have separated := initialized_effects_separate allNames
  have passive (name : String) (value : Core.Value) (member : name ∈ Effects.slots.map Prod.fst)
      (expected : passiveExpected accounts address complete balances name = some value) :=
    initializedObservation_passive memoryInitial initialized observations (plainNames.symm ▸ member) expected
  have targetRelated : CodeValue depth environment (part 4 12 context) (.word address) := by
    simpa only [contextLength] using contextRelated.part addressValue
  have deployingRelated : CodeValue depth environment (part 11 12 context) (.bool false) := by
    simpa only [contextLength] using contextRelated.part deployingValue
  have worldBound := (List.getElem?_eq_some_iff.mp worldFound).1
  have balancesBound := (List.getElem?_eq_some_iff.mp balancesFound).1
  obtain ⟨final, completed⟩ := frameCall_message_evaluates
    (by simpa only [slotTypes] using accepted) eligible closureRelated
    ((functionsRelated.prepend extra).evaluates (initial ++ suffix))
    ((CodeValue.packet referenceValues).evaluates (initial ++ suffix))
    (by simp [slots, allCells]) runtime separated
    (by exact List.mem_map.mpr ⟨initialMemoryCell initial, .head _, rfl⟩)
    (by exact List.mem_map.mpr ⟨initialSizeCell initial, .tail _ (.head _), rfl⟩)
    memoryInitial evaluated accounts address complete balances
    (passive "world" _ (by decide) rfl) (passive "address" _ (by decide) rfl)
    (passive "worldComplete" _ (by decide) rfl)
    (by
      intro name member notMemory
      apply passive name _ _ (snapshot_expected ⟨[], Core.Word.ofNatModulo 0⟩ accounts address complete balances name member notMemory)
      have present : ∀ name ∈ frameSnapshotNames, name ∈ Effects.slots.map Prod.fst := by decide
      exact present name member)
    (worldReference.prepend extra) (balancesReference.prepend extra)
    (targetRelated.prepend extra) (deployingRelated.prepend extra)
    (by simpa only [Core.Store.read?, List.getElem?_append_left worldBound] using worldFound)
    (by simpa only [Core.Store.read?, List.getElem?_append_left balancesBound] using balancesFound)
    (Nat.ne_of_lt worldBound) (Nat.ne_of_lt (Nat.lt_trans worldBound (Nat.lt_succ_self _)))
    (Nat.ne_of_lt balancesBound) (Nat.ne_of_lt (Nat.lt_trans balancesBound (Nat.lt_succ_self _)))
  exact ⟨final, continued _ _ _ completed⟩

theorem shared_reference_value {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {context : Code} {shared : AccountRuntime.References} {cells : List InitializedCell} {initialValues : List Core.Value}
    (references : RuntimeReferences depth environment shared cells) (initialized : InitializedCells cells initial)
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip initialValues).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse)
    {index : Nat} {name : String} {type : Core.Ty} {value : Core.Value}
    (knownName : (sharedSlotTypes.map Prod.fst)[index]? = some name)
    (knownValue : initialValues[index]? = some value)
    (knownType : ∀ slot ∈ sharedSlotTypes, slot.1 = name → slot.2 = type) :
    ∃ location, CodeValue depth environment (AccountRuntime.reference shared name) (.cellRef type location) ∧
      initial.read? location = some value := by
  obtain ⟨namedCell, namedMember, named, _⟩ := shared_description_cell description knownName knownValue
  obtain ⟨cell, member, selectedName, related⟩ := references.reference (List.mem_map.mpr ⟨namedCell, namedMember, named⟩)
  have typed : cell.type = type := knownType _ (shared_description_member description member) selectedName
  have valued := shared_description_value description member knownName knownValue selectedName
  exact ⟨cell.location, by simpa only [InitializedCell.reference, typed] using related,
    by simpa only [valued] using initialized cell member⟩

theorem shared_memory_absent {depth : Nat} {environment : Core.Environment}
    {context : Code} {shared : AccountRuntime.References} {cells : List InitializedCell} {initialValues : List Core.Value}
    (references : RuntimeReferences depth environment shared cells)
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip initialValues).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse) :
    shared.find? (·.1 == "memory") = none ∧ shared.find? (·.1 == "memorySize") = none := by
  have absent : ∀ slot ∈ sharedSlotTypes, slot.1 ≠ "memory" ∧ slot.1 ≠ "memorySize" := by decide
  exact ⟨references.absent "memory" (fun cell member => (absent _ (shared_description_member description member)).1),
    references.absent "memorySize" (fun cell member => (absent _ (shared_description_member description member)).2)⟩

theorem objectFrame_evaluates {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code Effects.slots fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram MemoryEffectCorrespondence.supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment captured : Core.Environment} {initial : Core.Store}
    {contextCode functions dispatcher creator : Code} {shared : AccountRuntime.References}
    {closure : Core.Value} (closureRelated : CapturedClosure compiled captured closure)
    (functionsRelated : CodeValue depth environment functions closure)
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    {cells : List InitializedCell} (references : RuntimeReferences depth environment shared cells)
    (initialized : InitializedCells cells initial)
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip (contextSharedValues object context)).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse)
    {creatorLocation : Nat}
    (creatorRelated : CodeValue depth environment creator (.cellRef (Core.OptionalCell.cellType Creation.callbackType) creatorLocation))
    (creatorFound : ∃ value, initial.read? creatorLocation = some value)
    {finalSource : Semantics.State MemorySemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) MemorySemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], ⟨[], Core.Word.ofNatModulo 0⟩⟩ sourceResult finalSource) :
    ∃ final, Core.Evaluates environment initial
      (AccountRuntime.objectFrame Effects.slots 1 [] none contextCode functions shared dispatcher creator depth)
      (messageValue sourceResult finalSource.external (StorageCorrespondence.canonical (object.initialWorld context))
        context.address context.completeWorld
        (Core.WordMapping.insertEntries context.address context.balance context.accounts)) final := by
  let accounts := StorageCorrespondence.canonical (object.initialWorld context)
  let balances := Core.WordMapping.insertEntries context.address context.balance context.accounts
  have description' : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip
        (sharedValues accounts context.completeWorld balances (ambientValues context.ambient))).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse := description
  have valid := shared_initialized_observation (address := context.address) description' initialized
  have fresh : FrameInitializersValid depth environment
      (initial ++ [Core.WordMapping.encode [], .word (Core.Word.ofNatModulo 0)])
      (requestCode contextCode) dispatcher (part 5 12 contextCode) (constant (Core.WordMapping.literal []))
      (number 0) (CodeBuilder.boolean false) shared
      (initializedObservation initial.length accounts context.address context.completeWorld balances) :=
    fresh_initializers_observation (request_related object context contextRelated) rfl rfl
      (contextRelated.part (index := 5) rfl) (CodeValue.mapping [] depth environment)
      (CodeValue.number 0 depth environment) (CodeValue.boolean false depth environment) references description'
  have sharedReady := references.sharedValid initialized
    (slots := Effects.slots.tail.tail)
    (fun slot member cell cellMember named => sharedSlotTypes_compatible
      (List.mem_append_left _ (List.mem_of_mem_tail (List.mem_of_mem_tail member)))
      (shared_description_member description cellMember) named) valid
  obtain ⟨creatorValue, creatorStored⟩ := creatorFound
  have creatorTyped : ∀ type, ("createHandler", type) ∈ Effects.slots.tail.tail →
      type = Core.OptionalCell.cellType Creation.callbackType := by
    have checked : ∀ slot ∈ Effects.slots.tail.tail, slot.1 = "createHandler" →
        slot.2 = Core.OptionalCell.cellType Creation.callbackType := by decide
    exact fun type member => checked ("createHandler", type) member rfl
  have creatorReady := creator_observation creatorRelated creatorStored creatorTyped accounts context.address context.completeWorld balances
  obtain ⟨memoryAbsent, sizeAbsent⟩ := shared_memory_absent references description
  obtain ⟨worldLocation, worldReference, worldFound⟩ := shared_reference_value references initialized description'
    (index := 0) rfl rfl (by decide : ∀ slot ∈ sharedSlotTypes, slot.1 = "world" → slot.2 = AccountState.type)
  obtain ⟨balancesLocation, balancesReference, balancesFound⟩ := shared_reference_value references initialized description'
    (index := 4) rfl rfl (by decide : ∀ slot ∈ sharedSlotTypes, slot.1 = "balances" → slot.2 = Core.WordMapping.type)
  exact objectFrame_evaluates_ready accepted eligible closureRelated functionsRelated contextRelated rfl
    accounts context.address context.completeWorld balances rfl (by simp only [contextValues, notDeploying]; rfl)
    fresh sharedReady creatorReady memoryAbsent sizeAbsent worldReference balancesReference worldFound balancesFound evaluated

theorem objectRuntime_preserves {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code Effects.slots fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram MemoryEffectCorrespondence.supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment : Core.Environment} {initial : Core.Store} {contextCode : Code}
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    {finalSource : Semantics.State MemorySemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) MemorySemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], ⟨[], Core.Word.ofNatModulo 0⟩⟩ sourceResult finalSource) :
    ∃ final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime Effects.slots compiled [] [] none [] contextCode depth)
      (messageValue sourceResult finalSource.external (StorageCorrespondence.canonical (object.initialWorld context))
        context.address context.completeWorld
        (Core.WordMapping.insertEntries context.address context.balance context.accounts)) final := by
  obtain ⟨closure, captured⟩ := compileFrame_captures accepted environment
  apply objectRuntime_evaluates_some (.cons captured .nil) (sharedValues_related object context contextRelated)
  intro functions shared dispatcher creator extra allocated cells _ creatorLocation functionsRelated references initialized description _ _ creatorRelated creatorFound
  exact objectFrame_evaluates accepted eligible captured functionsRelated object context notDeploying
    (contextRelated.prepend extra) references initialized description creatorRelated creatorFound evaluated

def publicMessageValue (object : Contract.CompiledObject) (context : Contract.Context)
    (result : Semantics.Result Semantics.Value) (memory : MemorySemantics.State) : Core.Value :=
  let normalized := Contract.normalizeContext context
  messageValue result memory (StorageCorrespondence.canonical (object.initialWorld normalized))
    normalized.address normalized.completeWorld
    (Core.WordMapping.insertEntries normalized.address normalized.balance normalized.accounts)

/-- Compilation and an independent Hull derivation suffice for the complete
publicly instantiated memory fragment. Runtime environments, cells and
initial memory are obtained from the actual object expression. -/
theorem compileObject_preserves {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {object : Contract.CompiledObject}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel none [] = .ok object)
    (eligible : DerivationCorrespondence.ExecutableProgram MemoryEffectCorrespondence.supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (context : Contract.Context) (notDeploying : context.deploying = false)
    {finalSource : Semantics.State MemorySemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) MemorySemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], ⟨[], Core.Word.ofNatModulo 0⟩⟩ sourceResult finalSource) :
    ∃ final, Core.Evaluates [] [] (object.instantiate context).expression
      (publicMessageValue object context sourceResult finalSource.external) final := by
  have compiled : AccountRuntime.compileObject program path fuel none [] = .ok object.expression := by
    unfold Contract.compileObject at accepted
    obtain ⟨expression, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
    cases returned
    exact compiled
  obtain ⟨frame, frameCompiled, objectExpression⟩ := compileObject_selected selected compiled
  have normalized : (Contract.normalizeContext context).deploying = false := notDeploying
  obtain ⟨final, executed⟩ := objectRuntime_preserves (by simpa using frameCompiled) eligible object
    (Contract.normalizeContext context) normalized
    (CodeValue.bound 0 [] (bundleValues (contextValues object (Contract.normalizeContext context)))) evaluated
  refine ⟨final, instantiate_evaluates context (parameter := AccountRuntime.contextType) (resultType := AccountRuntime.resultType) ?_ executed⟩
  rw [objectExpression]
  rfl

/-- Public execution and every genuine checkpoint chain agree with the source
message result at the cumulative number of Core transitions. -/
theorem compileObject_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {object : Contract.CompiledObject}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel none [] = .ok object)
    (eligible : DerivationCorrespondence.ExecutableProgram MemoryEffectCorrespondence.supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (context : Contract.Context) (notDeploying : context.deploying = false)
    {finalSource : Semantics.State MemorySemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) MemorySemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], ⟨[], Core.Word.ofNatModulo 0⟩⟩ sourceResult finalSource) :
    ∃ required, ∀ initialFuel additional limit last,
      Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
      (last = Contract.finish limit (publicMessageValue object context sourceResult finalSource.external) ↔
        required ≤ initialFuel + additional) ∧
      ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨_, executed⟩ := compileObject_preserves selected accepted eligible context notDeploying evaluated
  exact Contract.evaluation_resumes_exact executed

theorem prepare_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {context : Contract.Context} {prepared : Contract.Prepared}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.prepare program path context fuel = .ok prepared)
    (eligible : DerivationCorrespondence.ExecutableProgram MemoryEffectCorrespondence.supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (notDeploying : context.deploying = false)
    {finalSource : Semantics.State MemorySemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) MemorySemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], ⟨[], Core.Word.ofNatModulo 0⟩⟩ sourceResult finalSource) :
    ∃ object, Contract.compileObject program path fuel none [] = .ok object ∧
      prepared = object.instantiate context ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
        (last = Contract.finish limit (publicMessageValue object context sourceResult finalSource.external) ↔
          required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  unfold Contract.prepare at accepted
  obtain ⟨object, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
  cases returned
  exact ⟨object, compiled, rfl, compileObject_resumes_exact selected compiled eligible context notDeploying evaluated⟩

end Solcore.Frontend.RustHull.ContractMemoryCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractEnvironmentRuntimeFacts
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractRuntimeEffectsRuntimeFacts
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractRuntimeInitializationCorrespondence
/-! Reusable evaluation of the actual object frame initializer, with additional
resource observations carried to a source-driven continuation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractRuntimeEffectsCorrespondence
open Correspondence ScalarExecution CodeBuilder

theorem FrameInitializersValid.and {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {frame dispatcher gas code codeSize codeKnown : Code} {shared : AccountRuntime.References}
    {first second : InitializedCell → Prop}
    (left : FrameInitializersValid depth environment store frame dispatcher gas code codeSize codeKnown shared first)
    (right : FrameInitializersValid depth environment store frame dispatcher gas code codeSize codeKnown shared second) :
    FrameInitializersValid depth environment store frame dispatcher gas code codeSize codeKnown shared (fun cell => first cell ∧ second cell) := by
  intro extra suffix name type absent
  obtain ⟨value, evaluated, valid⟩ := left extra suffix name type absent
  obtain ⟨value', evaluated', valid'⟩ := right extra suffix name type absent
  have same := (Core.evaluation_deterministic evaluated evaluated').1
  subst value'
  exact ⟨value, evaluated, valid, valid'⟩

theorem objectFrame_initializes
    {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {contextCode functions dispatcher creator : Code} {shared : AccountRuntime.References}
    (object : Contract.CompiledObject) (context : Contract.Context)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    {sharedCells : List InitializedCell} (references : RuntimeReferences depth environment shared sharedCells)
    (initialized : InitializedCells sharedCells initial) (separate : CellLocations sharedCells)
    (description : sharedCells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip (ContractMemoryCorrespondence.contextSharedValues object context)).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse)
    {creatorLocation : Nat}
    (creatorRelated : CodeValue depth environment creator (.cellRef (Core.OptionalCell.cellType Creation.callbackType) creatorLocation))
    (creatorFound : ∃ value, initial.read? creatorLocation = some value)
    (creatorAfter : ∀ cell ∈ sharedCells, cell.location < creatorLocation)
    (property : InitializedCell → Prop) (observes : Core.Value → Core.Store → Prop)
    (freshExtra : FrameInitializersValid depth environment initial
      (ContractMemoryCorrespondence.requestCode contextCode) dispatcher (part 5 12 contextCode)
      (constant (Core.WordMapping.literal [])) (number 0) (CodeBuilder.boolean false) shared property)
    (sharedExtra : ∀ cell ∈ sharedCells, property cell)
    (creatorExtra : ∀ value, initial.read? creatorLocation = some value → property (creatorCell creatorLocation value))
    (continued : ∀ extra suffix frameReferences cells worldLocation balancesLocation,
      CodeValues (depth + extra.length) (extra ++ environment) frameReferences (cells.map InitializedCell.reference) →
      InitializedCells cells (initial ++ suffix) →
      cells.map (fun cell => (cell.name, cell.type)) = Effects.slots →
      (∀ cell ∈ cells, initializedObservation
        (StorageCorrespondence.canonical (object.initialWorld context)) context.address context.completeWorld context.isStatic
        (Core.WordMapping.insertEntries context.address context.balance context.accounts) worldLocation balancesLocation cell ∧ property cell) →
      CellLocations cells →
      CodeValue depth environment (AccountRuntime.reference shared "world") (.cellRef AccountState.type worldLocation) →
      CodeValue depth environment (AccountRuntime.reference shared "balances") (.cellRef Core.WordMapping.type balancesLocation) →
      initial.read? balancesLocation = some (Core.WordMapping.encode (Core.WordMapping.insertEntries context.address context.balance context.accounts)) →
      ∃ value final, Core.Evaluates (extra ++ environment) (initial ++ suffix)
        (bind (apply functions (packet frameReferences))
          (fun framed => AccountRuntime.completeMessage shared [] (part 4 12 contextCode) (part 11 12 contextCode) framed)
          (depth + extra.length)) value final ∧ observes value final) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectFrame Effects.slots 1 [] none contextCode functions shared dispatcher creator depth)
      value final ∧ observes value final := by
  let accounts := StorageCorrespondence.canonical (object.initialWorld context)
  let balances := Core.WordMapping.insertEntries context.address context.balance context.accounts
  have description' : sharedCells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip
        (ContractMemoryCorrespondence.sharedValues accounts context.completeWorld balances (ambientValues context.ambient))).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse := description
  obtain ⟨worldLocation, worldReference, worldFound⟩ := ContractMemoryCorrespondence.shared_reference_value references initialized description'
    (index := 0) rfl rfl (by decide : ∀ slot ∈ sharedSlotTypes, slot.1 = "world" → slot.2 = AccountState.type)
  obtain ⟨balancesLocation, balancesReference, balancesFound⟩ := ContractMemoryCorrespondence.shared_reference_value references initialized description'
    (index := 4) rfl rfl (by decide : ∀ slot ∈ sharedSlotTypes, slot.1 = "balances" → slot.2 = Core.WordMapping.type)
  obtain ⟨creatorValue, creatorStored⟩ := creatorFound
  let known := sharedCells ++ [creatorCell creatorLocation creatorValue]
  have fresh : FrameInitializersValid depth environment initial
      (ContractMemoryCorrespondence.requestCode contextCode) dispatcher (part 5 12 contextCode)
      (constant (Core.WordMapping.literal [])) (number 0) (CodeBuilder.boolean false) shared
      (initializedObservation accounts context.address context.completeWorld context.isStatic balances worldLocation balancesLocation) :=
    fresh_initializers_observation (ContractMemoryCorrespondence.request_related object context contextRelated) rfl rfl rfl
      (contextRelated.part (index := 5) rfl) (CodeValue.mapping [] depth environment)
      (CodeValue.number 0 depth environment) (CodeValue.boolean false depth environment) references description'
  have sharedBase := shared_initializers_valid (address := context.address) (isStatic := context.isStatic) (known := known) references initialized
    (fun _ member => List.mem_append_left _ member) description' worldReference balancesReference
  have creatorBase := creator_initialized_valid creatorRelated creatorStored
    (show creatorCell creatorLocation creatorValue ∈ known from List.mem_append_right _ (.head _))
    accounts context.address context.completeWorld context.isStatic balances worldLocation balancesLocation
  have freshBoth := FrameInitializersValid.and fresh freshExtra
  have sharedReady : FrameSharedValid depth environment initial Effects.slots shared
      (fun cell => (initializedObservation accounts context.address context.completeWorld context.isStatic balances worldLocation balancesLocation cell ∧ property cell) ∧ cell ∈ known) := by
    intro slot member name code found
    obtain ⟨cell, named, typed, related, stored, valid, included⟩ := sharedBase slot member name code found
    obtain ⟨source, sourceMember, sourceName, sourceRelated⟩ := references.find found
    have referenceEqual := (Core.evaluation_deterministic (related.evaluates initial) (sourceRelated.evaluates initial)).1
    have locationEqual := (Core.Value.cellRef.inj referenceEqual).2
    have valueEqual : cell.value = source.value := Option.some.inj
      (stored.symm.trans (by simpa only [← locationEqual] using initialized source sourceMember))
    have cellEqual : cell = source := by
      cases cell
      cases source
      simp_all [InitializedCell.reference]
    subst source
    exact ⟨cell, named, typed, related, stored, ⟨⟨valid, sharedExtra cell sourceMember⟩, included⟩⟩
  have creatorReady : FrameCreatorValid depth environment initial Effects.slots creator
      (fun cell => (initializedObservation accounts context.address context.completeWorld context.isStatic balances worldLocation balancesLocation cell ∧ property cell) ∧ cell ∈ known) := by
    intro type member
    obtain ⟨cell, named, typed, related, stored, valid, included⟩ := creatorBase type member
    have referenceEqual := (Core.evaluation_deterministic (related.evaluates initial) (creatorRelated.evaluates initial)).1
    have locationEqual := (Core.Value.cellRef.inj referenceEqual).2
    have cellEqual : cell = creatorCell creatorLocation cell.value := by
      cases cell
      simp_all [InitializedCell.reference, creatorCell]
    refine ⟨cell, named, typed, related, stored, ⟨⟨valid, ?_⟩, included⟩⟩
    rw [cellEqual]
    exact creatorExtra _ (by simpa only [← locationEqual] using stored)
  obtain ⟨extra, suffix, frameReferences, cells, referenceValues, stored, signature, observed, locations, allocated⟩ :=
    allocateFrameSlots_separates freshBoth sharedReady creatorReady (previous := []) (previousCells := []) .nil
      (by intro cell member; cases member) (by intro cell member; cases member)
      (known_initialized initialized creatorStored)
      (by simpa only [List.append_nil] using known_separate separate creatorAfter (value := creatorValue))
  simp only [List.reverse_nil, List.nil_append] at referenceValues stored observed locations allocated
  have cellLocations : CellLocations cells := locations.subset (fun _ member => List.mem_append_right _ member)
  obtain ⟨value, final, evaluated, observedResult⟩ := continued extra suffix frameReferences cells worldLocation balancesLocation
    referenceValues stored signature observed cellLocations worldReference balancesReference balancesFound
  exact ⟨value, final, allocated _ _ _ evaluated, observedResult⟩

end Solcore.Frontend.RustHull.ContractRuntimeEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractLogExecutionCorrespondence
/-! Actual public initialization supplies the immutable environment and every
mutable runtime cell before source-driven execution and receipt completion. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractLogCorrespondence
open Correspondence ScalarExecution CodeBuilder ContractRuntimeEffectsCorrespondence ContractEnvironmentCorrespondence

def contextInitialState (object : Contract.CompiledObject) (context : Contract.Context) : RuntimeLogEffectsSemantics.State :=
  ⟨⟨ContractRuntimeEffectsCorrespondence.contextInitialState object context, contextEnvironment context⟩, [], Core.Word.zero⟩

theorem objectFrame_evaluates {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code Effects.slots fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment captured : Core.Environment} {initial : Core.Store}
    {contextCode functions dispatcher creator : Code} {shared : AccountRuntime.References}
    {closure : Core.Value} (closureRelated : CapturedClosure compiled captured closure)
    (functionsRelated : CodeValue depth environment functions closure)
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    {sharedCells : List InitializedCell} (references : RuntimeReferences depth environment shared sharedCells)
    (initialized : InitializedCells sharedCells initial) (separate : CellLocations sharedCells)
    (description : sharedCells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip (ContractMemoryCorrespondence.contextSharedValues object context)).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse)
    {creatorLocation : Nat}
    (creatorRelated : CodeValue depth environment creator (.cellRef (Core.OptionalCell.cellType Creation.callbackType) creatorLocation))
    (creatorFound : ∃ value, initial.read? creatorLocation = some value)
    (creatorAfter : ∀ cell ∈ sharedCells, cell.location < creatorLocation)
    {finalSource : Semantics.State RuntimeLogEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeLogEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectFrame Effects.slots 1 [] none contextCode functions shared dispatcher creator depth)
      value final ∧ MessageRel sourceResult finalSource.external context.address
        (Core.WordMapping.insertEntries context.address context.balance context.accounts) value := by
  let accounts := StorageCorrespondence.canonical (object.initialWorld context)
  let balances := Core.WordMapping.insertEntries context.address context.balance context.accounts
  have description' : sharedCells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip
        (ContractMemoryCorrespondence.sharedValues accounts context.completeWorld balances (ambientValues context.ambient))).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse := description
  have fresh : FrameInitializersValid depth environment initial
      (ContractMemoryCorrespondence.requestCode contextCode) dispatcher (part 5 12 contextCode)
      (constant (Core.WordMapping.literal [])) (number 0) (CodeBuilder.boolean false) shared
      (ContractEnvironmentCorrespondence.initializedValue (contextEnvironment context)) :=
    ContractEnvironmentCorrespondence.fresh_initializers_observation context (ContractMemoryCorrespondence.request_related object context contextRelated)
      (contextRelated.part (index := 5) rfl) (CodeValue.mapping [] depth environment)
      (CodeValue.number 0 depth environment) (CodeValue.boolean false depth environment) references description'
  apply ContractRuntimeEffectsCorrespondence.objectFrame_initializes object context contextRelated references initialized separate
    description creatorRelated creatorFound creatorAfter (ContractEnvironmentCorrespondence.initializedValue (contextEnvironment context))
    (fun value _ => MessageRel sourceResult finalSource.external context.address balances value)
    fresh (ContractEnvironmentCorrespondence.shared_initialized_value context none description')
    (by intro value _ expected impossible; cases impossible)
  intro extra suffix frameReferences cells worldLocation balancesLocation referenceValues stored signature observations cellLocations
    worldReference balancesReference balancesFound
  have observed := fun cell member => (observations cell member).1
  obtain ⟨ready⟩ := RuntimeInitializedEffects.state_ready signature stored cellLocations
    (fun cell member => (observed cell member).1.1) rfl
  obtain ⟨logReady⟩ := RuntimeLogInitializedEffects.ready signature stored cellLocations ready
    (words := []) (cursor := Core.Word.zero)
    (fun cell member named => (observed cell member).1.2 "logs" (by decide) named)
    (fun cell member named => (observed cell member).1.2 "logSize" (by decide) named)
  have memoryLocation : logReady.layout.memory = ready.memory :=
    congrArg RuntimeEffectsCorrespondence.Layout.memory logReady.base
  have storageLocations : logReady.layout.storage = ready.locations :=
    congrArg RuntimeEffectsCorrespondence.Layout.storage logReady.base
  have boundary : logReady.layout.boundary = (initial ++ suffix).length :=
    congrArg RuntimeEffectsCorrespondence.Layout.boundary logReady.base
  let slots := cells.map InitializedCell.effectSlot
  have slotTypes : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots := by
    simpa only [RuntimeEffectsFrameCorrespondence.slotTypes, MemoryFrameCorrespondence.slotTypes,
      slots, List.map_map, Function.comp_def, InitializedCell.effectSlot] using signature
  have environmentRelated := initialized_environment cells (initialized_effects_unique signature)
    (Core.Value.unit :: bundleValues (cells.map InitializedCell.reference) :: captured)
  have runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (RuntimeEffectsFrameCorrespondence.slotTypes slots)) Core.Renaming.id
      ((cells.map InitializedCell.reference).reverse ++ Core.Value.unit :: bundleValues (cells.map InitializedCell.reference) :: captured) := by
    simpa only [slots, RuntimeEffectsFrameCorrespondence.slotTypes, MemoryFrameCorrespondence.slotTypes,
      List.map_map, Function.comp_def, InitializedCell.effectSlot] using environmentRelated
  have plainNames : cells.map InitializedCell.name = Effects.slots.map Prod.fst := by
    simpa only [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) signature
  have passive (name : String) (present : name ∈ RuntimeLogEffectsFrameCorrespondence.passiveSnapshotNames) :
      RuntimeLogEffectsFrameCorrespondence.PassiveCell logReady.layout
        slots (initial ++ suffix) name (passiveValues balances name) := by
    have inEffects : ∀ name ∈ RuntimeLogEffectsFrameCorrespondence.passiveSnapshotNames, name ∈ Effects.slots.map Prod.fst := by decide
    obtain ⟨cell, member, named⟩ := List.mem_map.mp (plainNames.symm ▸ inEffects name present)
    have same : name = "balances" := by
      simpa only [RuntimeLogEffectsFrameCorrespondence.passiveSnapshotNames, List.mem_singleton] using present
    have presentOld : name ∈ RuntimeEffectsFrameCorrespondence.passiveSnapshotNames := by
      simp [RuntimeEffectsFrameCorrespondence.passiveSnapshotNames, same]
    have valued := (observed cell member).1.2 name presentOld named
    have outside : name ∉ ["logs", "logSize", "memory", "memorySize", "world", "exit", "returnOffset", "returnSize"] := by
      have checked : ∀ name ∈ RuntimeLogEffectsFrameCorrespondence.passiveSnapshotNames,
        name ∉ ["logs", "logSize", "memory", "memorySize", "world", "exit", "returnOffset", "returnSize"] := by decide
      exact checked name present
    simpa only [slots, named, valued] using logReady.passive_cell cellLocations stored member (named ▸ outside)
  have worldSame : ready.locations.world = worldLocation := by
    obtain ⟨cell, member, same⟩ := List.mem_map.mp ready.worldMember
    have named := congrArg EffectSlot.name same
    have atLocation := congrArg EffectSlot.location same
    exact atLocation.symm.trans ((observed cell member).2.1 named)
  obtain ⟨balanceCell, balanceMember, balanceNamed⟩ := List.mem_map.mp
    (plainNames.symm ▸ (by decide : "balances" ∈ Effects.slots.map Prod.fst))
  have balanceSame := (observed balanceCell balanceMember).2.2 balanceNamed
  have balancePassive := logReady.passive_cell cellLocations stored balanceMember
    (by simp only [balanceNamed]; decide)
  obtain ⟨balanceSlot, balanceSlotMember, balanceSlotName, balanceOutside, balanceBound, balanceRead⟩ := balancePassive
  have balanceSlotSame : balanceSlot.location = balancesLocation := by
    obtain ⟨selected, selectedMember, slotEq⟩ := List.mem_map.mp balanceSlotMember
    have named : selected.name = "balances" := (congrArg EffectSlot.name slotEq).trans balanceSlotName |>.trans balanceNamed
    exact (congrArg EffectSlot.location slotEq).symm.trans ((observed selected selectedMember).2.2 named)
  have balanceOutside' : balancesLocation ∉ RuntimeLogEffectsCorrespondence.mutable logReady.layout := by
    simpa only [balanceSlotSame] using balanceOutside
  have balanceFound' : (initial ++ suffix).read? balancesLocation = some (Core.WordMapping.encode balances) := by
    exact ((StoreRetains.append initial suffix).read balancesLocation (List.getElem?_eq_some_iff.mp balancesFound).1).trans balancesFound
  have environmentInitial := initialized_related stored (fun cell member => (observations cell member).2)
  have initialRelated : StateRel (RuntimeLogEffectsCorrespondence.model logReady.layout
      (prefixRead logReady.layout.boundary (initial ++ suffix)) slots) []
      ⟨[], contextInitialState object context⟩ (initial ++ suffix) := by
    apply RuntimeLogEffectsCorrespondence.initial_state
    · simpa only [logReady.base, boundary, RuntimeEffectsCorrespondence.initialLayout] using
        RuntimeEnvironmentEffectsCorrespondence.initial_state ready.memoryRelated ready.storageRelated ready.distinct environmentInitial
    · exact logReady.logsRead
    · exact logReady.logSizeRead
  have passiveEnvironment : RuntimeLogEffectsCorrespondence.Passive logReady.layout slots := by
    apply RuntimeLogEffectsCorrespondence.Passive.of_names
      (memoryMember := by simpa only [memoryLocation] using ready.memoryMember)
      (worldMember := by simpa only [storageLocations] using ready.worldMember)
      (memorySizeMember := by simpa only [storageLocations] using ready.sizeMember)
      (exitMember := by simpa only [storageLocations] using ready.exitMember)
      (offsetMember := by simpa only [storageLocations] using ready.offsetMember)
      (sizeMember := by simpa only [storageLocations] using ready.returnSizeMember)
      (logsMember := logReady.logsMember) (logSizeMember := logReady.logSizeMember)
    intro first firstMember second secondMember same
    obtain ⟨left, leftMember, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨right, rightMember, rfl⟩ := List.mem_map.mp secondMember
    exact cellLocations left leftMember right rightMember same
  obtain ⟨value, final, completed, resultRelated⟩ := frameCall_message_evaluates
    (by simpa only [slotTypes] using accepted)
    (by simpa only [supported_actual slotTypes] using eligible) closureRelated
    ((functionsRelated.prepend extra).evaluates (initial ++ suffix))
    ((CodeValue.packet referenceValues).evaluates (initial ++ suffix))
    (by simp [slots]) runtime (initialized_effects_separate signature)
    (by simpa only [memoryLocation] using ready.memoryMember)
    (by simpa only [storageLocations] using ready.worldMember)
    (by simpa only [storageLocations] using ready.addressMember)
    (by simpa only [storageLocations] using ready.completeMember)
    (by simpa only [storageLocations] using ready.staticMember)
    (by simpa only [storageLocations] using ready.sizeMember)
    (by simpa only [storageLocations] using ready.exitMember)
    (by simpa only [storageLocations] using ready.offsetMember)
    (by simpa only [storageLocations] using ready.returnSizeMember)
    logReady.logsMember logReady.logSizeMember initialRelated passiveEnvironment evaluated context.address balances passive
    (by simpa only [storageLocations, worldSame] using worldReference.prepend extra) (balancesReference.prepend extra)
    ((contextRelated.part (index := 4) rfl).prepend extra)
    (by simpa only [notDeploying] using (contextRelated.part (index := 11) rfl).prepend extra)
    balanceFound' (by simpa only [balanceSlotSame] using balanceBound) balanceOutside'
  exact ⟨value, final, completed, resultRelated⟩

theorem objectRuntime_preserves {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code Effects.slots fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment : Core.Environment} {initial : Core.Store} {contextCode : Code}
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    {finalSource : Semantics.State RuntimeLogEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeLogEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime Effects.slots compiled [] [] none [] contextCode depth) value final ∧
      MessageRel sourceResult finalSource.external context.address
        (Core.WordMapping.insertEntries context.address context.balance context.accounts) value := by
  obtain ⟨closure, captured⟩ := compileFrame_captures accepted environment
  apply objectRuntime_evaluates_separated
    (fun value _ => MessageRel sourceResult finalSource.external context.address
      (Core.WordMapping.insertEntries context.address context.balance context.accounts) value)
    (.cons captured .nil) (ContractMemoryCorrespondence.sharedValues_related object context contextRelated)
  intro functions shared dispatcher creator extra allocated cells _ creatorLocation functionsRelated references initialized separate description _ _ creatorRelated creatorFound creatorAfter
  exact objectFrame_evaluates accepted eligible captured functionsRelated object context notDeploying
    (contextRelated.prepend extra) references initialized separate description creatorRelated creatorFound creatorAfter evaluated

def PublicMessageRel (context : Contract.Context) (result : Semantics.Result Semantics.Value)
    (state : RuntimeLogEffectsSemantics.State) (value : Core.Value) : Prop :=
  let normalized := Contract.normalizeContext context
  MessageRel result state normalized.address
    (Core.WordMapping.insertEntries normalized.address normalized.balance normalized.accounts) value

/-- Successful public compilation and an independent Hull derivation imply
execution of the actual contract expression. Every cell, reference and
separation condition comes from its allocation code. -/
theorem compileObject_preserves {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {object : Contract.CompiledObject}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel none [] = .ok object)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (context : Contract.Context) (notDeploying : context.deploying = false)
    {finalSource : Semantics.State RuntimeLogEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeLogEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates [] [] (object.instantiate context).expression value final ∧
      PublicMessageRel context sourceResult finalSource.external value := by
  have compiled : AccountRuntime.compileObject program path fuel none [] = .ok object.expression := by
    unfold Contract.compileObject at accepted
    obtain ⟨expression, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
    cases returned
    exact compiled
  obtain ⟨frame, frameCompiled, objectExpression⟩ := ContractMemoryCorrespondence.compileObject_selected selected compiled
  have normalized : (Contract.normalizeContext context).deploying = false := notDeploying
  obtain ⟨value, final, executed, related⟩ := objectRuntime_preserves (by simpa using frameCompiled) eligible object
    (Contract.normalizeContext context) normalized
    (CodeValue.bound 0 [] (bundleValues (contextValues object (Contract.normalizeContext context)))) evaluated
  refine ⟨value, final, instantiate_evaluates context (parameter := AccountRuntime.contextType) (resultType := AccountRuntime.resultType) ?_ executed, related⟩
  rw [objectExpression]
  rfl

/-- The actual receipt and every finite checkpoint chain reach the source
message at exactly the cumulative number of Core transitions required. -/
theorem compileObject_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {object : Contract.CompiledObject}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel none [] = .ok object)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (context : Contract.Context) (notDeploying : context.deploying = false)
    {finalSource : Semantics.State RuntimeLogEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeLogEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value, PublicMessageRel context sourceResult finalSource.external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨value, _, executed, related⟩ := compileObject_preserves selected accepted eligible context notDeploying evaluated
  exact ⟨value, related, Contract.evaluation_resumes_exact executed⟩

theorem prepare_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {context : Contract.Context} {prepared : Contract.Prepared}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.prepare program path context fuel = .ok prepared)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (notDeploying : context.deploying = false) :
    ∃ object, Contract.compileObject program path fuel none [] = .ok object ∧
      prepared = object.instantiate context ∧
      ∀ (sourceResult : Semantics.Result Semantics.Value) (finalSource : Semantics.State RuntimeLogEffectsSemantics.State),
        Semantics.EvalFunction (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeLogEffectsSemantics.effects
          (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object (Contract.normalizeContext context)⟩ sourceResult finalSource →
        ∃ value, PublicMessageRel context sourceResult finalSource.external value ∧
          ∃ required, ∀ initialFuel additional limit last,
            Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
            (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
            ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  unfold Contract.prepare at accepted
  obtain ⟨object, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
  cases returned
  exact ⟨object, compiled, rfl, fun _ _ evaluated =>
    compileObject_resumes_exact selected compiled eligible context notDeploying evaluated⟩

end Solcore.Frontend.RustHull.ContractLogCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractHashExecutionCorrespondence
/-! Actual public initialization supplies the immutable environment and every
mutable runtime cell before source-driven execution and receipt completion. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractHashCorrespondence
open Correspondence ScalarExecution CodeBuilder ContractRuntimeEffectsCorrespondence ContractEnvironmentCorrespondence

abbrev contextInitialState := ContractLogCorrespondence.contextInitialState

theorem objectFrame_evaluates {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code Effects.slots fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment captured : Core.Environment} {initial : Core.Store}
    {contextCode functions dispatcher creator : Code} {shared : AccountRuntime.References}
    {closure : Core.Value} (closureRelated : CapturedClosure compiled captured closure)
    (functionsRelated : CodeValue depth environment functions closure)
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    {sharedCells : List InitializedCell} (references : RuntimeReferences depth environment shared sharedCells)
    (initialized : InitializedCells sharedCells initial) (separate : CellLocations sharedCells)
    (description : sharedCells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip (ContractMemoryCorrespondence.contextSharedValues object context)).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse)
    {creatorLocation : Nat}
    (creatorRelated : CodeValue depth environment creator (.cellRef (Core.OptionalCell.cellType Creation.callbackType) creatorLocation))
    (creatorFound : ∃ value, initial.read? creatorLocation = some value)
    (creatorAfter : ∀ cell ∈ sharedCells, cell.location < creatorLocation)
    {finalSource : Semantics.State RuntimeLogEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeHashEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectFrame Effects.slots 1 [] none contextCode functions shared dispatcher creator depth)
      value final ∧ MessageRel sourceResult finalSource.external context.address
        (Core.WordMapping.insertEntries context.address context.balance context.accounts) value := by
  let accounts := StorageCorrespondence.canonical (object.initialWorld context)
  let balances := Core.WordMapping.insertEntries context.address context.balance context.accounts
  have description' : sharedCells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip
        (ContractMemoryCorrespondence.sharedValues accounts context.completeWorld balances (ambientValues context.ambient))).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse := description
  have fresh : FrameInitializersValid depth environment initial
      (ContractMemoryCorrespondence.requestCode contextCode) dispatcher (part 5 12 contextCode)
      (constant (Core.WordMapping.literal [])) (number 0) (CodeBuilder.boolean false) shared
      (ContractEnvironmentCorrespondence.initializedValue (contextEnvironment context)) :=
    ContractEnvironmentCorrespondence.fresh_initializers_observation context (ContractMemoryCorrespondence.request_related object context contextRelated)
      (contextRelated.part (index := 5) rfl) (CodeValue.mapping [] depth environment)
      (CodeValue.number 0 depth environment) (CodeValue.boolean false depth environment) references description'
  apply ContractRuntimeEffectsCorrespondence.objectFrame_initializes object context contextRelated references initialized separate
    description creatorRelated creatorFound creatorAfter (ContractEnvironmentCorrespondence.initializedValue (contextEnvironment context))
    (fun value _ => MessageRel sourceResult finalSource.external context.address balances value)
    fresh (ContractEnvironmentCorrespondence.shared_initialized_value context none description')
    (by intro value _ expected impossible; cases impossible)
  intro extra suffix frameReferences cells worldLocation balancesLocation referenceValues stored signature observations cellLocations
    worldReference balancesReference balancesFound
  have observed := fun cell member => (observations cell member).1
  obtain ⟨ready⟩ := RuntimeInitializedEffects.state_ready signature stored cellLocations
    (fun cell member => (observed cell member).1.1) rfl
  obtain ⟨logReady⟩ := RuntimeLogInitializedEffects.ready signature stored cellLocations ready
    (words := []) (cursor := Core.Word.zero)
    (fun cell member named => (observed cell member).1.2 "logs" (by decide) named)
    (fun cell member named => (observed cell member).1.2 "logSize" (by decide) named)
  have memoryLocation : logReady.layout.memory = ready.memory :=
    congrArg RuntimeEffectsCorrespondence.Layout.memory logReady.base
  have storageLocations : logReady.layout.storage = ready.locations :=
    congrArg RuntimeEffectsCorrespondence.Layout.storage logReady.base
  have boundary : logReady.layout.boundary = (initial ++ suffix).length :=
    congrArg RuntimeEffectsCorrespondence.Layout.boundary logReady.base
  let slots := cells.map InitializedCell.effectSlot
  have slotTypes : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots := by
    simpa only [RuntimeEffectsFrameCorrespondence.slotTypes, MemoryFrameCorrespondence.slotTypes,
      slots, List.map_map, Function.comp_def, InitializedCell.effectSlot] using signature
  have environmentRelated := initialized_environment cells (initialized_effects_unique signature)
    (Core.Value.unit :: bundleValues (cells.map InitializedCell.reference) :: captured)
  have runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (RuntimeEffectsFrameCorrespondence.slotTypes slots)) Core.Renaming.id
      ((cells.map InitializedCell.reference).reverse ++ Core.Value.unit :: bundleValues (cells.map InitializedCell.reference) :: captured) := by
    simpa only [slots, RuntimeEffectsFrameCorrespondence.slotTypes, MemoryFrameCorrespondence.slotTypes,
      List.map_map, Function.comp_def, InitializedCell.effectSlot] using environmentRelated
  have plainNames : cells.map InitializedCell.name = Effects.slots.map Prod.fst := by
    simpa only [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) signature
  have passive (name : String) (present : name ∈ RuntimeLogEffectsFrameCorrespondence.passiveSnapshotNames) :
      RuntimeLogEffectsFrameCorrespondence.PassiveCell logReady.layout
        slots (initial ++ suffix) name (passiveValues balances name) := by
    have inEffects : ∀ name ∈ RuntimeLogEffectsFrameCorrespondence.passiveSnapshotNames, name ∈ Effects.slots.map Prod.fst := by decide
    obtain ⟨cell, member, named⟩ := List.mem_map.mp (plainNames.symm ▸ inEffects name present)
    have same : name = "balances" := by
      simpa only [RuntimeLogEffectsFrameCorrespondence.passiveSnapshotNames, List.mem_singleton] using present
    have presentOld : name ∈ RuntimeEffectsFrameCorrespondence.passiveSnapshotNames := by
      simp [RuntimeEffectsFrameCorrespondence.passiveSnapshotNames, same]
    have valued := (observed cell member).1.2 name presentOld named
    have outside : name ∉ ["logs", "logSize", "memory", "memorySize", "world", "exit", "returnOffset", "returnSize"] := by
      have checked : ∀ name ∈ RuntimeLogEffectsFrameCorrespondence.passiveSnapshotNames,
        name ∉ ["logs", "logSize", "memory", "memorySize", "world", "exit", "returnOffset", "returnSize"] := by decide
      exact checked name present
    simpa only [slots, named, valued] using logReady.passive_cell cellLocations stored member (named ▸ outside)
  have worldSame : ready.locations.world = worldLocation := by
    obtain ⟨cell, member, same⟩ := List.mem_map.mp ready.worldMember
    have named := congrArg EffectSlot.name same
    have atLocation := congrArg EffectSlot.location same
    exact atLocation.symm.trans ((observed cell member).2.1 named)
  obtain ⟨balanceCell, balanceMember, balanceNamed⟩ := List.mem_map.mp
    (plainNames.symm ▸ (by decide : "balances" ∈ Effects.slots.map Prod.fst))
  have balanceSame := (observed balanceCell balanceMember).2.2 balanceNamed
  have balancePassive := logReady.passive_cell cellLocations stored balanceMember
    (by simp only [balanceNamed]; decide)
  obtain ⟨balanceSlot, balanceSlotMember, balanceSlotName, balanceOutside, balanceBound, balanceRead⟩ := balancePassive
  have balanceSlotSame : balanceSlot.location = balancesLocation := by
    obtain ⟨selected, selectedMember, slotEq⟩ := List.mem_map.mp balanceSlotMember
    have named : selected.name = "balances" := (congrArg EffectSlot.name slotEq).trans balanceSlotName |>.trans balanceNamed
    exact (congrArg EffectSlot.location slotEq).symm.trans ((observed selected selectedMember).2.2 named)
  have balanceOutside' : balancesLocation ∉ RuntimeLogEffectsCorrespondence.mutable logReady.layout := by
    simpa only [balanceSlotSame] using balanceOutside
  have balanceFound' : (initial ++ suffix).read? balancesLocation = some (Core.WordMapping.encode balances) := by
    exact ((StoreRetains.append initial suffix).read balancesLocation (List.getElem?_eq_some_iff.mp balancesFound).1).trans balancesFound
  have environmentInitial := initialized_related stored (fun cell member => (observations cell member).2)
  have initialRelated : StateRel (RuntimeLogEffectsCorrespondence.model logReady.layout
      (prefixRead logReady.layout.boundary (initial ++ suffix)) slots) []
      ⟨[], contextInitialState object context⟩ (initial ++ suffix) := by
    apply RuntimeLogEffectsCorrespondence.initial_state
    · simpa only [logReady.base, boundary, RuntimeEffectsCorrespondence.initialLayout] using
        RuntimeEnvironmentEffectsCorrespondence.initial_state ready.memoryRelated ready.storageRelated ready.distinct environmentInitial
    · exact logReady.logsRead
    · exact logReady.logSizeRead
  have passiveEnvironment : RuntimeLogEffectsCorrespondence.Passive logReady.layout slots := by
    apply RuntimeLogEffectsCorrespondence.Passive.of_names
      (memoryMember := by simpa only [memoryLocation] using ready.memoryMember)
      (worldMember := by simpa only [storageLocations] using ready.worldMember)
      (memorySizeMember := by simpa only [storageLocations] using ready.sizeMember)
      (exitMember := by simpa only [storageLocations] using ready.exitMember)
      (offsetMember := by simpa only [storageLocations] using ready.offsetMember)
      (sizeMember := by simpa only [storageLocations] using ready.returnSizeMember)
      (logsMember := logReady.logsMember) (logSizeMember := logReady.logSizeMember)
    intro first firstMember second secondMember same
    obtain ⟨left, leftMember, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨right, rightMember, rfl⟩ := List.mem_map.mp secondMember
    exact cellLocations left leftMember right rightMember same
  obtain ⟨value, final, completed, resultRelated⟩ := frameCall_message_evaluates
    (by simpa only [slotTypes] using accepted)
    (by simpa only [supported_actual slotTypes] using eligible) closureRelated
    ((functionsRelated.prepend extra).evaluates (initial ++ suffix))
    ((CodeValue.packet referenceValues).evaluates (initial ++ suffix))
    (by simp [slots]) runtime (initialized_effects_separate signature)
    (by simpa only [memoryLocation] using ready.memoryMember)
    (by simpa only [storageLocations] using ready.worldMember)
    (by simpa only [storageLocations] using ready.addressMember)
    (by simpa only [storageLocations] using ready.completeMember)
    (by simpa only [storageLocations] using ready.staticMember)
    (by simpa only [storageLocations] using ready.sizeMember)
    (by simpa only [storageLocations] using ready.exitMember)
    (by simpa only [storageLocations] using ready.offsetMember)
    (by simpa only [storageLocations] using ready.returnSizeMember)
    logReady.logsMember logReady.logSizeMember initialRelated passiveEnvironment evaluated context.address balances passive
    (by simpa only [storageLocations, worldSame] using worldReference.prepend extra) (balancesReference.prepend extra)
    ((contextRelated.part (index := 4) rfl).prepend extra)
    (by simpa only [notDeploying] using (contextRelated.part (index := 11) rfl).prepend extra)
    balanceFound' (by simpa only [balanceSlotSame] using balanceBound) balanceOutside'
  exact ⟨value, final, completed, resultRelated⟩

theorem objectRuntime_preserves {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code Effects.slots fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment : Core.Environment} {initial : Core.Store} {contextCode : Code}
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    {finalSource : Semantics.State RuntimeLogEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeHashEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime Effects.slots compiled [] [] none [] contextCode depth) value final ∧
      MessageRel sourceResult finalSource.external context.address
        (Core.WordMapping.insertEntries context.address context.balance context.accounts) value := by
  obtain ⟨closure, captured⟩ := compileFrame_captures accepted environment
  apply objectRuntime_evaluates_separated
    (fun value _ => MessageRel sourceResult finalSource.external context.address
      (Core.WordMapping.insertEntries context.address context.balance context.accounts) value)
    (.cons captured .nil) (ContractMemoryCorrespondence.sharedValues_related object context contextRelated)
  intro functions shared dispatcher creator extra allocated cells _ creatorLocation functionsRelated references initialized separate description _ _ creatorRelated creatorFound creatorAfter
  exact objectFrame_evaluates accepted eligible captured functionsRelated object context notDeploying
    (contextRelated.prepend extra) references initialized separate description creatorRelated creatorFound creatorAfter evaluated

abbrev PublicMessageRel := ContractLogCorrespondence.PublicMessageRel

/-- Successful public compilation and an independent Hull derivation imply
execution of the actual contract expression. Every cell, reference and
separation condition comes from its allocation code. -/
theorem compileObject_preserves {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {object : Contract.CompiledObject}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel none [] = .ok object)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (context : Contract.Context) (notDeploying : context.deploying = false)
    {finalSource : Semantics.State RuntimeLogEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeHashEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates [] [] (object.instantiate context).expression value final ∧
      PublicMessageRel context sourceResult finalSource.external value := by
  have compiled : AccountRuntime.compileObject program path fuel none [] = .ok object.expression := by
    unfold Contract.compileObject at accepted
    obtain ⟨expression, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
    cases returned
    exact compiled
  obtain ⟨frame, frameCompiled, objectExpression⟩ := ContractMemoryCorrespondence.compileObject_selected selected compiled
  have normalized : (Contract.normalizeContext context).deploying = false := notDeploying
  obtain ⟨value, final, executed, related⟩ := objectRuntime_preserves (by simpa using frameCompiled) eligible object
    (Contract.normalizeContext context) normalized
    (CodeValue.bound 0 [] (bundleValues (contextValues object (Contract.normalizeContext context)))) evaluated
  refine ⟨value, final, instantiate_evaluates context (parameter := AccountRuntime.contextType) (resultType := AccountRuntime.resultType) ?_ executed, related⟩
  rw [objectExpression]
  rfl

/-- The actual receipt and every finite checkpoint chain reach the source
message at exactly the cumulative number of Core transitions required. -/
theorem compileObject_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {object : Contract.CompiledObject}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel none [] = .ok object)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (context : Contract.Context) (notDeploying : context.deploying = false)
    {finalSource : Semantics.State RuntimeLogEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeHashEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value, PublicMessageRel context sourceResult finalSource.external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨value, _, executed, related⟩ := compileObject_preserves selected accepted eligible context notDeploying evaluated
  exact ⟨value, related, Contract.evaluation_resumes_exact executed⟩

theorem prepare_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {context : Contract.Context} {prepared : Contract.Prepared}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.prepare program path context fuel = .ok prepared)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (notDeploying : context.deploying = false) :
    ∃ object, Contract.compileObject program path fuel none [] = .ok object ∧
      prepared = object.instantiate context ∧
      ∀ (sourceResult : Semantics.Result Semantics.Value) (finalSource : Semantics.State RuntimeLogEffectsSemantics.State),
        Semantics.EvalFunction (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeHashEffectsSemantics.effects
          (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object (Contract.normalizeContext context)⟩ sourceResult finalSource →
        ∃ value, PublicMessageRel context sourceResult finalSource.external value ∧
          ∃ required, ∀ initialFuel additional limit last,
            Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
            (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
            ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  unfold Contract.prepare at accepted
  obtain ⟨object, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
  cases returned
  exact ⟨object, compiled, rfl, fun _ _ evaluated =>
    compileObject_resumes_exact selected compiled eligible context notDeploying evaluated⟩

end Solcore.Frontend.RustHull.ContractHashCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractAccountExecutionCorrespondence
/-! Actual public initialization supplies the immutable environment and every
mutable runtime cell before source-driven execution and receipt completion. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractAccountCorrespondence
open Correspondence ScalarExecution CodeBuilder ContractRuntimeEffectsCorrespondence ContractEnvironmentCorrespondence

def contextInitialState (object : Contract.CompiledObject) (context : Contract.Context) : RuntimeAccountEffectsSemantics.State :=
  ⟨ContractHashCorrespondence.contextInitialState object context,
    Core.WordMapping.insertEntries context.address context.balance context.accounts⟩

theorem objectFrame_evaluates {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code Effects.slots fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment captured : Core.Environment} {initial : Core.Store}
    {contextCode functions dispatcher creator : Code} {shared : AccountRuntime.References}
    {closure : Core.Value} (closureRelated : CapturedClosure compiled captured closure)
    (functionsRelated : CodeValue depth environment functions closure)
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    {sharedCells : List InitializedCell} (references : RuntimeReferences depth environment shared sharedCells)
    (initialized : InitializedCells sharedCells initial) (separate : CellLocations sharedCells)
    (description : sharedCells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip (ContractMemoryCorrespondence.contextSharedValues object context)).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse)
    {creatorLocation : Nat}
    (creatorRelated : CodeValue depth environment creator (.cellRef (Core.OptionalCell.cellType Creation.callbackType) creatorLocation))
    (creatorFound : ∃ value, initial.read? creatorLocation = some value)
    (creatorAfter : ∀ cell ∈ sharedCells, cell.location < creatorLocation)
    {finalSource : Semantics.State RuntimeAccountEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeAccountEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectFrame Effects.slots 1 [] none contextCode functions shared dispatcher creator depth)
      value final ∧ MessageRel sourceResult finalSource.external context.address value := by
  let accounts := StorageCorrespondence.canonical (object.initialWorld context)
  let balances := Core.WordMapping.insertEntries context.address context.balance context.accounts
  have description' : sharedCells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip
        (ContractMemoryCorrespondence.sharedValues accounts context.completeWorld balances (ambientValues context.ambient))).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse := description
  have fresh : FrameInitializersValid depth environment initial
      (ContractMemoryCorrespondence.requestCode contextCode) dispatcher (part 5 12 contextCode)
      (constant (Core.WordMapping.literal [])) (number 0) (CodeBuilder.boolean false) shared
      (ContractEnvironmentCorrespondence.initializedValue (contextEnvironment context)) :=
    ContractEnvironmentCorrespondence.fresh_initializers_observation context (ContractMemoryCorrespondence.request_related object context contextRelated)
      (contextRelated.part (index := 5) rfl) (CodeValue.mapping [] depth environment)
      (CodeValue.number 0 depth environment) (CodeValue.boolean false depth environment) references description'
  apply ContractRuntimeEffectsCorrespondence.objectFrame_initializes object context contextRelated references initialized separate
    description creatorRelated creatorFound creatorAfter (ContractEnvironmentCorrespondence.initializedValue (contextEnvironment context))
    (fun value _ => MessageRel sourceResult finalSource.external context.address value)
    fresh (ContractEnvironmentCorrespondence.shared_initialized_value context none description')
    (by intro value _ expected impossible; cases impossible)
  intro extra suffix frameReferences cells worldLocation balancesLocation referenceValues stored signature observations cellLocations
    worldReference balancesReference balancesFound
  have observed := fun cell member => (observations cell member).1
  obtain ⟨ready⟩ := RuntimeInitializedEffects.state_ready signature stored cellLocations
    (fun cell member => (observed cell member).1.1) rfl
  obtain ⟨logReady⟩ := RuntimeLogInitializedEffects.ready signature stored cellLocations ready
    (words := []) (cursor := Core.Word.zero)
    (fun cell member named => (observed cell member).1.2 "logs" (by decide) named)
    (fun cell member named => (observed cell member).1.2 "logSize" (by decide) named)
  obtain ⟨accountReady⟩ := RuntimeAccountInitializedEffects.ready signature stored cellLocations logReady
    (balances := balances) (fun cell member named => (observed cell member).1.2 "balances" (by decide) named)
  have memoryLocation : accountReady.layout.memory = ready.memory :=
    (congrArg (fun layout : RuntimeLogEffectsCorrespondence.Layout => layout.memory) accountReady.base).trans
      (congrArg RuntimeEffectsCorrespondence.Layout.memory logReady.base)
  have storageLocations : accountReady.layout.storage = ready.locations :=
    (congrArg (fun layout : RuntimeLogEffectsCorrespondence.Layout => layout.storage) accountReady.base).trans
      (congrArg RuntimeEffectsCorrespondence.Layout.storage logReady.base)
  have boundary : accountReady.layout.boundary = (initial ++ suffix).length :=
    (congrArg (fun layout : RuntimeLogEffectsCorrespondence.Layout => layout.boundary) accountReady.base).trans
      (congrArg RuntimeEffectsCorrespondence.Layout.boundary logReady.base)
  let slots := cells.map InitializedCell.effectSlot
  have slotTypes : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots := by
    simpa only [RuntimeEffectsFrameCorrespondence.slotTypes, MemoryFrameCorrespondence.slotTypes,
      slots, List.map_map, Function.comp_def, InitializedCell.effectSlot] using signature
  have environmentRelated := initialized_environment cells (initialized_effects_unique signature)
    (Core.Value.unit :: bundleValues (cells.map InitializedCell.reference) :: captured)
  have runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (RuntimeEffectsFrameCorrespondence.slotTypes slots)) Core.Renaming.id
      ((cells.map InitializedCell.reference).reverse ++ Core.Value.unit :: bundleValues (cells.map InitializedCell.reference) :: captured) := by
    simpa only [slots, RuntimeEffectsFrameCorrespondence.slotTypes, MemoryFrameCorrespondence.slotTypes,
      List.map_map, Function.comp_def, InitializedCell.effectSlot] using environmentRelated
  have worldSame : ready.locations.world = worldLocation := by
    obtain ⟨cell, member, same⟩ := List.mem_map.mp ready.worldMember
    have named := congrArg EffectSlot.name same
    have atLocation := congrArg EffectSlot.location same
    exact atLocation.symm.trans ((observed cell member).2.1 named)
  have balanceSame : accountReady.layout.balances = balancesLocation := by
    obtain ⟨cell, member, same⟩ := List.mem_map.mp accountReady.balancesMember
    have named := congrArg EffectSlot.name same
    have atLocation := congrArg EffectSlot.location same
    exact atLocation.symm.trans ((observed cell member).2.2 named)
  have environmentInitial := initialized_related stored (fun cell member => (observations cell member).2)
  have initialRelated : StateRel (RuntimeAccountEffectsCorrespondence.model accountReady.layout
      (prefixRead accountReady.layout.boundary (initial ++ suffix)) slots) []
      ⟨[], contextInitialState object context⟩ (initial ++ suffix) := by
    apply RuntimeAccountEffectsCorrespondence.initial_state
    · rw [accountReady.base]
      apply RuntimeLogEffectsCorrespondence.initial_state
      · simpa only [logReady.base, RuntimeEffectsCorrespondence.initialLayout] using
          RuntimeEnvironmentEffectsCorrespondence.initial_state ready.memoryRelated ready.storageRelated ready.distinct environmentInitial
      · exact logReady.logsRead
      · exact logReady.logSizeRead
    · exact accountReady.balancesRead
  have passiveEnvironment : RuntimeLogEffectsCorrespondence.Passive accountReady.layout.toLogLayout slots := by
    apply RuntimeLogEffectsCorrespondence.Passive.of_names
      (memoryMember := by simpa only [memoryLocation] using ready.memoryMember)
      (worldMember := by simpa only [storageLocations] using ready.worldMember)
      (memorySizeMember := by simpa only [storageLocations] using ready.sizeMember)
      (exitMember := by simpa only [storageLocations] using ready.exitMember)
      (offsetMember := by simpa only [storageLocations] using ready.offsetMember)
      (sizeMember := by simpa only [storageLocations] using ready.returnSizeMember)
      (logsMember := by simpa only [accountReady.base] using logReady.logsMember) (logSizeMember := by simpa only [accountReady.base] using logReady.logSizeMember)
    intro first firstMember second secondMember same
    obtain ⟨left, leftMember, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨right, rightMember, rfl⟩ := List.mem_map.mp secondMember
    exact cellLocations left leftMember right rightMember same
  obtain ⟨value, final, completed, resultRelated⟩ := frameCall_message_evaluates
    (by simpa only [slotTypes] using accepted)
    (by simpa only [supported_actual slotTypes] using eligible) closureRelated
    ((functionsRelated.prepend extra).evaluates (initial ++ suffix))
    ((CodeValue.packet referenceValues).evaluates (initial ++ suffix))
    (by simp [slots]) runtime (initialized_effects_separate signature)
    (by simpa only [memoryLocation] using ready.memoryMember)
    (by simpa only [storageLocations] using ready.worldMember)
    (by simpa only [storageLocations] using ready.addressMember)
    (by simpa only [storageLocations] using ready.completeMember)
    (by simpa only [storageLocations] using ready.staticMember)
    (by simpa only [storageLocations] using ready.sizeMember)
    (by simpa only [storageLocations] using ready.exitMember)
    (by simpa only [storageLocations] using ready.offsetMember)
    (by simpa only [storageLocations] using ready.returnSizeMember)
    (by simpa only [accountReady.base] using logReady.logsMember)
    (by simpa only [accountReady.base] using logReady.logSizeMember)
    accountReady.balancesMember initialRelated passiveEnvironment evaluated context.address
    (by simpa only [storageLocations, worldSame] using worldReference.prepend extra) (by simpa only [balanceSame] using balancesReference.prepend extra)
    ((contextRelated.part (index := 4) rfl).prepend extra)
    (by simpa only [notDeploying] using (contextRelated.part (index := 11) rfl).prepend extra)
  exact ⟨value, final, completed, resultRelated⟩

theorem objectRuntime_preserves {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code Effects.slots fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment : Core.Environment} {initial : Core.Store} {contextCode : Code}
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    {finalSource : Semantics.State RuntimeAccountEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeAccountEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime Effects.slots compiled [] [] none [] contextCode depth) value final ∧
      MessageRel sourceResult finalSource.external context.address value := by
  obtain ⟨closure, captured⟩ := compileFrame_captures accepted environment
  apply objectRuntime_evaluates_separated
    (fun value _ => MessageRel sourceResult finalSource.external context.address value)
    (.cons captured .nil) (ContractMemoryCorrespondence.sharedValues_related object context contextRelated)
  intro functions shared dispatcher creator extra allocated cells _ creatorLocation functionsRelated references initialized separate description _ _ creatorRelated creatorFound creatorAfter
  exact objectFrame_evaluates accepted eligible captured functionsRelated object context notDeploying
    (contextRelated.prepend extra) references initialized separate description creatorRelated creatorFound creatorAfter evaluated

def PublicMessageRel (context : Contract.Context) (result : Semantics.Result Semantics.Value)
    (state : RuntimeAccountEffectsSemantics.State) (value : Core.Value) : Prop :=
  MessageRel result state (Contract.normalizeContext context).address value

/-- Successful public compilation and an independent Hull derivation imply
execution of the actual contract expression. Every cell, reference and
separation condition comes from its allocation code. -/
theorem compileObject_preserves {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {object : Contract.CompiledObject}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel none [] = .ok object)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (context : Contract.Context) (notDeploying : context.deploying = false)
    {finalSource : Semantics.State RuntimeAccountEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeAccountEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates [] [] (object.instantiate context).expression value final ∧
      PublicMessageRel context sourceResult finalSource.external value := by
  have compiled : AccountRuntime.compileObject program path fuel none [] = .ok object.expression := by
    unfold Contract.compileObject at accepted
    obtain ⟨expression, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
    cases returned
    exact compiled
  obtain ⟨frame, frameCompiled, objectExpression⟩ := ContractMemoryCorrespondence.compileObject_selected selected compiled
  have normalized : (Contract.normalizeContext context).deploying = false := notDeploying
  obtain ⟨value, final, executed, related⟩ := objectRuntime_preserves (by simpa using frameCompiled) eligible object
    (Contract.normalizeContext context) normalized
    (CodeValue.bound 0 [] (bundleValues (contextValues object (Contract.normalizeContext context)))) evaluated
  refine ⟨value, final, instantiate_evaluates context (parameter := AccountRuntime.contextType) (resultType := AccountRuntime.resultType) ?_ executed, related⟩
  rw [objectExpression]
  rfl

/-- The actual receipt and every finite checkpoint chain reach the source
message at exactly the cumulative number of Core transitions required. -/
theorem compileObject_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {object : Contract.CompiledObject}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel none [] = .ok object)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (context : Contract.Context) (notDeploying : context.deploying = false)
    {finalSource : Semantics.State RuntimeAccountEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeAccountEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value, PublicMessageRel context sourceResult finalSource.external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨value, _, executed, related⟩ := compileObject_preserves selected accepted eligible context notDeploying evaluated
  exact ⟨value, related, Contract.evaluation_resumes_exact executed⟩

theorem prepare_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {context : Contract.Context} {prepared : Contract.Prepared}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.prepare program path context fuel = .ok prepared)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (notDeploying : context.deploying = false) :
    ∃ object, Contract.compileObject program path fuel none [] = .ok object ∧
      prepared = object.instantiate context ∧
      ∀ (sourceResult : Semantics.Result Semantics.Value) (finalSource : Semantics.State RuntimeAccountEffectsSemantics.State),
        Semantics.EvalFunction (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeAccountEffectsSemantics.effects
          (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object (Contract.normalizeContext context)⟩ sourceResult finalSource →
        ∃ value, PublicMessageRel context sourceResult finalSource.external value ∧
          ∃ required, ∀ initialFuel additional limit last,
            Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
            (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
            ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  unfold Contract.prepare at accepted
  obtain ⟨object, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
  cases returned
  exact ⟨object, compiled, rfl, fun _ _ evaluated =>
    compileObject_resumes_exact selected compiled eligible context notDeploying evaluated⟩

end Solcore.Frontend.RustHull.ContractAccountCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractCopyExecutionCorrespondence
/-! Actual public initialization supplies the immutable environment and every
mutable runtime cell before source-driven execution and receipt completion. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractCopyCorrespondence
open Correspondence ScalarExecution CodeBuilder ContractRuntimeEffectsCorrespondence ContractEnvironmentCorrespondence

abbrev contextInitialState := ContractLogCorrespondence.contextInitialState

theorem objectFrame_evaluates {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code Effects.slots fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment captured : Core.Environment} {initial : Core.Store}
    {contextCode functions dispatcher creator : Code} {shared : AccountRuntime.References}
    {closure : Core.Value} (closureRelated : CapturedClosure compiled captured closure)
    (functionsRelated : CodeValue depth environment functions closure)
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    {sharedCells : List InitializedCell} (references : RuntimeReferences depth environment shared sharedCells)
    (initialized : InitializedCells sharedCells initial) (separate : CellLocations sharedCells)
    (description : sharedCells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip (ContractMemoryCorrespondence.contextSharedValues object context)).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse)
    {creatorLocation : Nat}
    (creatorRelated : CodeValue depth environment creator (.cellRef (Core.OptionalCell.cellType Creation.callbackType) creatorLocation))
    (creatorFound : ∃ value, initial.read? creatorLocation = some value)
    (creatorAfter : ∀ cell ∈ sharedCells, cell.location < creatorLocation)
    {finalSource : Semantics.State RuntimeLogEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeCopyEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectFrame Effects.slots 1 [] none contextCode functions shared dispatcher creator depth)
      value final ∧ MessageRel sourceResult finalSource.external context.address
        (Core.WordMapping.insertEntries context.address context.balance context.accounts) value := by
  let accounts := StorageCorrespondence.canonical (object.initialWorld context)
  let balances := Core.WordMapping.insertEntries context.address context.balance context.accounts
  have description' : sharedCells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip
        (ContractMemoryCorrespondence.sharedValues accounts context.completeWorld balances (ambientValues context.ambient))).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse := description
  have fresh : FrameInitializersValid depth environment initial
      (ContractMemoryCorrespondence.requestCode contextCode) dispatcher (part 5 12 contextCode)
      (constant (Core.WordMapping.literal [])) (number 0) (CodeBuilder.boolean false) shared
      (ContractEnvironmentCorrespondence.initializedValue (contextEnvironment context)) :=
    ContractEnvironmentCorrespondence.fresh_initializers_observation context (ContractMemoryCorrespondence.request_related object context contextRelated)
      (contextRelated.part (index := 5) rfl) (CodeValue.mapping [] depth environment)
      (CodeValue.number 0 depth environment) (CodeValue.boolean false depth environment) references description'
  apply ContractRuntimeEffectsCorrespondence.objectFrame_initializes object context contextRelated references initialized separate
    description creatorRelated creatorFound creatorAfter (ContractEnvironmentCorrespondence.initializedValue (contextEnvironment context))
    (fun value _ => MessageRel sourceResult finalSource.external context.address balances value)
    fresh (ContractEnvironmentCorrespondence.shared_initialized_value context none description')
    (by intro value _ expected impossible; cases impossible)
  intro extra suffix frameReferences cells worldLocation balancesLocation referenceValues stored signature observations cellLocations
    worldReference balancesReference balancesFound
  have observed := fun cell member => (observations cell member).1
  obtain ⟨ready⟩ := RuntimeInitializedEffects.state_ready signature stored cellLocations
    (fun cell member => (observed cell member).1.1) rfl
  obtain ⟨logReady⟩ := RuntimeLogInitializedEffects.ready signature stored cellLocations ready
    (words := []) (cursor := Core.Word.zero)
    (fun cell member named => (observed cell member).1.2 "logs" (by decide) named)
    (fun cell member named => (observed cell member).1.2 "logSize" (by decide) named)
  have memoryLocation : logReady.layout.memory = ready.memory :=
    congrArg RuntimeEffectsCorrespondence.Layout.memory logReady.base
  have storageLocations : logReady.layout.storage = ready.locations :=
    congrArg RuntimeEffectsCorrespondence.Layout.storage logReady.base
  have boundary : logReady.layout.boundary = (initial ++ suffix).length :=
    congrArg RuntimeEffectsCorrespondence.Layout.boundary logReady.base
  let slots := cells.map InitializedCell.effectSlot
  have slotTypes : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots := by
    simpa only [RuntimeEffectsFrameCorrespondence.slotTypes, MemoryFrameCorrespondence.slotTypes,
      slots, List.map_map, Function.comp_def, InitializedCell.effectSlot] using signature
  have environmentRelated := initialized_environment cells (initialized_effects_unique signature)
    (Core.Value.unit :: bundleValues (cells.map InitializedCell.reference) :: captured)
  have runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (RuntimeEffectsFrameCorrespondence.slotTypes slots)) Core.Renaming.id
      ((cells.map InitializedCell.reference).reverse ++ Core.Value.unit :: bundleValues (cells.map InitializedCell.reference) :: captured) := by
    simpa only [slots, RuntimeEffectsFrameCorrespondence.slotTypes, MemoryFrameCorrespondence.slotTypes,
      List.map_map, Function.comp_def, InitializedCell.effectSlot] using environmentRelated
  have plainNames : cells.map InitializedCell.name = Effects.slots.map Prod.fst := by
    simpa only [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) signature
  have passive (name : String) (present : name ∈ RuntimeLogEffectsFrameCorrespondence.passiveSnapshotNames) :
      RuntimeLogEffectsFrameCorrespondence.PassiveCell logReady.layout
        slots (initial ++ suffix) name (passiveValues balances name) := by
    have inEffects : ∀ name ∈ RuntimeLogEffectsFrameCorrespondence.passiveSnapshotNames, name ∈ Effects.slots.map Prod.fst := by decide
    obtain ⟨cell, member, named⟩ := List.mem_map.mp (plainNames.symm ▸ inEffects name present)
    have same : name = "balances" := by
      simpa only [RuntimeLogEffectsFrameCorrespondence.passiveSnapshotNames, List.mem_singleton] using present
    have presentOld : name ∈ RuntimeEffectsFrameCorrespondence.passiveSnapshotNames := by
      simp [RuntimeEffectsFrameCorrespondence.passiveSnapshotNames, same]
    have valued := (observed cell member).1.2 name presentOld named
    have outside : name ∉ ["logs", "logSize", "memory", "memorySize", "world", "exit", "returnOffset", "returnSize"] := by
      have checked : ∀ name ∈ RuntimeLogEffectsFrameCorrespondence.passiveSnapshotNames,
        name ∉ ["logs", "logSize", "memory", "memorySize", "world", "exit", "returnOffset", "returnSize"] := by decide
      exact checked name present
    simpa only [slots, named, valued] using logReady.passive_cell cellLocations stored member (named ▸ outside)
  have worldSame : ready.locations.world = worldLocation := by
    obtain ⟨cell, member, same⟩ := List.mem_map.mp ready.worldMember
    have named := congrArg EffectSlot.name same
    have atLocation := congrArg EffectSlot.location same
    exact atLocation.symm.trans ((observed cell member).2.1 named)
  obtain ⟨balanceCell, balanceMember, balanceNamed⟩ := List.mem_map.mp
    (plainNames.symm ▸ (by decide : "balances" ∈ Effects.slots.map Prod.fst))
  have balanceSame := (observed balanceCell balanceMember).2.2 balanceNamed
  have balancePassive := logReady.passive_cell cellLocations stored balanceMember
    (by simp only [balanceNamed]; decide)
  obtain ⟨balanceSlot, balanceSlotMember, balanceSlotName, balanceOutside, balanceBound, balanceRead⟩ := balancePassive
  have balanceSlotSame : balanceSlot.location = balancesLocation := by
    obtain ⟨selected, selectedMember, slotEq⟩ := List.mem_map.mp balanceSlotMember
    have named : selected.name = "balances" := (congrArg EffectSlot.name slotEq).trans balanceSlotName |>.trans balanceNamed
    exact (congrArg EffectSlot.location slotEq).symm.trans ((observed selected selectedMember).2.2 named)
  have balanceOutside' : balancesLocation ∉ RuntimeLogEffectsCorrespondence.mutable logReady.layout := by
    simpa only [balanceSlotSame] using balanceOutside
  have balanceFound' : (initial ++ suffix).read? balancesLocation = some (Core.WordMapping.encode balances) := by
    exact ((StoreRetains.append initial suffix).read balancesLocation (List.getElem?_eq_some_iff.mp balancesFound).1).trans balancesFound
  have environmentInitial := initialized_related stored (fun cell member => (observations cell member).2)
  have initialRelated : StateRel (RuntimeLogEffectsCorrespondence.model logReady.layout
      (prefixRead logReady.layout.boundary (initial ++ suffix)) slots) []
      ⟨[], contextInitialState object context⟩ (initial ++ suffix) := by
    apply RuntimeLogEffectsCorrespondence.initial_state
    · simpa only [logReady.base, boundary, RuntimeEffectsCorrespondence.initialLayout] using
        RuntimeEnvironmentEffectsCorrespondence.initial_state ready.memoryRelated ready.storageRelated ready.distinct environmentInitial
    · exact logReady.logsRead
    · exact logReady.logSizeRead
  have passiveEnvironment : RuntimeLogEffectsCorrespondence.Passive logReady.layout slots := by
    apply RuntimeLogEffectsCorrespondence.Passive.of_names
      (memoryMember := by simpa only [memoryLocation] using ready.memoryMember)
      (worldMember := by simpa only [storageLocations] using ready.worldMember)
      (memorySizeMember := by simpa only [storageLocations] using ready.sizeMember)
      (exitMember := by simpa only [storageLocations] using ready.exitMember)
      (offsetMember := by simpa only [storageLocations] using ready.offsetMember)
      (sizeMember := by simpa only [storageLocations] using ready.returnSizeMember)
      (logsMember := logReady.logsMember) (logSizeMember := logReady.logSizeMember)
    intro first firstMember second secondMember same
    obtain ⟨left, leftMember, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨right, rightMember, rfl⟩ := List.mem_map.mp secondMember
    exact cellLocations left leftMember right rightMember same
  obtain ⟨value, final, completed, resultRelated⟩ := frameCall_message_evaluates
    (by simpa only [slotTypes] using accepted)
    (by simpa only [supported_actual slotTypes] using eligible) closureRelated
    ((functionsRelated.prepend extra).evaluates (initial ++ suffix))
    ((CodeValue.packet referenceValues).evaluates (initial ++ suffix))
    (by simp [slots]) runtime (initialized_effects_separate signature)
    (by simpa only [memoryLocation] using ready.memoryMember)
    (by simpa only [storageLocations] using ready.worldMember)
    (by simpa only [storageLocations] using ready.addressMember)
    (by simpa only [storageLocations] using ready.completeMember)
    (by simpa only [storageLocations] using ready.staticMember)
    (by simpa only [storageLocations] using ready.sizeMember)
    (by simpa only [storageLocations] using ready.exitMember)
    (by simpa only [storageLocations] using ready.offsetMember)
    (by simpa only [storageLocations] using ready.returnSizeMember)
    logReady.logsMember logReady.logSizeMember initialRelated passiveEnvironment evaluated context.address balances passive
    (by simpa only [storageLocations, worldSame] using worldReference.prepend extra) (balancesReference.prepend extra)
    ((contextRelated.part (index := 4) rfl).prepend extra)
    (by simpa only [notDeploying] using (contextRelated.part (index := 11) rfl).prepend extra)
    balanceFound' (by simpa only [balanceSlotSame] using balanceBound) balanceOutside'
  exact ⟨value, final, completed, resultRelated⟩

theorem objectRuntime_preserves {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code Effects.slots fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment : Core.Environment} {initial : Core.Store} {contextCode : Code}
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    {finalSource : Semantics.State RuntimeLogEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeCopyEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime Effects.slots compiled [] [] none [] contextCode depth) value final ∧
      MessageRel sourceResult finalSource.external context.address
        (Core.WordMapping.insertEntries context.address context.balance context.accounts) value := by
  obtain ⟨closure, captured⟩ := compileFrame_captures accepted environment
  apply objectRuntime_evaluates_separated
    (fun value _ => MessageRel sourceResult finalSource.external context.address
      (Core.WordMapping.insertEntries context.address context.balance context.accounts) value)
    (.cons captured .nil) (ContractMemoryCorrespondence.sharedValues_related object context contextRelated)
  intro functions shared dispatcher creator extra allocated cells _ creatorLocation functionsRelated references initialized separate description _ _ creatorRelated creatorFound creatorAfter
  exact objectFrame_evaluates accepted eligible captured functionsRelated object context notDeploying
    (contextRelated.prepend extra) references initialized separate description creatorRelated creatorFound creatorAfter evaluated

abbrev PublicMessageRel := ContractLogCorrespondence.PublicMessageRel

/-- Successful public compilation and an independent Hull derivation imply
execution of the actual contract expression. Every cell, reference and
separation condition comes from its allocation code. -/
theorem compileObject_preserves {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {object : Contract.CompiledObject}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel none [] = .ok object)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (context : Contract.Context) (notDeploying : context.deploying = false)
    {finalSource : Semantics.State RuntimeLogEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeCopyEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates [] [] (object.instantiate context).expression value final ∧
      PublicMessageRel context sourceResult finalSource.external value := by
  have compiled : AccountRuntime.compileObject program path fuel none [] = .ok object.expression := by
    unfold Contract.compileObject at accepted
    obtain ⟨expression, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
    cases returned
    exact compiled
  obtain ⟨frame, frameCompiled, objectExpression⟩ := ContractMemoryCorrespondence.compileObject_selected selected compiled
  have normalized : (Contract.normalizeContext context).deploying = false := notDeploying
  obtain ⟨value, final, executed, related⟩ := objectRuntime_preserves (by simpa using frameCompiled) eligible object
    (Contract.normalizeContext context) normalized
    (CodeValue.bound 0 [] (bundleValues (contextValues object (Contract.normalizeContext context)))) evaluated
  refine ⟨value, final, instantiate_evaluates context (parameter := AccountRuntime.contextType) (resultType := AccountRuntime.resultType) ?_ executed, related⟩
  rw [objectExpression]
  rfl

/-- The actual receipt and every finite checkpoint chain reach the source
message at exactly the cumulative number of Core transitions required. -/
theorem compileObject_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {object : Contract.CompiledObject}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel none [] = .ok object)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (context : Contract.Context) (notDeploying : context.deploying = false)
    {finalSource : Semantics.State RuntimeLogEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeCopyEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value, PublicMessageRel context sourceResult finalSource.external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨value, _, executed, related⟩ := compileObject_preserves selected accepted eligible context notDeploying evaluated
  exact ⟨value, related, Contract.evaluation_resumes_exact executed⟩

theorem prepare_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {context : Contract.Context} {prepared : Contract.Prepared}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.prepare program path context fuel = .ok prepared)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (notDeploying : context.deploying = false) :
    ∃ object, Contract.compileObject program path fuel none [] = .ok object ∧
      prepared = object.instantiate context ∧
      ∀ (sourceResult : Semantics.Result Semantics.Value) (finalSource : Semantics.State RuntimeLogEffectsSemantics.State),
        Semantics.EvalFunction (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeCopyEffectsSemantics.effects
          (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object (Contract.normalizeContext context)⟩ sourceResult finalSource →
        ∃ value, PublicMessageRel context sourceResult finalSource.external value ∧
          ∃ required, ∀ initialFuel additional limit last,
            Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
            (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
            ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  unfold Contract.prepare at accepted
  obtain ⟨object, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
  cases returned
  exact ⟨object, compiled, rfl, fun _ _ evaluated =>
    compileObject_resumes_exact selected compiled eligible context notDeploying evaluated⟩

end Solcore.Frontend.RustHull.ContractCopyCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractEnvironmentExecutionCorrespondence
/-! Actual public initialization supplies the immutable environment and every
mutable runtime cell before source-driven execution and receipt completion. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractEnvironmentCorrespondence
open Correspondence ScalarExecution CodeBuilder ContractRuntimeEffectsCorrespondence

def contextInitialState (object : Contract.CompiledObject) (context : Contract.Context) : RuntimeEnvironmentEffectsSemantics.State :=
  ⟨ContractRuntimeEffectsCorrespondence.contextInitialState object context, contextEnvironment context⟩

theorem objectFrame_evaluates {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code Effects.slots fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment captured : Core.Environment} {initial : Core.Store}
    {contextCode functions dispatcher creator : Code} {shared : AccountRuntime.References}
    {closure : Core.Value} (closureRelated : CapturedClosure compiled captured closure)
    (functionsRelated : CodeValue depth environment functions closure)
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    {sharedCells : List InitializedCell} (references : RuntimeReferences depth environment shared sharedCells)
    (initialized : InitializedCells sharedCells initial) (separate : CellLocations sharedCells)
    (description : sharedCells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip (ContractMemoryCorrespondence.contextSharedValues object context)).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse)
    {creatorLocation : Nat}
    (creatorRelated : CodeValue depth environment creator (.cellRef (Core.OptionalCell.cellType Creation.callbackType) creatorLocation))
    (creatorFound : ∃ value, initial.read? creatorLocation = some value)
    (creatorAfter : ∀ cell ∈ sharedCells, cell.location < creatorLocation)
    {finalSource : Semantics.State RuntimeEnvironmentEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEnvironmentEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectFrame Effects.slots 1 [] none contextCode functions shared dispatcher creator depth)
      value final ∧ MessageRel sourceResult finalSource.external.runtime context.address
        (Core.WordMapping.insertEntries context.address context.balance context.accounts) value := by
  let accounts := StorageCorrespondence.canonical (object.initialWorld context)
  let balances := Core.WordMapping.insertEntries context.address context.balance context.accounts
  have description' : sharedCells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip
        (ContractMemoryCorrespondence.sharedValues accounts context.completeWorld balances (ambientValues context.ambient))).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse := description
  have fresh : FrameInitializersValid depth environment initial
      (ContractMemoryCorrespondence.requestCode contextCode) dispatcher (part 5 12 contextCode)
      (constant (Core.WordMapping.literal [])) (number 0) (CodeBuilder.boolean false) shared
      (initializedValue (contextEnvironment context)) :=
    fresh_initializers_observation context (ContractMemoryCorrespondence.request_related object context contextRelated)
      (contextRelated.part (index := 5) rfl) (CodeValue.mapping [] depth environment)
      (CodeValue.number 0 depth environment) (CodeValue.boolean false depth environment) references description'
  apply ContractRuntimeEffectsCorrespondence.objectFrame_initializes object context contextRelated references initialized separate
    description creatorRelated creatorFound creatorAfter (initializedValue (contextEnvironment context))
    (fun value _ => MessageRel sourceResult finalSource.external.runtime context.address balances value)
    fresh (shared_initialized_value context none description')
    (by intro value _ expected impossible; cases impossible)
  intro extra suffix frameReferences cells worldLocation balancesLocation referenceValues stored signature observations cellLocations
    worldReference balancesReference balancesFound
  have observed := fun cell member => (observations cell member).1
  obtain ⟨ready⟩ := RuntimeInitializedEffects.state_ready signature stored cellLocations
    (fun cell member => (observed cell member).1.1) rfl
  let slots := cells.map InitializedCell.effectSlot
  have slotTypes : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots := by
    simpa only [RuntimeEffectsFrameCorrespondence.slotTypes, MemoryFrameCorrespondence.slotTypes,
      slots, List.map_map, Function.comp_def, InitializedCell.effectSlot] using signature
  have environmentRelated := initialized_environment cells (initialized_effects_unique signature)
    (Core.Value.unit :: bundleValues (cells.map InitializedCell.reference) :: captured)
  have runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (RuntimeEffectsFrameCorrespondence.slotTypes slots)) Core.Renaming.id
      ((cells.map InitializedCell.reference).reverse ++ Core.Value.unit :: bundleValues (cells.map InitializedCell.reference) :: captured) := by
    simpa only [slots, RuntimeEffectsFrameCorrespondence.slotTypes, MemoryFrameCorrespondence.slotTypes,
      List.map_map, Function.comp_def, InitializedCell.effectSlot] using environmentRelated
  have plainNames : cells.map InitializedCell.name = Effects.slots.map Prod.fst := by
    simpa only [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) signature
  have passive (name : String) (present : name ∈ RuntimeEffectsFrameCorrespondence.passiveSnapshotNames) :
      RuntimeEffectsFrameCorrespondence.PassiveCell
        (RuntimeEffectsCorrespondence.initialLayout ready.memoryRelated ready.storageRelated ready.distinct)
        slots (initial ++ suffix) name (passiveValues balances name) := by
    have inEffects : ∀ name ∈ RuntimeEffectsFrameCorrespondence.passiveSnapshotNames, name ∈ Effects.slots.map Prod.fst := by decide
    obtain ⟨cell, member, named⟩ := List.mem_map.mp (plainNames.symm ▸ inEffects name present)
    have valued := (observed cell member).1.2 name present named
    have outside : name ∉ ["memory", "memorySize", "world", "exit", "returnOffset", "returnSize"] := by
      have checked : ∀ name ∈ RuntimeEffectsFrameCorrespondence.passiveSnapshotNames,
        name ∉ ["memory", "memorySize", "world", "exit", "returnOffset", "returnSize"] := by decide
      exact checked name present
    simpa only [slots, named, valued] using ready.passive_cell cellLocations stored member (named ▸ outside)
  have worldSame : ready.locations.world = worldLocation := by
    obtain ⟨cell, member, same⟩ := List.mem_map.mp ready.worldMember
    have named := congrArg EffectSlot.name same
    have atLocation := congrArg EffectSlot.location same
    exact atLocation.symm.trans ((observed cell member).2.1 named)
  obtain ⟨balanceCell, balanceMember, balanceNamed⟩ := List.mem_map.mp
    (plainNames.symm ▸ (by decide : "balances" ∈ Effects.slots.map Prod.fst))
  have balanceSame := (observed balanceCell balanceMember).2.2 balanceNamed
  have balancePassive := ready.passive_cell cellLocations stored balanceMember
    (by simp only [balanceNamed]; decide)
  obtain ⟨balanceSlot, balanceSlotMember, balanceSlotName, balanceOutside, _, balanceRead⟩ := balancePassive
  have balanceSlotSame : balanceSlot.location = balancesLocation := by
    obtain ⟨selected, selectedMember, slotEq⟩ := List.mem_map.mp balanceSlotMember
    have named : selected.name = "balances" := (congrArg EffectSlot.name slotEq).trans balanceSlotName |>.trans balanceNamed
    exact (congrArg EffectSlot.location slotEq).symm.trans ((observed selected selectedMember).2.2 named)
  have balanceOutside' : balancesLocation ∉ RuntimeEffectsCorrespondence.mutable
      (RuntimeEffectsCorrespondence.initialLayout ready.memoryRelated ready.storageRelated ready.distinct) := by
    simpa only [balanceSlotSame] using balanceOutside
  have balanceFound' : (initial ++ suffix).read? balancesLocation = some (Core.WordMapping.encode balances) := by
    exact ((StoreRetains.append initial suffix).read balancesLocation (List.getElem?_eq_some_iff.mp balancesFound).1).trans balancesFound
  have environmentInitial := initialized_related stored (fun cell member => (observations cell member).2)
  have passiveEnvironment : RuntimeEnvironmentEffectsCorrespondence.Passive
      (RuntimeEffectsCorrespondence.initialLayout ready.memoryRelated ready.storageRelated ready.distinct) slots := by
    apply RuntimeEnvironmentEffectsCorrespondence.Passive.of_names
      (memoryMember := ready.memoryMember) (worldMember := ready.worldMember) (memorySizeMember := ready.sizeMember)
      (exitMember := ready.exitMember) (offsetMember := ready.offsetMember) (sizeMember := ready.returnSizeMember)
    intro first firstMember second secondMember same
    obtain ⟨left, leftMember, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨right, rightMember, rfl⟩ := List.mem_map.mp secondMember
    exact cellLocations left leftMember right rightMember same
  obtain ⟨value, final, completed, resultRelated⟩ := frameCall_message_evaluates
    (by simpa only [slotTypes] using accepted)
    (by simpa only [supported_actual slotTypes] using eligible) closureRelated
    ((functionsRelated.prepend extra).evaluates (initial ++ suffix))
    ((CodeValue.packet referenceValues).evaluates (initial ++ suffix))
    (by simp [slots]) runtime (initialized_effects_separate signature)
    ready.memoryMember ready.worldMember ready.addressMember ready.completeMember ready.staticMember
    ready.sizeMember ready.exitMember ready.offsetMember ready.returnSizeMember
    ready.memoryRelated ready.storageRelated ready.distinct environmentInitial passiveEnvironment evaluated context.address balances passive
    (by simpa only [worldSame] using worldReference.prepend extra) (balancesReference.prepend extra)
    ((contextRelated.part (index := 4) rfl).prepend extra)
    (by simpa only [notDeploying] using (contextRelated.part (index := 11) rfl).prepend extra)
    balanceFound' balanceOutside'
  exact ⟨value, final, completed, resultRelated⟩

theorem objectRuntime_preserves {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code Effects.slots fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment : Core.Environment} {initial : Core.Store} {contextCode : Code}
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    {finalSource : Semantics.State RuntimeEnvironmentEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEnvironmentEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime Effects.slots compiled [] [] none [] contextCode depth) value final ∧
      MessageRel sourceResult finalSource.external.runtime context.address
        (Core.WordMapping.insertEntries context.address context.balance context.accounts) value := by
  obtain ⟨closure, captured⟩ := compileFrame_captures accepted environment
  apply objectRuntime_evaluates_separated
    (fun value _ => MessageRel sourceResult finalSource.external.runtime context.address
      (Core.WordMapping.insertEntries context.address context.balance context.accounts) value)
    (.cons captured .nil) (ContractMemoryCorrespondence.sharedValues_related object context contextRelated)
  intro functions shared dispatcher creator extra allocated cells _ creatorLocation functionsRelated references initialized separate description _ _ creatorRelated creatorFound creatorAfter
  exact objectFrame_evaluates accepted eligible captured functionsRelated object context notDeploying
    (contextRelated.prepend extra) references initialized separate description creatorRelated creatorFound creatorAfter evaluated

def PublicMessageRel (context : Contract.Context) (result : Semantics.Result Semantics.Value)
    (state : RuntimeEffectsSemantics.State) (value : Core.Value) : Prop :=
  let normalized := Contract.normalizeContext context
  MessageRel result state normalized.address
    (Core.WordMapping.insertEntries normalized.address normalized.balance normalized.accounts) value

/-- Successful public compilation and an independent Hull derivation imply
execution of the actual contract expression. Every cell, reference and
separation condition comes from its allocation code. -/
theorem compileObject_preserves {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {object : Contract.CompiledObject}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel none [] = .ok object)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (context : Contract.Context) (notDeploying : context.deploying = false)
    {finalSource : Semantics.State RuntimeEnvironmentEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEnvironmentEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates [] [] (object.instantiate context).expression value final ∧
      PublicMessageRel context sourceResult finalSource.external.runtime value := by
  have compiled : AccountRuntime.compileObject program path fuel none [] = .ok object.expression := by
    unfold Contract.compileObject at accepted
    obtain ⟨expression, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
    cases returned
    exact compiled
  obtain ⟨frame, frameCompiled, objectExpression⟩ := ContractMemoryCorrespondence.compileObject_selected selected compiled
  have normalized : (Contract.normalizeContext context).deploying = false := notDeploying
  obtain ⟨value, final, executed, related⟩ := objectRuntime_preserves (by simpa using frameCompiled) eligible object
    (Contract.normalizeContext context) normalized
    (CodeValue.bound 0 [] (bundleValues (contextValues object (Contract.normalizeContext context)))) evaluated
  refine ⟨value, final, instantiate_evaluates context (parameter := AccountRuntime.contextType) (resultType := AccountRuntime.resultType) ?_ executed, related⟩
  rw [objectExpression]
  rfl

/-- The actual receipt and every finite checkpoint chain reach the source
message at exactly the cumulative number of Core transitions required. -/
theorem compileObject_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {object : Contract.CompiledObject}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel none [] = .ok object)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (context : Contract.Context) (notDeploying : context.deploying = false)
    {finalSource : Semantics.State RuntimeEnvironmentEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEnvironmentEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value, PublicMessageRel context sourceResult finalSource.external.runtime value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨value, _, executed, related⟩ := compileObject_preserves selected accepted eligible context notDeploying evaluated
  exact ⟨value, related, Contract.evaluation_resumes_exact executed⟩

theorem prepare_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {context : Contract.Context} {prepared : Contract.Prepared}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.prepare program path context fuel = .ok prepared)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (notDeploying : context.deploying = false) :
    ∃ object, Contract.compileObject program path fuel none [] = .ok object ∧
      prepared = object.instantiate context ∧
      ∀ (sourceResult : Semantics.Result Semantics.Value) (finalSource : Semantics.State RuntimeEnvironmentEffectsSemantics.State),
        Semantics.EvalFunction (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEnvironmentEffectsSemantics.effects
          (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object (Contract.normalizeContext context)⟩ sourceResult finalSource →
        ∃ value, PublicMessageRel context sourceResult finalSource.external.runtime value ∧
          ∃ required, ∀ initialFuel additional limit last,
            Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
            (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
            ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  unfold Contract.prepare at accepted
  obtain ⟨object, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
  cases returned
  exact ⟨object, compiled, rfl, fun _ _ evaluated =>
    compileObject_resumes_exact selected compiled eligible context notDeploying evaluated⟩

end Solcore.Frontend.RustHull.ContractEnvironmentCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractFullExecutionCorrespondence
/-! Actual public initialization supplies the immutable environment and every
mutable runtime cell before source-driven execution and receipt completion. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractFullCorrespondence
open Correspondence ScalarExecution CodeBuilder ContractRuntimeEffectsCorrespondence ContractEnvironmentCorrespondence

abbrev contextInitialState := ContractLogCorrespondence.contextInitialState

theorem objectFrame_evaluates {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code Effects.slots fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment captured : Core.Environment} {initial : Core.Store}
    {contextCode functions dispatcher creator : Code} {shared : AccountRuntime.References}
    {closure : Core.Value} (closureRelated : CapturedClosure compiled captured closure)
    (functionsRelated : CodeValue depth environment functions closure)
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    {sharedCells : List InitializedCell} (references : RuntimeReferences depth environment shared sharedCells)
    (initialized : InitializedCells sharedCells initial) (separate : CellLocations sharedCells)
    (description : sharedCells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip (ContractMemoryCorrespondence.contextSharedValues object context)).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse)
    {creatorLocation : Nat}
    (creatorRelated : CodeValue depth environment creator (.cellRef (Core.OptionalCell.cellType Creation.callbackType) creatorLocation))
    (creatorFound : ∃ value, initial.read? creatorLocation = some value)
    (creatorAfter : ∀ cell ∈ sharedCells, cell.location < creatorLocation)
    {finalSource : Semantics.State RuntimeLogEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeFullEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectFrame Effects.slots 1 [] none contextCode functions shared dispatcher creator depth)
      value final ∧ MessageRel sourceResult finalSource.external context.address
        (Core.WordMapping.insertEntries context.address context.balance context.accounts) value := by
  let accounts := StorageCorrespondence.canonical (object.initialWorld context)
  let balances := Core.WordMapping.insertEntries context.address context.balance context.accounts
  have description' : sharedCells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip
        (ContractMemoryCorrespondence.sharedValues accounts context.completeWorld balances (ambientValues context.ambient))).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse := description
  have fresh : FrameInitializersValid depth environment initial
      (ContractMemoryCorrespondence.requestCode contextCode) dispatcher (part 5 12 contextCode)
      (constant (Core.WordMapping.literal [])) (number 0) (CodeBuilder.boolean false) shared
      (ContractEnvironmentCorrespondence.initializedValue (contextEnvironment context)) :=
    ContractEnvironmentCorrespondence.fresh_initializers_observation context (ContractMemoryCorrespondence.request_related object context contextRelated)
      (contextRelated.part (index := 5) rfl) (CodeValue.mapping [] depth environment)
      (CodeValue.number 0 depth environment) (CodeValue.boolean false depth environment) references description'
  apply ContractRuntimeEffectsCorrespondence.objectFrame_initializes object context contextRelated references initialized separate
    description creatorRelated creatorFound creatorAfter (ContractEnvironmentCorrespondence.initializedValue (contextEnvironment context))
    (fun value _ => MessageRel sourceResult finalSource.external context.address balances value)
    fresh (ContractEnvironmentCorrespondence.shared_initialized_value context none description')
    (by intro value _ expected impossible; cases impossible)
  intro extra suffix frameReferences cells worldLocation balancesLocation referenceValues stored signature observations cellLocations
    worldReference balancesReference balancesFound
  have observed := fun cell member => (observations cell member).1
  obtain ⟨ready⟩ := RuntimeInitializedEffects.state_ready signature stored cellLocations
    (fun cell member => (observed cell member).1.1) rfl
  obtain ⟨logReady⟩ := RuntimeLogInitializedEffects.ready signature stored cellLocations ready
    (words := []) (cursor := Core.Word.zero)
    (fun cell member named => (observed cell member).1.2 "logs" (by decide) named)
    (fun cell member named => (observed cell member).1.2 "logSize" (by decide) named)
  have memoryLocation : logReady.layout.memory = ready.memory :=
    congrArg RuntimeEffectsCorrespondence.Layout.memory logReady.base
  have storageLocations : logReady.layout.storage = ready.locations :=
    congrArg RuntimeEffectsCorrespondence.Layout.storage logReady.base
  have boundary : logReady.layout.boundary = (initial ++ suffix).length :=
    congrArg RuntimeEffectsCorrespondence.Layout.boundary logReady.base
  let slots := cells.map InitializedCell.effectSlot
  have slotTypes : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots := by
    simpa only [RuntimeEffectsFrameCorrespondence.slotTypes, MemoryFrameCorrespondence.slotTypes,
      slots, List.map_map, Function.comp_def, InitializedCell.effectSlot] using signature
  have environmentRelated := initialized_environment cells (initialized_effects_unique signature)
    (Core.Value.unit :: bundleValues (cells.map InitializedCell.reference) :: captured)
  have runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (RuntimeEffectsFrameCorrespondence.slotTypes slots)) Core.Renaming.id
      ((cells.map InitializedCell.reference).reverse ++ Core.Value.unit :: bundleValues (cells.map InitializedCell.reference) :: captured) := by
    simpa only [slots, RuntimeEffectsFrameCorrespondence.slotTypes, MemoryFrameCorrespondence.slotTypes,
      List.map_map, Function.comp_def, InitializedCell.effectSlot] using environmentRelated
  have plainNames : cells.map InitializedCell.name = Effects.slots.map Prod.fst := by
    simpa only [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) signature
  have passive (name : String) (present : name ∈ RuntimeLogEffectsFrameCorrespondence.passiveSnapshotNames) :
      RuntimeLogEffectsFrameCorrespondence.PassiveCell logReady.layout
        slots (initial ++ suffix) name (passiveValues balances name) := by
    have inEffects : ∀ name ∈ RuntimeLogEffectsFrameCorrespondence.passiveSnapshotNames, name ∈ Effects.slots.map Prod.fst := by decide
    obtain ⟨cell, member, named⟩ := List.mem_map.mp (plainNames.symm ▸ inEffects name present)
    have same : name = "balances" := by
      simpa only [RuntimeLogEffectsFrameCorrespondence.passiveSnapshotNames, List.mem_singleton] using present
    have presentOld : name ∈ RuntimeEffectsFrameCorrespondence.passiveSnapshotNames := by
      simp [RuntimeEffectsFrameCorrespondence.passiveSnapshotNames, same]
    have valued := (observed cell member).1.2 name presentOld named
    have outside : name ∉ ["logs", "logSize", "memory", "memorySize", "world", "exit", "returnOffset", "returnSize"] := by
      have checked : ∀ name ∈ RuntimeLogEffectsFrameCorrespondence.passiveSnapshotNames,
        name ∉ ["logs", "logSize", "memory", "memorySize", "world", "exit", "returnOffset", "returnSize"] := by decide
      exact checked name present
    simpa only [slots, named, valued] using logReady.passive_cell cellLocations stored member (named ▸ outside)
  have worldSame : ready.locations.world = worldLocation := by
    obtain ⟨cell, member, same⟩ := List.mem_map.mp ready.worldMember
    have named := congrArg EffectSlot.name same
    have atLocation := congrArg EffectSlot.location same
    exact atLocation.symm.trans ((observed cell member).2.1 named)
  obtain ⟨balanceCell, balanceMember, balanceNamed⟩ := List.mem_map.mp
    (plainNames.symm ▸ (by decide : "balances" ∈ Effects.slots.map Prod.fst))
  have balanceSame := (observed balanceCell balanceMember).2.2 balanceNamed
  have balancePassive := logReady.passive_cell cellLocations stored balanceMember
    (by simp only [balanceNamed]; decide)
  obtain ⟨balanceSlot, balanceSlotMember, balanceSlotName, balanceOutside, balanceBound, balanceRead⟩ := balancePassive
  have balanceSlotSame : balanceSlot.location = balancesLocation := by
    obtain ⟨selected, selectedMember, slotEq⟩ := List.mem_map.mp balanceSlotMember
    have named : selected.name = "balances" := (congrArg EffectSlot.name slotEq).trans balanceSlotName |>.trans balanceNamed
    exact (congrArg EffectSlot.location slotEq).symm.trans ((observed selected selectedMember).2.2 named)
  have balanceOutside' : balancesLocation ∉ RuntimeLogEffectsCorrespondence.mutable logReady.layout := by
    simpa only [balanceSlotSame] using balanceOutside
  have balanceFound' : (initial ++ suffix).read? balancesLocation = some (Core.WordMapping.encode balances) := by
    exact ((StoreRetains.append initial suffix).read balancesLocation (List.getElem?_eq_some_iff.mp balancesFound).1).trans balancesFound
  have environmentInitial := initialized_related stored (fun cell member => (observations cell member).2)
  have initialRelated : StateRel (RuntimeLogEffectsCorrespondence.model logReady.layout
      (prefixRead logReady.layout.boundary (initial ++ suffix)) slots) []
      ⟨[], contextInitialState object context⟩ (initial ++ suffix) := by
    apply RuntimeLogEffectsCorrespondence.initial_state
    · simpa only [logReady.base, boundary, RuntimeEffectsCorrespondence.initialLayout] using
        RuntimeEnvironmentEffectsCorrespondence.initial_state ready.memoryRelated ready.storageRelated ready.distinct environmentInitial
    · exact logReady.logsRead
    · exact logReady.logSizeRead
  have passiveEnvironment : RuntimeLogEffectsCorrespondence.Passive logReady.layout slots := by
    apply RuntimeLogEffectsCorrespondence.Passive.of_names
      (memoryMember := by simpa only [memoryLocation] using ready.memoryMember)
      (worldMember := by simpa only [storageLocations] using ready.worldMember)
      (memorySizeMember := by simpa only [storageLocations] using ready.sizeMember)
      (exitMember := by simpa only [storageLocations] using ready.exitMember)
      (offsetMember := by simpa only [storageLocations] using ready.offsetMember)
      (sizeMember := by simpa only [storageLocations] using ready.returnSizeMember)
      (logsMember := logReady.logsMember) (logSizeMember := logReady.logSizeMember)
    intro first firstMember second secondMember same
    obtain ⟨left, leftMember, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨right, rightMember, rfl⟩ := List.mem_map.mp secondMember
    exact cellLocations left leftMember right rightMember same
  obtain ⟨value, final, completed, resultRelated⟩ := frameCall_message_evaluates
    (by simpa only [slotTypes] using accepted)
    (by simpa only [supported_actual slotTypes] using eligible) closureRelated
    ((functionsRelated.prepend extra).evaluates (initial ++ suffix))
    ((CodeValue.packet referenceValues).evaluates (initial ++ suffix))
    (by simp [slots]) runtime (initialized_effects_separate signature)
    (by simpa only [memoryLocation] using ready.memoryMember)
    (by simpa only [storageLocations] using ready.worldMember)
    (by simpa only [storageLocations] using ready.addressMember)
    (by simpa only [storageLocations] using ready.completeMember)
    (by simpa only [storageLocations] using ready.staticMember)
    (by simpa only [storageLocations] using ready.sizeMember)
    (by simpa only [storageLocations] using ready.exitMember)
    (by simpa only [storageLocations] using ready.offsetMember)
    (by simpa only [storageLocations] using ready.returnSizeMember)
    logReady.logsMember logReady.logSizeMember initialRelated passiveEnvironment evaluated context.address balances passive
    (by simpa only [storageLocations, worldSame] using worldReference.prepend extra) (balancesReference.prepend extra)
    ((contextRelated.part (index := 4) rfl).prepend extra)
    (by simpa only [notDeploying] using (contextRelated.part (index := 11) rfl).prepend extra)
    balanceFound' (by simpa only [balanceSlotSame] using balanceBound) balanceOutside'
  exact ⟨value, final, completed, resultRelated⟩

theorem objectRuntime_preserves {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code Effects.slots fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment : Core.Environment} {initial : Core.Store} {contextCode : Code}
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    {finalSource : Semantics.State RuntimeLogEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeFullEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime Effects.slots compiled [] [] none [] contextCode depth) value final ∧
      MessageRel sourceResult finalSource.external context.address
        (Core.WordMapping.insertEntries context.address context.balance context.accounts) value := by
  obtain ⟨closure, captured⟩ := compileFrame_captures accepted environment
  apply objectRuntime_evaluates_separated
    (fun value _ => MessageRel sourceResult finalSource.external context.address
      (Core.WordMapping.insertEntries context.address context.balance context.accounts) value)
    (.cons captured .nil) (ContractMemoryCorrespondence.sharedValues_related object context contextRelated)
  intro functions shared dispatcher creator extra allocated cells _ creatorLocation functionsRelated references initialized separate description _ _ creatorRelated creatorFound creatorAfter
  exact objectFrame_evaluates accepted eligible captured functionsRelated object context notDeploying
    (contextRelated.prepend extra) references initialized separate description creatorRelated creatorFound creatorAfter evaluated

abbrev PublicMessageRel := ContractLogCorrespondence.PublicMessageRel

/-- Successful public compilation and an independent Hull derivation imply
execution of the actual contract expression. Every cell, reference and
separation condition comes from its allocation code. -/
theorem compileObject_preserves {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {object : Contract.CompiledObject}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel none [] = .ok object)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (context : Contract.Context) (notDeploying : context.deploying = false)
    {finalSource : Semantics.State RuntimeLogEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeFullEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates [] [] (object.instantiate context).expression value final ∧
      PublicMessageRel context sourceResult finalSource.external value := by
  have compiled : AccountRuntime.compileObject program path fuel none [] = .ok object.expression := by
    unfold Contract.compileObject at accepted
    obtain ⟨expression, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
    cases returned
    exact compiled
  obtain ⟨frame, frameCompiled, objectExpression⟩ := ContractMemoryCorrespondence.compileObject_selected selected compiled
  have normalized : (Contract.normalizeContext context).deploying = false := notDeploying
  obtain ⟨value, final, executed, related⟩ := objectRuntime_preserves (by simpa using frameCompiled) eligible object
    (Contract.normalizeContext context) normalized
    (CodeValue.bound 0 [] (bundleValues (contextValues object (Contract.normalizeContext context)))) evaluated
  refine ⟨value, final, instantiate_evaluates context (parameter := AccountRuntime.contextType) (resultType := AccountRuntime.resultType) ?_ executed, related⟩
  rw [objectExpression]
  rfl

/-- The actual receipt and every finite checkpoint chain reach the source
message at exactly the cumulative number of Core transitions required. -/
theorem compileObject_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {object : Contract.CompiledObject}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel none [] = .ok object)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (context : Contract.Context) (notDeploying : context.deploying = false)
    {finalSource : Semantics.State RuntimeLogEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeFullEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value, PublicMessageRel context sourceResult finalSource.external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨value, _, executed, related⟩ := compileObject_preserves selected accepted eligible context notDeploying evaluated
  exact ⟨value, related, Contract.evaluation_resumes_exact executed⟩

theorem prepare_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {context : Contract.Context} {prepared : Contract.Prepared}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.prepare program path context fuel = .ok prepared)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (notDeploying : context.deploying = false) :
    ∃ object, Contract.compileObject program path fuel none [] = .ok object ∧
      prepared = object.instantiate context ∧
      ∀ (sourceResult : Semantics.Result Semantics.Value) (finalSource : Semantics.State RuntimeLogEffectsSemantics.State),
        Semantics.EvalFunction (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeFullEffectsSemantics.effects
          (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object (Contract.normalizeContext context)⟩ sourceResult finalSource →
        ∃ value, PublicMessageRel context sourceResult finalSource.external value ∧
          ∃ required, ∀ initialFuel additional limit last,
            Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
            (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
            ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  unfold Contract.prepare at accepted
  obtain ⟨object, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
  cases returned
  exact ⟨object, compiled, rfl, fun _ _ evaluated =>
    compileObject_resumes_exact selected compiled eligible context notDeploying evaluated⟩

end Solcore.Frontend.RustHull.ContractFullCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractRuntimeEffectsExecutionCorrespondence
/-! Public contract execution derives all memory and storage initialization
conditions from the actual object wrapper before applying source preservation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractRuntimeEffectsCorrespondence
open Correspondence ScalarExecution CodeBuilder

theorem objectFrame_evaluates {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code Effects.slots fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram RuntimeEffectsCorrespondence.supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment captured : Core.Environment} {initial : Core.Store}
    {contextCode functions dispatcher creator : Code} {shared : AccountRuntime.References}
    {closure : Core.Value} (closureRelated : CapturedClosure compiled captured closure)
    (functionsRelated : CodeValue depth environment functions closure)
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    {sharedCells : List InitializedCell} (references : RuntimeReferences depth environment shared sharedCells)
    (initialized : InitializedCells sharedCells initial) (separate : CellLocations sharedCells)
    (description : sharedCells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip (ContractMemoryCorrespondence.contextSharedValues object context)).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse)
    {creatorLocation : Nat}
    (creatorRelated : CodeValue depth environment creator (.cellRef (Core.OptionalCell.cellType Creation.callbackType) creatorLocation))
    (creatorFound : ∃ value, initial.read? creatorLocation = some value)
    (creatorAfter : ∀ cell ∈ sharedCells, cell.location < creatorLocation)
    {finalSource : Semantics.State RuntimeEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectFrame Effects.slots 1 [] none contextCode functions shared dispatcher creator depth)
      value final ∧ MessageRel sourceResult finalSource.external context.address
        (Core.WordMapping.insertEntries context.address context.balance context.accounts) value := by
  let accounts := StorageCorrespondence.canonical (object.initialWorld context)
  let balances := Core.WordMapping.insertEntries context.address context.balance context.accounts
  have description' : sharedCells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip
        (ContractMemoryCorrespondence.sharedValues accounts context.completeWorld balances (ambientValues context.ambient))).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse := description
  obtain ⟨worldLocation, worldReference, worldFound⟩ := ContractMemoryCorrespondence.shared_reference_value references initialized description'
    (index := 0) rfl rfl (by decide : ∀ slot ∈ sharedSlotTypes, slot.1 = "world" → slot.2 = AccountState.type)
  obtain ⟨balancesLocation, balancesReference, balancesFound⟩ := ContractMemoryCorrespondence.shared_reference_value references initialized description'
    (index := 4) rfl rfl (by decide : ∀ slot ∈ sharedSlotTypes, slot.1 = "balances" → slot.2 = Core.WordMapping.type)
  obtain ⟨creatorValue, creatorStored⟩ := creatorFound
  let known := sharedCells ++ [creatorCell creatorLocation creatorValue]
  have fresh : FrameInitializersValid depth environment initial
      (ContractMemoryCorrespondence.requestCode contextCode) dispatcher (part 5 12 contextCode)
      (constant (Core.WordMapping.literal [])) (number 0) (CodeBuilder.boolean false) shared
      (initializedObservation accounts context.address context.completeWorld context.isStatic balances worldLocation balancesLocation) :=
    fresh_initializers_observation (ContractMemoryCorrespondence.request_related object context contextRelated) rfl rfl rfl
      (contextRelated.part (index := 5) rfl) (CodeValue.mapping [] depth environment)
      (CodeValue.number 0 depth environment) (CodeValue.boolean false depth environment) references description'
  have sharedReady := shared_initializers_valid (address := context.address) (isStatic := context.isStatic) (known := known) references initialized
    (fun _ member => List.mem_append_left _ member) description' worldReference balancesReference
  have creatorReady := creator_initialized_valid creatorRelated creatorStored
    (show creatorCell creatorLocation creatorValue ∈ known from List.mem_append_right _ (.head _))
    accounts context.address context.completeWorld context.isStatic balances worldLocation balancesLocation
  obtain ⟨extra, suffix, frameReferences, cells, referenceValues, stored, signature, observed, locations, continued⟩ :=
    allocateFrameSlots_separates fresh sharedReady creatorReady (previous := []) (previousCells := []) .nil
      (by intro cell member; cases member) (by intro cell member; cases member)
      (known_initialized initialized creatorStored)
      (by simpa only [List.append_nil] using known_separate separate creatorAfter (value := creatorValue))
  simp only [List.reverse_nil, List.nil_append] at referenceValues stored observed locations continued
  have cellLocations : CellLocations cells := locations.subset (fun _ member => List.mem_append_right _ member)
  obtain ⟨ready⟩ := RuntimeInitializedEffects.state_ready signature stored cellLocations
    (fun cell member => (observed cell member).1.1) rfl
  let slots := cells.map InitializedCell.effectSlot
  have slotTypes : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots := by
    simpa only [RuntimeEffectsFrameCorrespondence.slotTypes, MemoryFrameCorrespondence.slotTypes,
      slots, List.map_map, Function.comp_def, InitializedCell.effectSlot] using signature
  have environmentRelated := initialized_environment cells (initialized_effects_unique signature)
    (Core.Value.unit :: bundleValues (cells.map InitializedCell.reference) :: captured)
  have runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (RuntimeEffectsFrameCorrespondence.slotTypes slots)) Core.Renaming.id
      ((cells.map InitializedCell.reference).reverse ++ Core.Value.unit :: bundleValues (cells.map InitializedCell.reference) :: captured) := by
    simpa only [slots, RuntimeEffectsFrameCorrespondence.slotTypes, MemoryFrameCorrespondence.slotTypes,
      List.map_map, Function.comp_def, InitializedCell.effectSlot] using environmentRelated
  have plainNames : cells.map InitializedCell.name = Effects.slots.map Prod.fst := by
    simpa only [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) signature
  have passive (name : String) (present : name ∈ RuntimeEffectsFrameCorrespondence.passiveSnapshotNames) :
      RuntimeEffectsFrameCorrespondence.PassiveCell
        (RuntimeEffectsCorrespondence.initialLayout ready.memoryRelated ready.storageRelated ready.distinct)
        slots (initial ++ suffix) name (passiveValues balances name) := by
    have inEffects : ∀ name ∈ RuntimeEffectsFrameCorrespondence.passiveSnapshotNames, name ∈ Effects.slots.map Prod.fst := by decide
    obtain ⟨cell, member, named⟩ := List.mem_map.mp (plainNames.symm ▸ inEffects name present)
    have valued := (observed cell member).1.2 name present named
    have outside : name ∉ ["memory", "memorySize", "world", "exit", "returnOffset", "returnSize"] := by
      have checked : ∀ name ∈ RuntimeEffectsFrameCorrespondence.passiveSnapshotNames,
        name ∉ ["memory", "memorySize", "world", "exit", "returnOffset", "returnSize"] := by decide
      exact checked name present
    simpa only [slots, named, valued] using ready.passive_cell cellLocations stored member (named ▸ outside)
  have worldSame : ready.locations.world = worldLocation := by
    obtain ⟨cell, member, same⟩ := List.mem_map.mp ready.worldMember
    have named := congrArg EffectSlot.name same
    have atLocation := congrArg EffectSlot.location same
    exact atLocation.symm.trans ((observed cell member).2.1 named)
  obtain ⟨balanceCell, balanceMember, balanceNamed⟩ := List.mem_map.mp
    (plainNames.symm ▸ (by decide : "balances" ∈ Effects.slots.map Prod.fst))
  have balanceSame := (observed balanceCell balanceMember).2.2 balanceNamed
  have balancePassive := ready.passive_cell cellLocations stored balanceMember
    (by simp only [balanceNamed]; decide)
  obtain ⟨balanceSlot, balanceSlotMember, balanceSlotName, balanceOutside, _, balanceRead⟩ := balancePassive
  have balanceSlotSame : balanceSlot.location = balancesLocation := by
    obtain ⟨selected, selectedMember, slotEq⟩ := List.mem_map.mp balanceSlotMember
    have named : selected.name = "balances" := (congrArg EffectSlot.name slotEq).trans balanceSlotName |>.trans balanceNamed
    exact (congrArg EffectSlot.location slotEq).symm.trans ((observed selected selectedMember).2.2 named)
  have balanceOutside' : balancesLocation ∉ RuntimeEffectsCorrespondence.mutable
      (RuntimeEffectsCorrespondence.initialLayout ready.memoryRelated ready.storageRelated ready.distinct) := by
    simpa only [balanceSlotSame] using balanceOutside
  have balanceFound' : (initial ++ suffix).read? balancesLocation = some (Core.WordMapping.encode balances) := by
    exact ((StoreRetains.append initial suffix).read balancesLocation (List.getElem?_eq_some_iff.mp balancesFound).1).trans balancesFound
  obtain ⟨value, final, completed, resultRelated⟩ := frameCall_message_evaluates
    (by simpa only [slotTypes] using accepted) eligible closureRelated
    ((functionsRelated.prepend extra).evaluates (initial ++ suffix))
    ((CodeValue.packet referenceValues).evaluates (initial ++ suffix))
    (by simp [slots]) runtime (initialized_effects_separate signature)
    ready.memoryMember ready.worldMember ready.addressMember ready.completeMember ready.staticMember
    ready.sizeMember ready.exitMember ready.offsetMember ready.returnSizeMember
    ready.memoryRelated ready.storageRelated ready.distinct evaluated context.address balances passive
    (by simpa only [worldSame] using worldReference.prepend extra) (balancesReference.prepend extra)
    ((contextRelated.part (index := 4) rfl).prepend extra)
    (by simpa only [notDeploying] using (contextRelated.part (index := 11) rfl).prepend extra)
    balanceFound' balanceOutside'
  exact ⟨value, final, continued _ _ _ completed, resultRelated⟩

theorem objectRuntime_preserves {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code Effects.slots fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram RuntimeEffectsCorrespondence.supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment : Core.Environment} {initial : Core.Store} {contextCode : Code}
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    {finalSource : Semantics.State RuntimeEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime Effects.slots compiled [] [] none [] contextCode depth) value final ∧
      MessageRel sourceResult finalSource.external context.address
        (Core.WordMapping.insertEntries context.address context.balance context.accounts) value := by
  obtain ⟨closure, captured⟩ := compileFrame_captures accepted environment
  apply objectRuntime_evaluates_separated
    (fun value _ => MessageRel sourceResult finalSource.external context.address
      (Core.WordMapping.insertEntries context.address context.balance context.accounts) value)
    (.cons captured .nil) (ContractMemoryCorrespondence.sharedValues_related object context contextRelated)
  intro functions shared dispatcher creator extra allocated cells _ creatorLocation functionsRelated references initialized separate description _ _ creatorRelated creatorFound creatorAfter
  exact objectFrame_evaluates accepted eligible captured functionsRelated object context notDeploying
    (contextRelated.prepend extra) references initialized separate description creatorRelated creatorFound creatorAfter evaluated

def PublicMessageRel (context : Contract.Context) (result : Semantics.Result Semantics.Value)
    (state : RuntimeEffectsSemantics.State) (value : Core.Value) : Prop :=
  let normalized := Contract.normalizeContext context
  MessageRel result state normalized.address
    (Core.WordMapping.insertEntries normalized.address normalized.balance normalized.accounts) value

/-- Successful public compilation and an independent Hull derivation imply
execution of the actual contract expression. Every cell, reference and
separation condition comes from its allocation code. -/
theorem compileObject_preserves {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {object : Contract.CompiledObject}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel none [] = .ok object)
    (eligible : DerivationCorrespondence.ExecutableProgram RuntimeEffectsCorrespondence.supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (context : Contract.Context) (notDeploying : context.deploying = false)
    {finalSource : Semantics.State RuntimeEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates [] [] (object.instantiate context).expression value final ∧
      PublicMessageRel context sourceResult finalSource.external value := by
  have compiled : AccountRuntime.compileObject program path fuel none [] = .ok object.expression := by
    unfold Contract.compileObject at accepted
    obtain ⟨expression, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
    cases returned
    exact compiled
  obtain ⟨frame, frameCompiled, objectExpression⟩ := ContractMemoryCorrespondence.compileObject_selected selected compiled
  have normalized : (Contract.normalizeContext context).deploying = false := notDeploying
  obtain ⟨value, final, executed, related⟩ := objectRuntime_preserves (by simpa using frameCompiled) eligible object
    (Contract.normalizeContext context) normalized
    (CodeValue.bound 0 [] (bundleValues (contextValues object (Contract.normalizeContext context)))) evaluated
  refine ⟨value, final, instantiate_evaluates context (parameter := AccountRuntime.contextType) (resultType := AccountRuntime.resultType) ?_ executed, related⟩
  rw [objectExpression]
  rfl

/-- The actual receipt and every finite checkpoint chain reach the source
message at exactly the cumulative number of Core transitions required. -/
theorem compileObject_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {object : Contract.CompiledObject}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel none [] = .ok object)
    (eligible : DerivationCorrespondence.ExecutableProgram RuntimeEffectsCorrespondence.supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (context : Contract.Context) (notDeploying : context.deploying = false)
    {finalSource : Semantics.State RuntimeEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value, PublicMessageRel context sourceResult finalSource.external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨value, _, executed, related⟩ := compileObject_preserves selected accepted eligible context notDeploying evaluated
  exact ⟨value, related, Contract.evaluation_resumes_exact executed⟩

theorem prepare_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {context : Contract.Context} {prepared : Contract.Prepared}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.prepare program path context fuel = .ok prepared)
    (eligible : DerivationCorrespondence.ExecutableProgram RuntimeEffectsCorrespondence.supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (notDeploying : context.deploying = false) :
    ∃ object, Contract.compileObject program path fuel none [] = .ok object ∧
      prepared = object.instantiate context ∧
      ∀ (sourceResult : Semantics.Result Semantics.Value) (finalSource : Semantics.State RuntimeEffectsSemantics.State),
        Semantics.EvalFunction (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEffectsSemantics.effects
          (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState object (Contract.normalizeContext context)⟩ sourceResult finalSource →
        ∃ value, PublicMessageRel context sourceResult finalSource.external value ∧
          ∃ required, ∀ initialFuel additional limit last,
            Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
            (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
            ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  unfold Contract.prepare at accepted
  obtain ⟨object, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
  cases returned
  exact ⟨object, compiled, rfl, fun _ _ evaluated =>
    compileObject_resumes_exact selected compiled eligible context notDeploying evaluated⟩

end Solcore.Frontend.RustHull.ContractRuntimeEffectsCorrespondence
end
