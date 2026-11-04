import Solcore.Frontend.RustHull.Semantics.Frames
import Solcore.Frontend.RustHull.ContractCodeTheorems
import Solcore.Frontend.RustHull.Internal.CallStates
import Solcore.Frontend.RustHull.Internal.RuntimeObjects
import Solcore.Frontend.RustHull.Internal.CallTransport
import Solcore.Frontend.RustHull.AccountRuntime
import Solcore.Frontend.RustHull.Internal.AccountLayers
import Solcore.Frontend.RustHull.Internal.AccountCalls
import Solcore.Frontend.RustHull.Internal.LinkedWorld

/-!
# Child frames

Fresh child frames: allocation, shared resources, invocation and completion.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.ChildFrameInitializationFacts
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ChildFrameInitializedResources
/-! Actual child cells provide the complete state relation for the compiled
frame. All locations and their separation come from allocation evidence. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildFrameCorrespondence
open Core Correspondence ScalarExecution

structure Ready (cells : List InitializedCell) (store : Store)
    (state : RuntimeReturnDataEffectsSemantics.State) (bytes : List UInt8) where
  layout : RuntimeReturnDataEffectsCorrespondence.Layout
  boundary : layout.boundary = store.length
  members : ∀ slot ∈ RuntimeCallInitializedEffects.baseSlots layout,
    slot ∈ cells.map InitializedCell.effectSlot
  codes : ∀ imageCells, layout.codeCells = some imageCells →
    ⟨"code", WordMapping.type, imageCells.code⟩ ∈ cells.map InitializedCell.effectSlot ∧
    ⟨"codeKnown", .bool, imageCells.known⟩ ∈ cells.map InitializedCell.effectSlot
  mode : layout.codeCells.isSome = true
  related : StateRel (RuntimeReturnDataEffectsCorrespondence.model layout (prefixRead layout.boundary store)
    (cells.map InitializedCell.effectSlot) (some bytes)) [] ⟨[], state⟩ store
  passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout (cells.map InitializedCell.effectSlot)

theorem initialized_ready {cells : List InitializedCell} {store : Store}
    (parent : RuntimeCallEffectsSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8)
    {accounts : StorageCorrespondence.Accounts}
    (world : accounts.map Prod.fst = shared.world)
    (signature : cells.map (fun cell => (cell.name, cell.type)) = RuntimeExtendedInitializedEffects.slots true)
    (stored : InitializedCells cells store) (separate : CellLocations cells)
    (observed : ∀ cell ∈ cells, Observed accounts (Initial parent request shared bytes) bytes cell) :
    Nonempty (Ready cells store (Initial parent request shared bytes) bytes) := by
  obtain ⟨runtime, logs, accountsReady⟩ := RuntimeExtendedInitializedEffects.ready signature stored separate
    (fun cell member => (observed cell member).runtime) world
    (fun cell member => (observed cell member).logs)
    (fun cell member => (observed cell member).logSize)
    (fun cell member => (observed cell member).balances)
  obtain ⟨accountsReady⟩ := accountsReady
  have environment := ContractEnvironmentCorrespondence.initialized_related stored
    (fun cell member => (observed cell member).environment)
  obtain ⟨ready⟩ := RuntimeReturnDataInitializedEffects.ready signature stored separate accountsReady
    (image := some bytes) (data := []) (size := Word.zero)
    (fun cell member => (observed cell member).data)
    (by
      intro cell member named typed
      apply (observed cell member).environment
      simp only [named, typed, EnvironmentBuiltinCorrespondence.observation, Initial, ChildFrameSemantics.initial])
    (fun _ cell member => (observed cell member).code)
    (fun _ cell member => (observed cell member).known)
  have memoryLocation : ready.layout.memory = runtime.memory := by
    change ready.layout.toAccountLayout.memory = runtime.memory
    rw [ready.base]
    exact (congrArg (fun layout : RuntimeLogEffectsCorrespondence.Layout => layout.memory) accountsReady.base).trans
      (congrArg RuntimeEffectsCorrespondence.Layout.memory logs.base)
  have storageLocations : ready.layout.storage = runtime.locations := by
    change ready.layout.toAccountLayout.storage = runtime.locations
    rw [ready.base]
    exact (congrArg (fun layout : RuntimeLogEffectsCorrespondence.Layout => layout.storage) accountsReady.base).trans
      (congrArg RuntimeEffectsCorrespondence.Layout.storage logs.base)
  have boundary : ready.layout.boundary = store.length := by
    change ready.layout.toAccountLayout.boundary = store.length
    rw [ready.base]
    exact (congrArg (fun layout : RuntimeLogEffectsCorrespondence.Layout => layout.boundary) accountsReady.base).trans
      (congrArg RuntimeEffectsCorrespondence.Layout.boundary logs.base)
  have related : StateRel (RuntimeReturnDataEffectsCorrespondence.model ready.layout
      (prefixRead ready.layout.boundary store) (cells.map InitializedCell.effectSlot) (some bytes)) []
      ⟨[], Initial parent request shared bytes⟩ store := by
    apply RuntimeReturnDataEffectsCorrespondence.initial_state
    · rw [ready.base]
      apply RuntimeAccountEffectsCorrespondence.initial_state
      · rw [accountsReady.base]
        apply RuntimeLogEffectsCorrespondence.initial_state
        · simpa only [logs.base, RuntimeEffectsCorrespondence.initialLayout] using
            RuntimeEnvironmentEffectsCorrespondence.initial_state runtime.memoryRelated runtime.storageRelated runtime.distinct environment
        · exact logs.logsRead
        · exact logs.logSizeRead
      · exact accountsReady.balancesRead
    · exact ready.readData
    · exact ready.readSize
    · exact ready.readCode
  refine ⟨ready.layout, boundary, RuntimeCallInitializedEffects.base_members ready,
    ready.codeMembers, ready.mode, related, ?_⟩
  apply RuntimeLogEffectsCorrespondence.Passive.of_names
    (memoryMember := by simpa only [memoryLocation] using runtime.memoryMember)
    (worldMember := by simpa only [storageLocations] using runtime.worldMember)
    (memorySizeMember := by simpa only [storageLocations] using runtime.sizeMember)
    (exitMember := by simpa only [storageLocations] using runtime.exitMember)
    (offsetMember := by simpa only [storageLocations] using runtime.offsetMember)
    (sizeMember := by simpa only [storageLocations] using runtime.returnSizeMember)
    (logsMember := by simpa only [ready.base, accountsReady.base] using logs.logsMember)
    (logSizeMember := by simpa only [ready.base, accountsReady.base] using logs.logSizeMember)
  intro first firstMember second secondMember same
  obtain ⟨left, leftMember, rfl⟩ := List.mem_map.mp firstMember
  obtain ⟨right, rightMember, rfl⟩ := List.mem_map.mp secondMember
  exact separate left leftMember right rightMember same

end Solcore.Frontend.RustHull.ChildFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ChildFrameAllocationCorrespondence
/-! The actual child allocator combines existing shared cells with fresh local
cells. The continuation receives the derived frame layout and state relation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildFrameCorrespondence
open Core Correspondence ScalarExecution CodeBuilder

theorem allocateFrame_initializes {depth : Nat} {environment : Environment} {initial : Store}
    {frame dispatcher creator gas code size known : Code} {shared : AccountRuntime.References}
    (parent : RuntimeCallEffectsSemantics.State) (request : AccountCallSemantics.Request)
    (sharedState : AccountCallSemantics.Shared) (bytes : List UInt8)
    {accounts : StorageCorrespondence.Accounts} (world : accounts.map Prod.fst = sharedState.world)
    {sharedCells : List InitializedCell}
    (references : RuntimeReferences depth environment shared sharedCells)
    (signature : sharedCells.map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse)
    (initialized : InitializedCells sharedCells initial) (separate : CellLocations sharedCells)
    (observed : ∀ cell ∈ sharedCells, Observed accounts (Initial parent request sharedState bytes) bytes cell)
    {creatorLocation : Nat} {creatorValue : Value}
    (creatorRelated : CodeValue depth environment creator
      (.cellRef (OptionalCell.cellType Creation.callbackType) creatorLocation))
    (creatorFound : initial.read? creatorLocation = some creatorValue)
    (creatorSeparate : ∀ cell ∈ sharedCells, cell.location ≠ creatorLocation)
    (frameRelated : CodeValue depth environment frame (CallTransportCorrespondence.requestValue request))
    (gasRelated : CodeValue depth environment gas (optionalWordValue (some request.gas)))
    (codeRelated : CodeValue depth environment code (WordMapping.encode (Memory.packBytes bytes)))
    (sizeRelated : CodeValue depth environment size (.word (Word.ofNatModulo bytes.length)))
    (knownRelated : CodeValue depth environment known (.bool true))
    (continuation : List Code → Code) (observes : Value → Store → Prop)
    (continued : ∀ extra suffix cells values,
      CodeValues (depth + extra.length) (extra ++ environment) values (cells.map InitializedCell.reference) →
      InitializedCells cells (initial ++ suffix) →
      cells.map (fun cell => (cell.name, cell.type)) = RuntimeExtendedInitializedEffects.slots true →
      CellLocations (sharedCells ++ [ContractRuntimeEffectsCorrespondence.creatorCell creatorLocation creatorValue] ++ cells) →
      (∀ cell ∈ cells, cell.location < initial.length → cell ∈ sharedCells ∨ cell.name = "createHandler") →
      (∀ cell ∈ cells, cell.name ∈ sharedSlotTypes.map Prod.fst → cell ∈ sharedCells) →
      Ready cells (initial ++ suffix) (Initial parent request sharedState bytes) bytes →
      ∃ value final, Core.Evaluates (extra ++ environment) (initial ++ suffix)
        (continuation values (depth + extra.length)) value final ∧ observes value final) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.allocateFrame (RuntimeExtendedInitializedEffects.slots true) shared
        frame dispatcher creator gas code size known continuation depth) value final ∧ observes value final := by
  let knownCells := sharedCells ++ [ContractRuntimeEffectsCorrespondence.creatorCell creatorLocation creatorValue]
  have names : shared.map Prod.fst = (sharedSlotTypes.map Prod.fst).reverse := by
    rw [references.names]
    have same := congrArg (List.map Prod.fst) signature
    simpa only [List.map_map, Function.comp_def, List.map_reverse] using same
  have fresh := fresh_observed (store := initial) (dispatcher := dispatcher)
    parent request sharedState bytes accounts names frameRelated gasRelated codeRelated sizeRelated knownRelated
  let property := fun cell => Observed accounts (Initial parent request sharedState bytes) bytes cell ∧
    (cell.location < initial.length → cell ∈ sharedCells ∨ cell.name = "createHandler") ∧
    (cell.name ∈ sharedSlotTypes.map Prod.fst → cell ∈ sharedCells)
  have freshOrigin : FrameInitializersValid depth environment initial frame dispatcher gas code size known shared
      (fun cell => (cell.location < initial.length → cell ∈ sharedCells ∨ cell.name = "createHandler") ∧
        (cell.name ∈ sharedSlotTypes.map Prod.fst → cell ∈ sharedCells)) := by
    apply frameInitializers_valid frameRelated rfl gasRelated codeRelated sizeRelated knownRelated
    intro name type location value absent bound _
    exact ⟨fun before => False.elim (Nat.not_lt_of_ge bound before),
      fun member => False.elim (absent_shared_name names absent member)⟩
  have sharedReady : FrameSharedValid depth environment initial (RuntimeExtendedInitializedEffects.slots true) shared
      (fun cell => property cell ∧ cell ∈ knownCells) := by
    apply references.sharedValid initialized
    · intro slot member cell cellMember named
      apply sharedSlotTypes_compatible (sharedSlot := (cell.name, cell.type)) member _ named
      have present := List.mem_map_of_mem (f := fun cell : InitializedCell => (cell.name, cell.type)) cellMember
      rw [signature] at present
      exact List.mem_reverse.mp present
    · intro cell member
      exact ⟨⟨observed cell member, (fun _ => Or.inl member), fun _ => member⟩, List.mem_append_left _ member⟩
  have creatorReady : FrameCreatorValid depth environment initial (RuntimeExtendedInitializedEffects.slots true) creator
      (fun cell => property cell ∧ cell ∈ knownCells) := by
    intro type member
    have types : ∀ slot ∈ RuntimeExtendedInitializedEffects.slots true,
        slot.1 = "createHandler" → slot.2 = OptionalCell.cellType Creation.callbackType := by decide
    cases types ("createHandler", type) member rfl
    exact ⟨ContractRuntimeEffectsCorrespondence.creatorCell creatorLocation creatorValue,
      rfl, rfl, creatorRelated, creatorFound,
      ⟨creator_observed accounts _ bytes creatorLocation creatorValue, (fun _ => Or.inr rfl),
        by intro impossible; simp [ContractRuntimeEffectsCorrespondence.creatorCell, sharedSlotTypes, Ambient.slots] at impossible⟩,
      List.mem_append_right _ (.head _)⟩
  have knownStored : InitializedCells knownCells initial := by
    intro cell member
    rcases List.mem_append.mp member with member | member
    · exact initialized cell member
    · have same : cell = ContractRuntimeEffectsCorrespondence.creatorCell creatorLocation creatorValue := by simpa using member
      subst cell
      exact creatorFound
  have knownSeparate : CellLocations knownCells := by
    intro left leftMember right rightMember same
    rcases List.mem_append.mp leftMember with leftMember | leftMember
    · rcases List.mem_append.mp rightMember with rightMember | rightMember
      · exact separate left leftMember right rightMember same
      · have equal : right = ContractRuntimeEffectsCorrespondence.creatorCell creatorLocation creatorValue := by simpa using rightMember
        subst right
        exact False.elim (creatorSeparate left leftMember same)
    · have equal : left = ContractRuntimeEffectsCorrespondence.creatorCell creatorLocation creatorValue := by simpa using leftMember
      subst left
      rcases List.mem_append.mp rightMember with rightMember | rightMember
      · exact False.elim (creatorSeparate right rightMember same.symm)
      · have equal : right = ContractRuntimeEffectsCorrespondence.creatorCell creatorLocation creatorValue := by simpa using rightMember
        subst right
        rfl
  obtain ⟨extra, suffix, values, cells, related, stored, signature', valid, locations, evaluates⟩ :=
    allocateFrameSlots_separates (ContractRuntimeEffectsCorrespondence.FrameInitializersValid.and fresh freshOrigin) sharedReady creatorReady (previous := []) (previousCells := [])
      .nil (by intro cell member; cases member) (by intro cell member; cases member) knownStored
      (by simpa only [List.append_nil] using knownSeparate)
  simp only [List.reverse_nil, List.nil_append, List.append_nil] at related stored valid locations
  obtain ⟨ready⟩ := initialized_ready parent request sharedState bytes world signature' stored
    (locations.subset (fun _ member => List.mem_append_right _ member)) (fun cell member => (valid cell member).1)
  obtain ⟨value, final, evaluated, result⟩ := continued extra suffix cells values related stored signature' locations (fun cell member => (valid cell member).2.1) (fun cell member => (valid cell member).2.2) ready
  exact ⟨value, final, evaluates continuation value final evaluated, result⟩

end Solcore.Frontend.RustHull.ChildFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ChildFrameSharedResources
/-! A child reuses the parent's shared references after earlier effects have
updated their values. Refreshing the proof inventory changes no reference or
location and reads the values from the current store. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildFrameCorrespondence
open Core Correspondence ScalarExecution

def refreshCell (store : Store) (cell : InitializedCell) : InitializedCell :=
  {cell with value := (store.read? cell.location).getD .unit}

def refresh (store : Store) (cells : List InitializedCell) : List InitializedCell :=
  cells.map (refreshCell store)

theorem refresh_signature (store : Store) (cells : List InitializedCell) :
    (refresh store cells).map (fun cell => (cell.name, cell.type)) =
      cells.map (fun cell => (cell.name, cell.type)) := by
  simp only [refresh, List.map_map, Function.comp_def, refreshCell]

theorem refresh_references {depth : Nat} {environment : Environment}
    {references : AccountRuntime.References} {cells : List InitializedCell}
    (related : RuntimeReferences depth environment references cells) (store : Store) :
    RuntimeReferences depth environment references (refresh store cells) := by
  constructor
  · simpa only [refresh, List.map_map, Function.comp_def, refreshCell] using related.names
  · simp only [refresh, List.map_map]
    exact related.values

theorem refresh_stored {store : Store} {cells : List InitializedCell}
    (bounded : ∀ cell ∈ cells, cell.location < store.length) :
    InitializedCells (refresh store cells) store := by
  intro cell member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  have bound := bounded original originalMember
  have found : store.read? original.location = some (store[original.location]) :=
    List.getElem?_eq_getElem (bounded original originalMember)
  change store.read? original.location = some ((store.read? original.location).getD .unit)
  simp only [found, Option.getD_some]

theorem refresh_locations {store : Store} {cells : List InitializedCell} (separate : CellLocations cells) :
    CellLocations (refresh store cells) := by
  intro left leftMember right rightMember same
  obtain ⟨originalLeft, originalLeftMember, rfl⟩ := List.mem_map.mp leftMember
  obtain ⟨originalRight, originalRightMember, rfl⟩ := List.mem_map.mp rightMember
  exact separate originalLeft originalLeftMember originalRight originalRightMember same

/-- Value assertions are transported from the actual reads. A stale initial
value is never reused as evidence for a child frame. -/
theorem refresh_observed {store : Store} {cells : List InitializedCell}
    {accounts : StorageCorrespondence.Accounts} {state : RuntimeReturnDataEffectsSemantics.State}
    {bytes : List UInt8}
    (observed : ∀ cell ∈ cells, ∀ value, store.read? cell.location = some value →
      Observed accounts state bytes {cell with value := value})
    (bounded : ∀ cell ∈ cells, cell.location < store.length) :
    ∀ cell ∈ refresh store cells, Observed accounts state bytes cell := by
  intro cell member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  have bound := bounded original originalMember
  have found : store.read? original.location = some (store[original.location]) :=
    List.getElem?_eq_getElem (bounded original originalMember)
  simpa only [refreshCell, found, Option.getD_some] using observed original originalMember _ found

end Solcore.Frontend.RustHull.ChildFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ChildCallbackContextCorrespondence
/-! Captured ambient and creator cells remain available to child allocation.
Mutable shared values are read afresh from the current transport resources. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildCallbackContextCorrespondence
open Core Correspondence ScalarExecution ContractCallCorrespondence
open RuntimeCallEffectsCorrespondence (Layout sharedLocations)

structure Inventory (layout : Layout) (cells : List InitializedCell) (creator : Nat) : Prop where
  signature : cells.map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse
  shared : SharedCells cells (sharedLocations layout)
  separate : CellLocations cells
  below : ∀ cell ∈ cells, cell.location < layout.boundary
  creatorBelow : creator < layout.boundary
  creatorSeparate : ∀ cell ∈ cells, cell.location ≠ creator
  ambientOutside : ∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
    cell.location ∉ RuntimeCallEffectsCorrespondence.mutable layout
  creatorOutside : creator ∉ RuntimeCallEffectsCorrespondence.mutable layout

def context {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    (inventory : Inventory layout cells creator) : RuntimeChildCallEffectsCorrespondence.Context layout where
  valid read := (∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
    read cell.location = some cell.value) ∧ ∃ value, read creator = some value
  frame := by
    intro before after retained valid
    refine ⟨fun cell member ambient => ?_, ?_⟩
    · rw [retained _ (inventory.ambientOutside cell member ambient)]
      exact valid.1 cell member ambient
    · obtain ⟨value, found⟩ := valid.2
      exact ⟨value, (retained _ inventory.creatorOutside).trans found⟩

theorem initial {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    (inventory : Inventory layout cells creator) {store : Store}
    (stored : InitializedCells cells store) (present : ∃ value, store.read? creator = some value) :
    (context inventory).valid (prefixRead layout.boundary store) := by
  refine ⟨fun cell member _ => ?_, ?_⟩
  · simpa only [prefixRead, inventory.below cell member, ↓reduceIte] using stored cell member
  · simpa only [prefixRead, inventory.creatorBelow, ↓reduceIte] using present

theorem reads {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    (inventory : Inventory layout cells creator) {store : Store}
    (valid : (context inventory).valid (prefixRead layout.boundary store)) :
    (∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst → store.read? cell.location = some cell.value) ∧
      ∃ value, store.read? creator = some value := by
  refine ⟨fun cell member ambient => ?_, ?_⟩
  · simpa only [prefixRead, inventory.below cell member, ↓reduceIte] using valid.1 cell member ambient
  · simpa only [prefixRead, inventory.creatorBelow, ↓reduceIte] using valid.2

theorem Inventory.unique {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    (inventory : Inventory layout cells creator) : (cells.map InitializedCell.name).Nodup := by
  have names := congrArg (List.map Prod.fst) inventory.signature
  simp only [List.map_reverse, List.map_map, Function.comp_def] at names
  rw [names]
  decide

private theorem same_named {cells : List InitializedCell} (unique : (cells.map InitializedCell.name).Nodup)
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

private theorem named_location {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    (inventory : Inventory layout cells creator) {cell : InitializedCell} (member : cell ∈ cells)
    {name : String} {type : Core.Ty} {location : Nat} (named : cell.name = name)
    (selected : ∃ other ∈ cells, other.name = name ∧ other.reference = .cellRef type location) :
    cell.location = location := by
  obtain ⟨other, otherMember, otherName, reference⟩ := selected
  have same := same_named inventory.unique member otherMember (named.trans otherName.symm)
  subst other
  exact (Core.Value.cellRef.inj reference).2

/-- Every shared name is reused, and an older local reference is either a
shared reference or the explicitly installed creator reference. -/
def Origin (shared : List InitializedCell) (boundary : Nat) (cell : InitializedCell) : Prop :=
  (cell.name ∈ sharedSlotTypes.map Prod.fst → cell ∈ shared) ∧
  (cell.location < boundary → cell ∈ shared ∨ cell.name = "createHandler")

theorem fresh_origin {depth : Nat} {environment : Environment} {store : Store}
    {frame dispatcher gas code size known : CodeBuilder.Code} {shared : AccountRuntime.References}
    {cells : List InitializedCell} (references : RuntimeReferences depth environment shared cells)
    (signature : cells.map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse)
    {values : List Value} {gasValue codeValue sizeValue knownValue : Value}
    (frameRelated : CodeValue depth environment frame (bundleValues values)) (length : values.length = 8)
    (gasRelated : CodeValue depth environment gas gasValue)
    (codeRelated : CodeValue depth environment code codeValue)
    (sizeRelated : CodeValue depth environment size sizeValue)
    (knownRelated : CodeValue depth environment known knownValue) :
    FrameInitializersValid depth environment store frame dispatcher gas code size known shared (Origin cells store.length) := by
  have names : shared.map Prod.fst = (sharedSlotTypes.map Prod.fst).reverse := by
    rw [references.names]
    have names := congrArg (List.map Prod.fst) signature
    simpa only [List.map_map, List.map_reverse, Function.comp_def] using names
  apply frameInitializers_valid frameRelated length gasRelated codeRelated sizeRelated knownRelated
  intro name type location value absent bounded _
  exact ⟨fun member => False.elim (ChildFrameCorrespondence.absent_shared_name names absent member),
    fun before => False.elim (Nat.not_lt_of_ge bounded before)⟩

theorem creator_origin (cells : List InitializedCell) (boundary location : Nat) (value : Value) :
    Origin cells boundary (ContractRuntimeEffectsCorrespondence.creatorCell location value) := by
  refine ⟨?_, fun _ => Or.inr rfl⟩
  intro impossible
  simp [ContractRuntimeEffectsCorrespondence.creatorCell, sharedSlotTypes, Ambient.slots] at impossible

theorem shared_included {shared cells : List InitializedCell} {withCode : Bool} {boundary : Nat}
    (sharedSignature : shared.map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse)
    (signature : cells.map (fun cell => (cell.name, cell.type)) = RuntimeExtendedInitializedEffects.slots withCode)
    (origin : ∀ cell ∈ cells, Origin shared boundary cell) : ∀ cell ∈ shared, cell ∈ cells := by
  have unique : (shared.map InitializedCell.name).Nodup := by
    have names := congrArg (List.map Prod.fst) sharedSignature
    simp only [List.map_map, List.map_reverse, Function.comp_def] at names
    rw [names]
    decide
  intro cell member
  have typed : (cell.name, cell.type) ∈ sharedSlotTypes := by
    have listed := List.mem_map_of_mem (f := fun cell : InitializedCell => (cell.name, cell.type)) member
    rw [sharedSignature] at listed
    exact List.mem_reverse.mp listed
  have included : (cell.name, cell.type) ∈ RuntimeExtendedInitializedEffects.slots withCode := by
    have all : ∀ entry ∈ sharedSlotTypes, entry ∈ RuntimeExtendedInitializedEffects.slots withCode := by
      intro entry member
      simp only [sharedSlotTypes, Ambient.slots, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with (rfl | rfl | rfl | rfl | rfl) |
        (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals cases withCode <;> simp [RuntimeExtendedInitializedEffects.slots, Effects.slots, Ambient.slots]
    exact all _ typed
  rw [← signature] at included
  obtain ⟨other, otherMember, equal⟩ := List.mem_map.mp included
  have sameName := (Prod.mk.inj equal).1
  have otherShared := (origin other otherMember).1 (sameName ▸ List.mem_map_of_mem (f := Prod.fst) typed)
  exact (same_named unique otherShared member sameName) ▸ otherMember

private def mutableSlots (layout : Layout) : List EffectSlot :=
  [⟨"balances", WordMapping.type, layout.balances⟩,
   ⟨"returnData", WordMapping.type, layout.returnData⟩,
   ⟨"returnDataSize", .word, layout.returnDataSize⟩,
   ⟨"logs", WordMapping.type, layout.logs⟩,
   ⟨"logSize", .word, layout.logSize⟩,
   ⟨"memory", WordMapping.type, layout.memory⟩,
   ⟨"memorySize", .word, layout.storage.memorySize⟩,
   ⟨"world", AccountState.type, layout.storage.world⟩,
   ⟨"exit", .word, layout.storage.exit⟩,
   ⟨"returnOffset", .word, layout.storage.returnOffset⟩,
   ⟨"returnSize", .word, layout.storage.returnSize⟩]

private theorem mutable_members {layout : Layout} {cells : List InitializedCell}
    (members : ∀ slot ∈ RuntimeCallInitializedEffects.baseSlots layout.toReturnDataLayout,
      slot ∈ cells.map InitializedCell.effectSlot) :
    ∀ slot ∈ mutableSlots layout, slot ∈ cells.map InitializedCell.effectSlot := by
  intro slot member
  apply members slot
  simp only [mutableSlots, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [RuntimeCallInitializedEffects.baseSlots]

theorem ambient_outside {layout : Layout} {shared cells : List InitializedCell}
    (included : ∀ cell ∈ shared, cell ∈ cells) (separate : CellLocations cells)
    (members : ∀ slot ∈ RuntimeCallInitializedEffects.baseSlots layout.toReturnDataLayout,
      slot ∈ cells.map InitializedCell.effectSlot) :
    ∀ cell ∈ shared, cell.name ∈ Ambient.slots.map Prod.fst →
      cell.location ∉ RuntimeCallEffectsCorrespondence.mutable layout := by
  intro cell member ambient inside
  change cell.location ∈ (mutableSlots layout).map EffectSlot.location at inside
  obtain ⟨slot, slotMember, same⟩ := List.mem_map.mp inside
  obtain ⟨other, otherMember, equal⟩ := List.mem_map.mp (mutable_members members slot slotMember)
  have named : cell.name = slot.name := by
    rw [← equal]
    exact separate cell (included cell member) other otherMember (same ▸ congrArg EffectSlot.location equal).symm
  have names := List.mem_map_of_mem (f := EffectSlot.name) slotMember
  rw [← named] at names
  simp only [mutableSlots, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at names
  rcases names with named | named | named | named | named | named | named | named | named | named | named
  all_goals simp [named, Ambient.slots] at ambient

theorem creator_outside {layout : Layout} {shared cells : List InitializedCell} {creator boundary : Nat}
    (before : creator < boundary) (afterShared : ∀ cell ∈ shared, cell.location < creator)
    (origin : ∀ cell ∈ cells, Origin shared boundary cell)
    (members : ∀ slot ∈ RuntimeCallInitializedEffects.baseSlots layout.toReturnDataLayout,
      slot ∈ cells.map InitializedCell.effectSlot) : creator ∉ RuntimeCallEffectsCorrespondence.mutable layout := by
  intro inside
  change creator ∈ (mutableSlots layout).map EffectSlot.location at inside
  obtain ⟨slot, slotMember, same⟩ := List.mem_map.mp inside
  obtain ⟨cell, cellMember, equal⟩ := List.mem_map.mp (mutable_members members slot slotMember)
  have location : cell.location = creator := (congrArg EffectSlot.location equal).trans same
  rcases (origin cell cellMember).2 (location ▸ before) with sharedMember | named
  · have impossible := afterShared cell sharedMember
    rw [location] at impossible
    exact Nat.lt_irrefl _ impossible
  · have names := List.mem_map_of_mem (f := EffectSlot.name) slotMember
    have slotName : slot.name = "createHandler" := (congrArg EffectSlot.name equal).symm.trans named
    simp [mutableSlots, slotName] at names


/-- The current parent observations follow from its ordinary runtime relation
and the same concrete ambient reads retained by the callback context. -/
theorem parent_observed {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    (inventory : Inventory layout cells creator) {slots : List EffectSlot}
    (members : ∀ cell ∈ cells, cell.effectSlot ∈ slots)
    {baseline : Nat → Option Value} {image : Option (List UInt8)}
    {handlers : RuntimeCallEffectsCorrespondence.Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Store}
    (related : StateRel (RuntimeCallEffectsCorrespondence.model layout baseline slots image handlers) world state store)
    (valid : (context inventory).valid (prefixRead layout.boundary store)) :
    ∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
      ContractEnvironmentCorrespondence.initializedValue state.external.runtime.runtime.runtime.runtime.environment cell := by
  have environment := RuntimeEnvironmentEffectsCorrespondence.observations_related
    (RuntimeLogEffectsCorrespondence.runtime_related
    (RuntimeAccountEffectsCorrespondence.runtime_related (RuntimeCallEffectsCorrespondence.account_related related)))
  intro cell member ambient value specified
  have actual := environment _ (members cell member) value specified
  exact Option.some.inj (((reads inventory valid).1 cell member ambient).symm.trans actual)

/-- All reused cells are justified by their current reads; catalog links choose
one exact encoded world witness for both storage and child initialization. -/
theorem current_observed {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    (inventory : Inventory layout cells creator) {store : Store}
    (valid : (context inventory).valid (prefixRead layout.boundary store))
    (parent : RuntimeCallEffectsSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8)
    (ambient : ∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
      ContractEnvironmentCorrespondence.initializedValue parent.runtime.runtime.runtime.runtime.environment cell)
    {anchors : List CatalogWorldCorrespondence.Anchor}
    (linked : RuntimeLinkedWorldCorrespondence.StateRel anchors shared.world layout.storage.world store)
    (resources : AccountCallCorrespondence.SharedStateRel (sharedLocations layout) shared store) :
    ∃ accounts, accounts.map Prod.fst = shared.world ∧ CatalogWorldCorrespondence.Links anchors accounts ∧
      ∀ cell ∈ cells, ∀ value, store.read? cell.location = some value →
        ChildFrameCorrespondence.Observed accounts (ChildFrameCorrespondence.Initial parent request shared bytes) bytes
          {cell with value := value} := by
  obtain ⟨accounts, same, links, worldRead⟩ := linked
  refine ⟨accounts, same, links, ?_⟩
  intro cell member value found
  have signature : (cell.name, cell.type) ∈ sharedSlotTypes := by
    have present := List.mem_map_of_mem (f := fun cell : InitializedCell => (cell.name, cell.type)) member
    rw [inventory.signature] at present
    exact List.mem_reverse.mp present
  have readValue : ∀ name type location expected,
      (selected : ∃ other ∈ cells, other.name = name ∧ other.reference = .cellRef type location) →
      cell.name = name → store.read? location = some expected → value = expected := by
    intro name type location expected selected named read
    have located := named_location inventory member named selected
    exact Option.some.inj ((located ▸ found).symm.trans read)
  have world := readValue "world" AccountState.type layout.storage.world (StorageCorrespondence.world accounts) inventory.shared.world
  have complete := readValue "worldComplete" .bool layout.storage.complete (Value.bool shared.complete) inventory.shared.complete
  have logs := readValue "logs" WordMapping.type layout.logs (WordMapping.encode shared.logs) inventory.shared.logs
  have logSize := readValue "logSize" .word layout.logSize (Value.word shared.logSize) inventory.shared.logSize
  have balances := readValue "balances" WordMapping.type layout.balances (WordMapping.encode shared.balances) inventory.shared.balances
  constructor
  · intro expected specified
    change RuntimeInitializedEffects.expected accounts
      (ChildFrameCorrespondence.Initial parent request shared bytes).runtime.runtime.runtime.runtime cell.name = some expected at specified
    change value = expected
    simp only [sharedSlotTypes, Ambient.slots, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at signature
    rcases signature with (signature | signature | signature | signature | signature) | signature
    all_goals try (obtain ⟨named, typed⟩ := Prod.mk.inj signature; rw [named] at specified)
    · cases specified
      exact world named worldRead
    · cases specified
      exact complete named resources.complete
    · contradiction
    · contradiction
    · contradiction
    · rcases signature with signature | signature | signature | signature | signature | signature | signature | signature | signature | signature | signature | signature
      all_goals obtain ⟨named, _⟩ := Prod.mk.inj signature
      all_goals rw [named] at specified
      all_goals contradiction
  · intro expected specified
    change EnvironmentBuiltinCorrespondence.observation
      (ChildFrameCorrespondence.Initial parent request shared bytes).runtime.runtime.runtime.environment cell.name cell.type = some expected at specified
    change value = expected
    have ambientPair : (cell.name, cell.type) ∈ Ambient.slots := by
      simp only [sharedSlotTypes, List.mem_append] at signature
      rcases signature with sharedMember | ambientMember
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at sharedMember
        rcases sharedMember with equal | equal | equal | equal | equal
        all_goals obtain ⟨named, typed⟩ := Prod.mk.inj equal
        all_goals rw [named, typed] at specified
        all_goals contradiction
      · exact ambientMember
    have ambientName : cell.name ∈ Ambient.slots.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) ambientPair
    have inherited : EnvironmentBuiltinCorrespondence.observation
        (ChildFrameCorrespondence.Initial parent request shared bytes).runtime.runtime.runtime.environment cell.name cell.type =
        EnvironmentBuiltinCorrespondence.observation parent.runtime.runtime.runtime.runtime.environment cell.name cell.type := by
      simp only [Ambient.slots, List.mem_cons, List.not_mem_nil, or_false] at ambientPair
      rcases ambientPair with equal | equal | equal | equal | equal | equal | equal | equal | equal | equal | equal | equal
      all_goals obtain ⟨named, typed⟩ := Prod.mk.inj equal
      all_goals rw [named, typed]
      all_goals rfl
    rw [inherited] at specified
    have sameValue := ambient cell member ambientName expected specified
    have sameRead := (reads inventory valid).1 cell member ambientName
    exact (Option.some.inj (found.symm.trans sameRead)).trans sameValue
  · intro named
    change cell.name = "code" at named
    have present := List.mem_map_of_mem (f := Prod.fst) signature
    simp [named, sharedSlotTypes, Ambient.slots] at present
  · intro named
    change cell.name = "codeKnown" at named
    have present := List.mem_map_of_mem (f := Prod.fst) signature
    simp [named, sharedSlotTypes, Ambient.slots] at present
  · intro named
    change cell.name = "returnData" at named
    have present := List.mem_map_of_mem (f := Prod.fst) signature
    simp [named, sharedSlotTypes, Ambient.slots] at present
  · exact fun named => logs named resources.logs
  · exact fun named => logSize named resources.logSize
  · exact fun named => balances named resources.balances

/-- The exact inventory expected by actual allocateFrame is reconstructed at
callback entry, including writes performed since the closure was captured. -/
theorem refresh_ready {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    (inventory : Inventory layout cells creator) {store : Store}
    (bounded : layout.boundary ≤ store.length)
    (valid : (context inventory).valid (prefixRead layout.boundary store))
    (parent : RuntimeCallEffectsSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8)
    (ambient : ∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
      ContractEnvironmentCorrespondence.initializedValue parent.runtime.runtime.runtime.runtime.environment cell)
    {anchors : List CatalogWorldCorrespondence.Anchor}
    (linked : RuntimeLinkedWorldCorrespondence.StateRel anchors shared.world layout.storage.world store)
    (resources : AccountCallCorrespondence.SharedStateRel (sharedLocations layout) shared store) :
    ∃ accounts creatorValue, accounts.map Prod.fst = shared.world ∧ CatalogWorldCorrespondence.Links anchors accounts ∧
      InitializedCells (ChildFrameCorrespondence.refresh store cells) store ∧
      (ChildFrameCorrespondence.refresh store cells).map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse ∧
      CellLocations (ChildFrameCorrespondence.refresh store cells) ∧
      (∀ cell ∈ ChildFrameCorrespondence.refresh store cells,
        ChildFrameCorrespondence.Observed accounts (ChildFrameCorrespondence.Initial parent request shared bytes) bytes cell) ∧
      store.read? creator = some creatorValue ∧
      (∀ cell ∈ ChildFrameCorrespondence.refresh store cells, cell.location ≠ creator) := by
  obtain ⟨accounts, same, links, observed⟩ := current_observed inventory valid parent request shared bytes ambient linked resources
  obtain ⟨creatorValue, creatorRead⟩ := (reads inventory valid).2
  have below : ∀ cell ∈ cells, cell.location < store.length :=
    fun cell member => Nat.lt_of_lt_of_le (inventory.below cell member) bounded
  refine ⟨accounts, creatorValue, same, links, ChildFrameCorrespondence.refresh_stored below,
    (ChildFrameCorrespondence.refresh_signature store cells).trans inventory.signature,
    ChildFrameCorrespondence.refresh_locations inventory.separate,
    ChildFrameCorrespondence.refresh_observed observed below, creatorRead, ?_⟩
  intro cell member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact inventory.creatorSeparate original present


end Solcore.Frontend.RustHull.ChildCallbackContextCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ChildResultCorrespondence
/-! Actual child completion observes the exit before its status and extracts
complete return or revert bytes without changing any existing resource cell. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildResultCorrespondence
open Core CodeBuilder Correspondence ScalarExecution

def frameValue (status : Value) (state : RuntimeEffectsSemantics.State)
    (storage logs cursor balances world : Value) : Value :=
  .pair status (bundleValues [.word state.storage.exit, .word state.storage.returnOffset,
    .word state.storage.returnSize, WordMapping.encode state.memory.words, storage, logs, cursor, balances, world])

theorem childResult_evaluates {status : Semantics.Result Semantics.Value} {state : RuntimeEffectsSemantics.State}
    {response : Semantics.Result AccountCallSemantics.Response}
    (responded : ChildResultSemantics.Respond status state response)
    {depth : Nat} {environment : Environment} {store : Store} {result : Code}
    {statusValue storage logs cursor balances world : Value}
    (statusRelated : Correspondence.ResultRel .unit status statusValue)
    (framed : CodeValue depth environment result (frameValue statusValue state storage logs cursor balances world)) :
    ∃ target final, CallTransportCorrespondence.ResponseRel response target ∧
      Evaluates environment store (AccountRuntime.childResult result depth) target final ∧
      StoreRetains store final := by
  have snapshotRelated : CodeValue depth environment (AccountRuntime.second result)
      (bundleValues [.word state.storage.exit, .word state.storage.returnOffset,
        .word state.storage.returnSize, WordMapping.encode state.memory.words, storage, logs, cursor, balances, world]) :=
    fun extra here => .second (framed extra here)
  have exitRelated := snapshotRelated.part (index := 0) rfl
  have offsetRelated := snapshotRelated.part (index := 1) rfl
  have lengthRelated := snapshotRelated.part (index := 2) rfl
  have memoryRelated := snapshotRelated.part (index := 3) rfl
  have statusEvaluated : Evaluates environment store (AccountRuntime.first result depth) statusValue store :=
    .first (framed.evaluates store)
  have test (kind : Nat) : Evaluates environment store
      (binary .wordEq (part 0 9 (AccountRuntime.second result)) (number kind) depth)
      (.bool (state.storage.exit == Word.ofNatModulo kind)) store :=
    .binary (exitRelated.evaluates store) .word rfl
  have copied (success : Bool) {data : Semantics.Result MemorySemantics.Entries}
      (extracted : MemorySnapshotSemantics.Extract state.memory.words state.storage.returnOffset state.storage.returnSize data) :
      ∃ target final, CallTransportCorrespondence.ResponseRel (ChildResultSemantics.response success state.storage.returnSize data) target ∧
        Evaluates environment store
          (bindResult Calls.responseType (fun depth => MemorySnapshot.extract
            (part 3 9 (AccountRuntime.second result) depth) (part 1 9 (AccountRuntime.second result) depth)
            (part 2 9 (AccountRuntime.second result) depth)) (fun data =>
              AccountRuntime.callResult (CodeBuilder.boolean success) data (part 2 9 (AccountRuntime.second result))) depth) target final ∧
        StoreRetains store final := by
    obtain ⟨target, final, related, evaluated, retained⟩ := MemorySnapshotCorrespondence.extract_preserves extracted
      (memoryRelated.evaluates store) (offsetRelated.evaluates store) (lengthRelated.evaluates store)
    cases related with
    | language reason =>
        exact ⟨.inLeft Calls.responseType (.word reason), final, .language _, LanguageResult.bind_failure Calls.responseType evaluated, retained⟩
    | returned entries =>
        refine ⟨.inRight .word (CallTransportCorrespondence.responseValue ⟨success, entries, state.storage.returnSize⟩),
          final, .returned _, ?_, retained⟩
        apply LanguageResult.bind_success Calls.responseType evaluated
        exact .inRight (.pair .bool (.pair (.var (by simp)) ((lengthRelated.prepend [WordMapping.encode entries]).evaluates final)))
  cases responded with
  | invalid exit =>
      refine ⟨.inRight .word (CallTransportCorrespondence.responseValue (AccountCallSemantics.emptyResponse false)), store, .returned _, ?_, .refl _⟩
      apply Evaluates.ifTrue (by simpa only [exit, beq_self_eq_true] using test 3)
      exact .inRight (.pair .bool (.pair (.construct .unit) .word))
  | reverted exit extracted =>
      obtain ⟨target, final, related, evaluated, retained⟩ := copied false extracted
      refine ⟨target, final, related, ?_, retained⟩
      apply Evaluates.ifFalse (by simpa only [exit, show (Word.ofNatModulo 2 == Word.ofNatModulo 3) = false from by decide +kernel] using test 3)
      exact .ifTrue (by simpa only [exit, beq_self_eq_true] using test 2) evaluated
  | returned exit extracted =>
      obtain ⟨target, final, related, evaluated, retained⟩ := copied true extracted
      refine ⟨target, final, related, ?_, retained⟩
      apply Evaluates.ifFalse (by simpa only [exit, show (Word.ofNatModulo 1 == Word.ofNatModulo 3) = false from by decide +kernel] using test 3)
      apply Evaluates.ifFalse (by simpa only [exit, show (Word.ofNatModulo 1 == Word.ofNatModulo 2) = false from by decide +kernel] using test 2)
      exact .ifTrue (by simpa only [exit, beq_self_eq_true] using test 1) evaluated
  | failed invalid reverted returned failed =>
      subst status
      cases statusRelated with
      | language reason =>
          refine ⟨.inLeft Calls.responseType (.word reason), store, .language _, ?_, .refl _⟩
          apply Evaluates.ifFalse (by simpa only [beq_eq_false_iff_ne.mpr invalid] using test 3)
          apply Evaluates.ifFalse (by simpa only [beq_eq_false_iff_ne.mpr reverted] using test 2)
          apply Evaluates.ifFalse (by simpa only [beq_eq_false_iff_ne.mpr returned] using test 1)
          exact .caseLeft statusEvaluated (.inLeft (.var rfl))
  | completed invalid reverted returned finished =>
      subst status
      cases statusRelated with
      | value related =>
          cases related
          refine ⟨.inRight .word (CallTransportCorrespondence.responseValue (AccountCallSemantics.emptyResponse true)), store, .returned _, ?_, .refl _⟩
          apply Evaluates.ifFalse (by simpa only [beq_eq_false_iff_ne.mpr invalid] using test 3)
          apply Evaluates.ifFalse (by simpa only [beq_eq_false_iff_ne.mpr reverted] using test 2)
          apply Evaluates.ifFalse (by simpa only [beq_eq_false_iff_ne.mpr returned] using test 1)
          exact .caseRight statusEvaluated (.inRight (.pair .bool (.pair (.construct .unit) .word)))

end Solcore.Frontend.RustHull.ChildResultCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ChildFrameResultCorrespondence
/-! The actual frame completion lookup and child-result wrapper agree with
the independent exit rules, including lookup faults and revert data. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildFrameCorrespondence
open Core Correspondence ScalarExecution CodeBuilder

theorem completion_components {status : Semantics.Result Semantics.Value} {statusValue : Value}
    {state : RuntimeReturnDataEffectsSemantics.State} {accounts : StorageCorrespondence.Accounts}
    (related : ResultRel .unit status statusValue)
    (world : accounts.map Prod.fst = state.runtime.runtime.runtime.runtime.storage.world) :
    ∃ completed storage,
      ResultRel .unit (ChildFrameSemantics.completedStatus status state.runtime.runtime.runtime.runtime) completed ∧
      frameCompletionValue statusValue (RuntimeReturnDataEffectsFrameCorrespondence.snapshotValues state accounts)
        (StorageCorrespondence.get accounts state.runtime.runtime.runtime.runtime.storage.address
          state.runtime.runtime.runtime.runtime.storage.complete) =
      ChildResultCorrespondence.frameValue completed state.runtime.runtime.runtime.runtime storage
        (WordMapping.encode state.runtime.runtime.words) (.word state.runtime.runtime.cursor)
        (WordMapping.encode state.runtime.balances) (StorageCorrespondence.world accounts) := by
  have source := StorageCorrespondence.get_source accounts state.runtime.runtime.runtime.runtime.storage.address
    state.runtime.runtime.runtime.runtime.storage.complete
  rw [world] at source
  cases found : StorageCorrespondence.get accounts state.runtime.runtime.runtime.runtime.storage.address
      state.runtime.runtime.runtime.runtime.storage.complete with
  | error reason =>
      have sourceFound : StorageSemantics.get state.runtime.runtime.runtime.runtime.storage.world
          state.runtime.runtime.runtime.runtime.storage.address state.runtime.runtime.runtime.runtime.storage.complete = .error reason := by
        simpa only [found, Except.map] using source.symm
      refine ⟨.inLeft .unit (.word reason), WordMapping.encode [], ?_, ?_⟩
      · simp only [ChildFrameSemantics.completedStatus, sourceFound]
        exact .language _
      · rfl
  | ok account =>
      obtain ⟨account, identity⟩ := account
      have sourceFound : StorageSemantics.get state.runtime.runtime.runtime.runtime.storage.world
          state.runtime.runtime.runtime.runtime.storage.address state.runtime.runtime.runtime.runtime.storage.complete = .ok account := by
        simpa only [found, Except.map] using source.symm
      exact ⟨statusValue, WordMapping.encode account.storage,
        by simpa only [ChildFrameSemantics.completedStatus, sourceFound] using related, by rfl⟩

theorem finish_evaluates {depth : Nat} {environment : Environment} {store : Store} {result : Code}
    {status : Semantics.Result Semantics.Value} {statusValue : Value}
    {state : RuntimeReturnDataEffectsSemantics.State} {accounts : StorageCorrespondence.Accounts}
    {response : Semantics.Result AccountCallSemantics.Response}
    (statusRelated : ResultRel .unit status statusValue)
    (world : accounts.map Prod.fst = state.runtime.runtime.runtime.runtime.storage.world)
    (responded : ChildResultSemantics.Respond
      (ChildFrameSemantics.completedStatus status state.runtime.runtime.runtime.runtime)
      state.runtime.runtime.runtime.runtime response)
    (framed : CodeValue depth environment result
      (frameCompletionValue statusValue (RuntimeReturnDataEffectsFrameCorrespondence.snapshotValues state accounts)
        (StorageCorrespondence.get accounts state.runtime.runtime.runtime.runtime.storage.address
          state.runtime.runtime.runtime.runtime.storage.complete))) :
    ∃ target final, CallTransportCorrespondence.ResponseRel response target ∧
      Core.Evaluates environment store (AccountRuntime.childResult result depth) target final ∧ StoreRetains store final := by
  obtain ⟨completed, storage, related, same⟩ := completion_components statusRelated world
  rw [same] at framed
  exact ChildResultCorrespondence.childResult_evaluates responded related framed

theorem bind_evaluates {depth : Nat} {environment : Environment} {initial store : Store}
    {function argument : Code}
    {status : Semantics.Result Semantics.Value} {statusValue : Value}
    {state : RuntimeReturnDataEffectsSemantics.State} {accounts : StorageCorrespondence.Accounts}
    {response : Semantics.Result AccountCallSemantics.Response}
    (statusRelated : ResultRel .unit status statusValue)
    (world : accounts.map Prod.fst = state.runtime.runtime.runtime.runtime.storage.world)
    (responded : ChildResultSemantics.Respond
      (ChildFrameSemantics.completedStatus status state.runtime.runtime.runtime.runtime)
      state.runtime.runtime.runtime.runtime response)
    (called : Core.Evaluates environment initial (apply function argument depth)
      (frameCompletionValue statusValue (RuntimeReturnDataEffectsFrameCorrespondence.snapshotValues state accounts)
        (StorageCorrespondence.get accounts state.runtime.runtime.runtime.runtime.storage.address
          state.runtime.runtime.runtime.runtime.storage.complete)) store) :
    ∃ target final, CallTransportCorrespondence.ResponseRel response target ∧
      Core.Evaluates environment initial (bind (apply function argument) AccountRuntime.childResult depth) target final ∧
      StoreRetains store final := by
  obtain ⟨target, final, related, evaluated, retained⟩ := finish_evaluates (store := store)
    statusRelated world responded (CodeValue.bound depth environment _)
  exact ⟨target, final, related, .letE called evaluated, retained⟩

end Solcore.Frontend.RustHull.ChildFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ChildFrameStateFrameCorrespondence
/-! Child-local mutable cells are freshly allocated. Only the shared account,
log and balance cells can change below the child's allocation boundary. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildFrameCorrespondence
open Core Correspondence ScalarExecution

def sharedLocations (layout : RuntimeReturnDataEffectsCorrespondence.Layout) : AccountCallCorrespondence.SharedLocations :=
  ⟨layout.storage.world, layout.logs, layout.logSize, layout.balances, layout.storage.complete⟩

def mutable (layout : RuntimeReturnDataEffectsCorrespondence.Layout) : List Nat :=
  layout.returnData :: layout.returnDataSize :: RuntimeLogEffectsCorrespondence.mutable layout.toLogLayout

def mutableSlots (layout : RuntimeReturnDataEffectsCorrespondence.Layout) : List EffectSlot :=
  [⟨"returnData", WordMapping.type, layout.returnData⟩, ⟨"returnDataSize", .word, layout.returnDataSize⟩,
   ⟨"logs", WordMapping.type, layout.logs⟩, ⟨"logSize", .word, layout.logSize⟩,
   ⟨"memory", WordMapping.type, layout.memory⟩, ⟨"memorySize", .word, layout.storage.memorySize⟩,
   ⟨"world", AccountState.type, layout.storage.world⟩, ⟨"exit", .word, layout.storage.exit⟩,
   ⟨"returnOffset", .word, layout.storage.returnOffset⟩, ⟨"returnSize", .word, layout.storage.returnSize⟩]

theorem mutable_early_shared {cells sharedCells : List InitializedCell} {initial allocated : Store}
    {state : RuntimeReturnDataEffectsSemantics.State} {bytes : List UInt8}
    (ready : Ready cells allocated state bytes)
    (signature : sharedCells.map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse)
    (origins : ∀ cell ∈ cells, cell.location < initial.length → cell ∈ sharedCells ∨ cell.name = "createHandler")
    {location : Nat} (below : location < initial.length) (member : location ∈ mutable ready.layout) :
    location ∈ (sharedLocations ready.layout).mutable := by
  have mapped : (mutableSlots ready.layout).map EffectSlot.location = mutable ready.layout := rfl
  rw [← mapped] at member
  obtain ⟨slot, slotMember, same⟩ := List.mem_map.mp member
  have base : slot ∈ RuntimeCallInitializedEffects.baseSlots ready.layout := by
    simp only [mutableSlots, List.mem_cons, List.not_mem_nil, or_false] at slotMember
    rcases slotMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [RuntimeCallInitializedEffects.baseSlots]
  obtain ⟨cell, cellMember, slotEqual⟩ := List.mem_map.mp (ready.members slot base)
  have sameLocation : cell.location = location := (congrArg EffectSlot.location slotEqual).trans same
  rcases origins cell cellMember (sameLocation ▸ below) with shared | creator
  · have present : cell.name ∈ sharedSlotTypes.map Prod.fst := by
      have member := List.mem_map_of_mem (f := fun cell : InitializedCell => (cell.name, cell.type)) shared
      rw [signature] at member
      exact List.mem_map_of_mem (List.mem_reverse.mp member)
    have named : cell.name = slot.name := congrArg EffectSlot.name slotEqual
    rw [named] at present
    simp only [mutableSlots, List.mem_cons, List.not_mem_nil, or_false] at slotMember
    rcases slotMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (solve | simp [sharedSlotTypes, Ambient.slots] at present)
      | (rw [← same]; simp [sharedLocations, AccountCallCorrespondence.SharedLocations.mutable])
  · have named : slot.name = "createHandler" := (congrArg EffectSlot.name slotEqual).symm.trans creator
    simp only [mutableSlots, List.mem_cons, List.not_mem_nil, or_false] at slotMember
    rcases slotMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp at named

theorem other_related {layout : RuntimeReturnDataEffectsCorrespondence.Layout}
    {baseline : Nat → Option Value} {slots : List EffectSlot} {image : Option (List UInt8)}
    {world : World} {state : Semantics.State RuntimeReturnDataEffectsSemantics.State} {store : Store}
    (related : StateRel (RuntimeReturnDataEffectsCorrespondence.model layout baseline slots image) world state store)
    {location : Nat} (outside : location ∉ mutable layout) : prefixRead layout.boundary store location = baseline location := by
  have separate : location ≠ layout.returnData ∧ location ≠ layout.returnDataSize ∧
      location ∉ RuntimeLogEffectsCorrespondence.mutable layout.toLogLayout := by
    simpa only [mutable, List.mem_cons, not_or] using outside
  have passive := RuntimeLogEffectsCorrespondence.other_related
    (RuntimeAccountEffectsCorrespondence.runtime_related (RuntimeReturnDataEffectsCorrespondence.account_related related)) separate.2.2
  simpa only [RuntimeReturnDataEffectsCorrespondence.patched, separate.1, separate.2.1, ↓reduceIte] using passive

theorem parent_frame {cells sharedCells : List InitializedCell} {initial suffix final : Store}
    {state : RuntimeReturnDataEffectsSemantics.State} {bytes : List UInt8}
    (ready : Ready cells (initial ++ suffix) state bytes)
    (signature : sharedCells.map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse)
    (origins : ∀ cell ∈ cells, cell.location < initial.length → cell ∈ sharedCells ∨ cell.name = "createHandler")
    {world : World} {next : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    (related : StateRel (RuntimeReturnDataEffectsCorrespondence.model ready.layout
      (prefixRead ready.layout.boundary (initial ++ suffix)) (cells.map InitializedCell.effectSlot) (some bytes)) world next final) :
    AccountCallCorrespondence.SharedFrame (sharedLocations ready.layout) initial final := by
  refine ⟨?_, ?_⟩
  · have bounded := related.external.1
    rw [ready.boundary] at bounded
    exact Nat.le_trans (by simp) bounded
  · intro location value outside found
    have below : location < initial.length := (List.getElem?_eq_some_iff.mp found).1
    have beforeBoundary : location < ready.layout.boundary := by rw [ready.boundary]; exact Nat.lt_of_lt_of_le below (by simp)
    have preserved := other_related related
      (fun member => outside (mutable_early_shared ready signature origins below member))
    have same : final.read? location = initial.read? location := by
      simpa only [prefixRead, beforeBoundary, ↓reduceIte, Core.Store.read?, List.getElem?_append_left below] using preserved
    exact same.trans found

theorem shared_state {cells : List InitializedCell} {initial final : Store}
    {state : RuntimeReturnDataEffectsSemantics.State} {bytes : List UInt8}
    (ready : Ready cells initial state bytes) (separate : CellLocations cells)
    {world : World} {next : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    (related : StateRel (RuntimeReturnDataEffectsCorrespondence.model ready.layout
      (prefixRead ready.layout.boundary initial) (cells.map InitializedCell.effectSlot) (some bytes)) world next final)
    (depth : Word) :
    AccountCallCorrespondence.SharedStateRel (sharedLocations ready.layout)
      (RuntimeCallEffectsSemantics.shared ⟨next.external, depth⟩) final := by
  have account := RuntimeReturnDataEffectsCorrespondence.account_related related
  have logs := RuntimeAccountEffectsCorrespondence.runtime_related account
  have logState := RuntimeLogEffectsCorrespondence.logs_related logs
  have runtime := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related (RuntimeLogEffectsCorrespondence.runtime_related logs))
  refine ⟨runtime.world, logState.logs.logs, logState.logs.logSize,
    RuntimeAccountEffectsCorrespondence.balances_related account, runtime.complete, ?_⟩
  let selected : List EffectSlot := [⟨"world", AccountState.type, ready.layout.storage.world⟩,
    ⟨"logs", WordMapping.type, ready.layout.logs⟩, ⟨"logSize", .word, ready.layout.logSize⟩,
    ⟨"balances", WordMapping.type, ready.layout.balances⟩, ⟨"worldComplete", .bool, ready.layout.storage.complete⟩]
  have included : ∀ slot ∈ selected, slot ∈ cells.map InitializedCell.effectSlot := by
    intro slot member
    apply ready.members
    simp only [selected, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals simp [RuntimeCallInitializedEffects.baseSlots]
  exact ContractCallCorrespondence.effectSlots_distinct separate included (by change (["world", "logs", "logSize", "balances", "worldComplete"] : List String).Nodup; decide)

theorem shared_cells {cells sharedCells : List InitializedCell} {store : Store}
    {state : RuntimeReturnDataEffectsSemantics.State} {bytes : List UInt8}
    (ready : Ready cells store state bytes)
    (origins : ∀ cell ∈ cells, cell.name ∈ sharedSlotTypes.map Prod.fst → cell ∈ sharedCells) :
    ContractCallCorrespondence.SharedCells sharedCells (sharedLocations ready.layout) := by
  apply RuntimeCallInitializedEffects.shared_cells ready.members
  intro cell member named
  apply origins cell member
  simp only [ContractCallCorrespondence.dispatchSharedNames, List.mem_cons, List.not_mem_nil, or_false] at named
  rcases named with named | named | named | named | named
  all_goals simp [named, sharedSlotTypes]

theorem shared_references_unique {depth : Nat} {environment : Environment}
    {shared : AccountRuntime.References} {left right : AccountCallCorrespondence.SharedLocations}
    (first : AccountCallCorrespondence.SharedReferences depth environment shared left)
    (second : AccountCallCorrespondence.SharedReferences depth environment shared right) : left = right := by
  have world := (Value.cellRef.inj (Core.evaluation_deterministic (first.world.evaluates []) (second.world.evaluates [])).1).2
  have logs := (Value.cellRef.inj (Core.evaluation_deterministic (first.logs.evaluates []) (second.logs.evaluates [])).1).2
  have logSize := (Value.cellRef.inj (Core.evaluation_deterministic (first.logSize.evaluates []) (second.logSize.evaluates [])).1).2
  have balances := (Value.cellRef.inj (Core.evaluation_deterministic (first.balances.evaluates []) (second.balances.evaluates [])).1).2
  have complete := (Value.cellRef.inj (Core.evaluation_deterministic (first.complete.evaluates []) (second.complete.evaluates [])).1).2
  cases left
  cases right
  simp_all

end Solcore.Frontend.RustHull.ChildFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ChildFrameInvokeCorrespondence
/-! A compiled catalog child executes through its actual fresh allocator,
captured frame closure and completion wrapper. The resulting shared state and
code links are returned to account dispatch; caller-local cells are retained. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildFrameCorrespondence
open Core Correspondence ScalarExecution CodeBuilder

theorem invoke_evaluates {source : ChildFrameSemantics.Code} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame source.program source.body (RuntimeExtendedInitializedEffects.slots true) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram (ContractReturnDataCorrespondence.supported true) source.functions)
    {depth : Nat} {environment captured : Environment} {initial : Store}
    {frame dispatcher creator gas code size known function : Code} {closure : Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : CodeValue depth environment function closure)
    (parent : RuntimeCallEffectsSemantics.State) (request : AccountCallSemantics.Request)
    (sharedState : AccountCallSemantics.Shared)
    {shared : AccountRuntime.References} {sharedCells : List InitializedCell}
    {accounts : StorageCorrespondence.Accounts} (world : accounts.map Prod.fst = sharedState.world)
    (references : RuntimeReferences depth environment shared sharedCells)
    (signature : sharedCells.map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse)
    (initialized : InitializedCells sharedCells initial) (separate : CellLocations sharedCells)
    (observed : ∀ cell ∈ sharedCells, Observed accounts (Initial parent request sharedState source.bytes) source.bytes cell)
    {creatorLocation : Nat} {creatorValue : Value}
    (creatorRelated : CodeValue depth environment creator (.cellRef (OptionalCell.cellType Creation.callbackType) creatorLocation))
    (creatorFound : initial.read? creatorLocation = some creatorValue)
    (creatorSeparate : ∀ cell ∈ sharedCells, cell.location ≠ creatorLocation)
    (frameRelated : CodeValue depth environment frame (CallTransportCorrespondence.requestValue request))
    (gasRelated : CodeValue depth environment gas (optionalWordValue (some request.gas)))
    (codeRelated : CodeValue depth environment code (WordMapping.encode (Memory.packBytes source.bytes)))
    (sizeRelated : CodeValue depth environment size (.word (Word.ofNatModulo source.bytes.length)))
    (knownRelated : CodeValue depth environment known (.bool true))
    {locations : AccountCallCorrespondence.SharedLocations} {anchors : List CatalogWorldCorrespondence.Anchor}
    (sharedReferences : AccountCallCorrespondence.SharedReferences depth environment shared locations)
    (linked : RuntimeLinkedWorldCorrespondence.StateRel anchors sharedState.world locations.world initial)
    {status : Semantics.Result Semantics.Value} {finalSource : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    {response : Semantics.Result AccountCallSemantics.Response}
    (evaluated : Semantics.EvalFunction source.functions (RuntimeReturnDataEffectsSemantics.effects (some source.bytes))
      source.entry [] ⟨[], Initial parent request sharedState source.bytes⟩ status finalSource)
    (responded : ChildResultSemantics.Respond
      (ChildFrameSemantics.completedStatus status finalSource.external.runtime.runtime.runtime.runtime)
      finalSource.external.runtime.runtime.runtime.runtime response) :
    ∃ target final, Core.Evaluates environment initial
      (AccountRuntime.allocateFrame (RuntimeExtendedInitializedEffects.slots true) shared frame dispatcher creator gas code size known
        (fun values => bind (apply function (packet values)) AccountRuntime.childResult) depth) target final ∧
      CallTransportCorrespondence.ResponseRel response target ∧
      AccountCallCorrespondence.LinkedSharedStateRel anchors locations
        (RuntimeCallEffectsSemantics.shared ⟨finalSource.external, request.depth⟩) final ∧
      AccountCallCorrespondence.SharedFrame locations initial final := by
  apply allocateFrame_initializes parent request sharedState source.bytes world references signature initialized separate observed
    creatorRelated creatorFound creatorSeparate frameRelated gasRelated codeRelated sizeRelated knownRelated
    (fun values => bind (apply function (packet values)) AccountRuntime.childResult)
    (fun target final => CallTransportCorrespondence.ResponseRel response target ∧
      AccountCallCorrespondence.LinkedSharedStateRel anchors locations
        (RuntimeCallEffectsSemantics.shared ⟨finalSource.external, request.depth⟩) final ∧
      AccountCallCorrespondence.SharedFrame locations initial final)
  intro extra suffix cells values valuesRelated stored cellsSignature allSeparate origins sharedOrigins ready
  have cellsSeparate := allSeparate.subset (fun _ member => List.mem_append_right _ member)
  have unique : (sharedCells.map InitializedCell.name).Nodup := by
    have names := congrArg (List.map Prod.fst) signature
    simp only [List.map_map, Function.comp_def, List.map_reverse] at names
    rw [names]
    decide
  have locationsEqual : sharedLocations ready.layout = locations :=
    shared_references_unique ((shared_cells ready sharedOrigins).references unique references) sharedReferences
  have initialLinked : RuntimeLinkedWorldCorrespondence.StateRel anchors sharedState.world ready.layout.storage.world (initial ++ suffix) := by
    have same := congrArg AccountCallCorrespondence.SharedLocations.world locationsEqual
    change ready.layout.storage.world = locations.world at same
    rw [same]
    exact linked.retained (StoreRetains.append initial suffix)
  have linkedState := RuntimeLinkedReturnDataEffectsCorrespondence.of_base ready.related initialLinked
  let slots := cells.map InitializedCell.effectSlot
  have slotTypes : RuntimeReturnDataEffectsFrameCorrespondence.slotTypes slots = RuntimeExtendedInitializedEffects.slots true := by
    simpa only [RuntimeReturnDataEffectsFrameCorrespondence.slotTypes, RuntimeLogEffectsFrameCorrespondence.slotTypes,
      MemoryFrameCorrespondence.slotTypes, slots, List.map_map, Function.comp_def, InitializedCell.effectSlot] using cellsSignature
  have environmentRelated := initialized_environment cells (RuntimeExtendedInitializedEffects.initialized_unique cellsSignature)
    (Value.unit :: bundleValues (cells.map InitializedCell.reference) :: captured)
  have runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (RuntimeReturnDataEffectsFrameCorrespondence.slotTypes slots)) Renaming.id
      ((cells.map InitializedCell.reference).reverse ++ Value.unit :: bundleValues (cells.map InitializedCell.reference) :: captured) := by
    simpa only [RuntimeReturnDataEffectsFrameCorrespondence.slotTypes, RuntimeLogEffectsFrameCorrespondence.slotTypes,
      MemoryFrameCorrespondence.slotTypes, slots, List.map_map, Function.comp_def, InitializedCell.effectSlot] using environmentRelated
  have member := ready.members
  obtain ⟨extension, statusValue, accounts', bodyStore, represented, statusRelated, called, state, _⟩ :=
    RuntimeLinkedReturnDataEffectsFrameCorrespondence.compileFrame_call_preserves_observed
      (by simpa only [slotTypes] using accepted)
      (by simpa only [ContractReturnDataCorrespondence.supported_actual slotTypes, ChildFrameSemantics.Code.functions,
        ChildFrameSemantics.Code.entry, AccountRuntime.frameFunction, AccountRuntime.frameEntry] using eligible)
      closureRelated ((resolved.prepend extra).evaluates (initial ++ suffix))
      ((CodeValue.packet valuesRelated).evaluates (initial ++ suffix)) (by simp [slots]) runtime
      (RuntimeExtendedInitializedEffects.initialized_separate cellsSignature)
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots])) ready.codes
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots]))
      (member _ (by simp [RuntimeCallInitializedEffects.baseSlots])) ready.mode linkedState ready.passive evaluated
  have baseState := RuntimeLinkedReturnDataEffectsCorrespondence.base_related state
  have finalShared : AccountCallCorrespondence.LinkedSharedStateRel anchors (sharedLocations ready.layout)
      (RuntimeCallEffectsSemantics.shared ⟨finalSource.external, request.depth⟩) bodyStore :=
    ⟨shared_state ready cellsSeparate baseState request.depth, RuntimeLinkedReturnDataEffectsCorrespondence.linked_related state⟩
  have retained := parent_frame ready signature origins baseState
  rw [locationsEqual] at finalShared retained
  obtain ⟨target, final, resultRelated, executed, extractionRetains⟩ := bind_evaluates statusRelated represented responded called
  exact ⟨target, final, executed, resultRelated, finalShared.retained extractionRetains,
    retained.trans (AccountCallCorrespondence.SharedFrame.ofRetains extractionRetains)⟩

end Solcore.Frontend.RustHull.ChildFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ChildCatalogExecutionCorrespondence
/-! Source catalog selection is connected to compiled closure indices and the
actual account dispatch lookup. Each selected child receives a fresh frame and
current shared resources; the proof does not assume child evaluation in Core. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildCatalogExecutionCorrespondence
open Core Correspondence ScalarExecution CodeBuilder
open RuntimeCallEffectsCorrespondence (Layout sharedLocations)
open AccountCallCorrespondence

/-- All conditions concern source selection, compilation structure and runtime
identity representation. Child execution is derived separately below. -/
def CatalogConnection (sourceCatalog : ChildFrameSemantics.Catalog)
    (catalog : List AccountRuntime.CodeDefinition) (anchors : List CatalogWorldCorrespondence.Anchor) : Prop :=
  ∀ address source, ChildFrameSemantics.select sourceCatalog address = some source →
    ∃ index definition, catalog[index]? = some definition ∧ source.program = definition.program ∧
      AccountRuntime.select definition.program.objects definition.path = .ok source.body ∧
      source.bytes = definition.bytes ∧
      CatalogWorldCorrespondence.Anchor.mk address source.bytes (index + 2) ∈ anchors ∧
      Word.ofNatModulo (index + 2) ≠ Word.zero ∧
      (List.range (catalog.length + 1)).find?
        (fun candidate => Word.ofNatModulo (index + 2) == Word.ofNatModulo (candidate + 1)) = some (index + 1) ∧
      DerivationCorrespondence.ExecutableProgram (ContractReturnDataCorrespondence.supported true) source.functions

theorem selected_frame {sourceCatalog : ChildFrameSemantics.Catalog}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    (connection : CatalogConnection sourceCatalog catalog anchors)
    {fuel : Nat} {others : List Core.Expr}
    (compiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    {captured environment : Environment} {values : List Value} {closure : Value} {depth : Nat} {functions : Code}
    (closures : CapturedClosures captured others values)
    (functionsRelated : CodeValue depth environment functions (bundleValues (closure :: values)))
    {address : Word} {source : ChildFrameSemantics.Code}
    (selected : ChildFrameSemantics.select sourceCatalog address = some source) :
    ∃ index expression value,
      CatalogWorldCorrespondence.Anchor.mk address source.bytes (index + 2) ∈ anchors ∧
      Word.ofNatModulo (index + 2) ≠ Word.zero ∧
      (List.range (others.length + 1)).find?
        (fun candidate => Word.ofNatModulo (index + 2) == Word.ofNatModulo (candidate + 1)) = some (index + 1) ∧
      AccountRuntime.compileFrame source.program source.body (RuntimeExtendedInitializedEffects.slots true) fuel = .ok expression ∧
      DerivationCorrespondence.ExecutableProgram (ContractReturnDataCorrespondence.supported true) source.functions ∧
      CapturedClosure expression captured value ∧
      CodeValue depth environment (part (index + 1) (others.length + 1) functions) value := by
  obtain ⟨index, definition, found, program, body, _, anchored, nonzero, first, eligible⟩ := connection address source selected
  obtain ⟨code, expression, value, codeSelected, accepted, captured, referenced⟩ :=
    ContractCatalogCorrespondence.catalog_reference compiled closures functionsRelated found
  have same : code = source.body := Except.ok.inj (codeSelected.symm.trans body)
  subst code
  refine ⟨index, expression, value, anchored, nonzero, ?_, ?_, eligible, captured, referenced⟩
  · simpa only [compiled.length] using first
  · simpa only [program] using accepted

theorem child_runs_preserves {sourceCatalog : ChildFrameSemantics.Catalog}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    (connection : CatalogConnection sourceCatalog catalog anchors)
    {fuel : Nat} {others : List Core.Expr}
    (compiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    {captured environment : Environment} {values : List Value} {closure : Value} {depth : Nat}
    {functions dispatcher creator : Code} {shared : AccountRuntime.References}
    (closures : CapturedClosures captured others values)
    (functionsRelated : CodeValue depth environment functions (bundleValues (closure :: values)))
    {layout : Layout} {cells : List InitializedCell} {creatorLocation : Nat}
    (inventory : ChildCallbackContextCorrespondence.Inventory layout cells creatorLocation)
    (references : RuntimeReferences depth environment shared cells)
    (creatorRelated : CodeValue depth environment creator (.cellRef (OptionalCell.cellType Creation.callbackType) creatorLocation))
    (parent : RuntimeCallEffectsSemantics.State)
    (ambient : ∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
      ContractEnvironmentCorrespondence.initializedValue parent.runtime.runtime.runtime.runtime.environment cell) :
    ChildRunPreservation anchors (sharedLocations layout) shared
      (RuntimeCatalogDispatchCorrespondence.runFrame (RuntimeExtendedInitializedEffects.slots true)
        (others.length + 1) functions shared dispatcher creator)
      (ChildFrameSemantics.CallFree sourceCatalog parent)
      (RuntimeChildCallEffectsCorrespondence.childReady layout (ChildCallbackContextCorrespondence.context inventory))
      depth environment := by
  intro caller request initialShared response finalShared computed extra store extended precompiled sharedReferences argument related ready
  cases computed with
  | @executed caller request initialShared account source status finalSource response ordinary found selected known evaluated responded =>
    obtain ⟨index, expression, value, anchored, nonzero, first, accepted, eligible, capturedFrame, functionRelated⟩ :=
      selected_frame connection compiled closures functionsRelated selected
    obtain ⟨accounts, actualAccount, sameWorld, links, worldRead, sourceFound, actualFound, code⟩ :=
      RuntimeLinkedWorldCorrespondence.selected related.linked anchored
    have sameAccount : actualAccount = account := Option.some.inj (sourceFound.symm.trans found)
    subst actualAccount
    let baseDepth := depth + extra.length
    let baseEnvironment := extra ++ environment
    let afterLookup := StorageCorrespondence.getStore accounts request.target initialShared.complete baseEnvironment store
    have retained : StoreRetains store afterLookup := StoreRetains.append _ _
    have afterReady := RuntimeChildCallEffectsCorrespondence.childReady_preserved
      (SharedFrame.ofRetains retained) ready
    obtain ⟨freshAccounts, creatorValue, freshWorld, _, stored, signature, separate, observed, creatorRead, creatorSeparate⟩ :=
      ChildCallbackContextCorrespondence.refresh_ready inventory afterReady.1 afterReady.2
        parent request initialShared source.bytes ambient (related.linked.retained retained) (related.shared.retained retained)
    let recordValue := StorageCorrespondence.record account (index + 2)
    let recordCode : Code := fun here => .var (here - baseDepth - 1)
    have recordRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment) recordCode recordValue :=
      CodeValue.bound baseDepth baseEnvironment recordValue
    have frameRelated := (childRequest_value argument).prepend [recordValue]
    have gasRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment)
        (present (part 5 8 (childRequest extended))) (optionalWordValue (some request.gas)) := by
      intro prefixValues current
      exact .inRight ((frameRelated.part (index := 5) rfl) prefixValues current)
    have codeRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment)
        (part 4 9 recordCode) (WordMapping.encode (Memory.packBytes source.bytes)) := by
      simpa only [StorageCorrespondence.record, known, Option.getD_some, List.length_cons, List.length_nil] using recordRelated.part (index := 4) rfl
    have sizeRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment)
        (part 5 9 recordCode) (.word (Word.ofNatModulo source.bytes.length)) := by
      simpa only [StorageCorrespondence.record, known, Option.getD_some, List.length_cons, List.length_nil] using recordRelated.part (index := 5) rfl
    have knownRelated : CodeValue (baseDepth + 1) (recordValue :: baseEnvironment)
        (part 6 9 recordCode) (.bool true) := by
      simpa only [StorageCorrespondence.record, known, Option.isSome_some, List.length_cons, List.length_nil] using recordRelated.part (index := 6) rfl
    have refreshedReferences := ChildFrameCorrespondence.refresh_references
      ((references.prepend extra).prepend [recordValue]) afterLookup
    obtain ⟨target, final, invoked, resultRelated, finalRelated, frame⟩ :=
      ChildFrameCorrespondence.invoke_evaluates accepted eligible capturedFrame
        ((functionRelated.prepend extra).prepend [recordValue]) parent request initialShared freshWorld
        refreshedReferences signature stored separate observed
        ((creatorRelated.prepend extra).prepend [recordValue]) creatorRead creatorSeparate
        frameRelated gasRelated codeRelated sizeRelated knownRelated
        (sharedReferences.prepend [recordValue]) (related.linked.retained retained) evaluated responded
        (dispatcher := dispatcher)
    have selectedRun := RuntimeCatalogDispatchCorrespondence.runFrame_evaluates first recordRelated invoked
    refine ⟨target, final, ?_, resultRelated, finalRelated, (SharedFrame.ofRetains retained).trans frame⟩
    exact accountRun_child_evaluates sharedReferences
      ((argument.part (index := 0) rfl).part (index := 0) rfl) worldRead related.shared.complete
      ordinary actualFound nonzero selectedRun

/-- Actual object initialization supplies the closure packet, immutable lexical
references and captured dispatcher body used by the child theorem. -/
theorem captured_child_runs_preserves {sourceCatalog : ChildFrameSemantics.Catalog}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    (connection : CatalogConnection sourceCatalog catalog anchors)
    {fuel : Nat} {others : List Core.Expr}
    (compiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    {captured : Environment} {values : List Value} {closure : Value}
    (closures : CapturedClosures captured others values)
    {images : List (Nat × List UInt8)} {cells : List InitializedCell} {dispatcherLocation creatorLocation : Nat}
    {initial : Store}
    (capture : ObjectCallbackCapture (RuntimeExtendedInitializedEffects.slots true) (others.length + 1) images catalog
      (closure :: values) cells dispatcherLocation creatorLocation initial)
    {layout : Layout} (inventory : ChildCallbackContextCorrespondence.Inventory layout cells creatorLocation)
    (sharedReferences : SharedReferences capture.depth capture.environment capture.shared (sharedLocations layout))
    (parent : RuntimeCallEffectsSemantics.State)
    (ambient : ∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
      ContractEnvironmentCorrespondence.initializedValue parent.runtime.runtime.runtime.runtime.environment cell) :
    let dispatcher := ContractCallCorrespondence.captured_dispatcher capture (sharedLocations layout) sharedReferences
    ChildRunPreservation anchors (sharedLocations layout) dispatcher.shared dispatcher.runFrame
      (ChildFrameSemantics.CallFree sourceCatalog parent)
      (RuntimeChildCallEffectsCorrespondence.childReady layout (ChildCallbackContextCorrespondence.context inventory))
      dispatcher.depth dispatcher.captured :=
  child_runs_preserves connection compiled closures capture.functionValues inventory capture.references
    capture.creatorValue parent ambient

end Solcore.Frontend.RustHull.ChildCatalogExecutionCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractChildCallRuntimeFacts
/-! The public object's actual shared and frame allocations supply the static
inventory used by child callbacks. No callback resource assumption is added to
the public source theorem. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractChildCallCorrespondence
open Core Correspondence ScalarExecution ContractCallCorrespondence
open ChildCallbackContextCorrespondence
open RuntimeCallEffectsCorrespondence (Layout sharedLocations)

theorem shared_signature {context : CodeBuilder.Code} {cells : List InitializedCell} {values : List Value}
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip values).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse)
    (length : (AccountRuntime.sharedInitializers context).length ≤ values.length) :
    cells.map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse := by
  have typed := congrArg (List.map (fun entry : String × Core.Ty × Value => (entry.1, entry.2.1))) description
  simp only [List.map_reverse, List.map_map, Function.comp_def] at typed
  rw [typed]
  have firsts := List.map_fst_zip length
  have mapped := congrArg (List.map (fun entry : String × Core.Ty × CodeBuilder.Code => (entry.1, entry.2.1))) firsts
  simp only [List.map_map, Function.comp_def, sharedInitializers_types] at mapped
  exact congrArg List.reverse mapped

/-- The actual named frame references identify the five current shared
resources and every captured ambient cell. Bounds and separation come from the
same allocation, including the previously allocated creator cell. -/
theorem initialized_inventory {layout : Layout} {sharedCells cells : List InitializedCell}
    {initial store : Store} {creator : Nat} {withCode : Bool}
    (sharedSignature : sharedCells.map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse)
    (signature : cells.map (fun cell => (cell.name, cell.type)) = RuntimeExtendedInitializedEffects.slots withCode)
    (stored : InitializedCells cells store) (separate : CellLocations cells)
    (boundary : layout.boundary = store.length)
    (members : ∀ slot ∈ RuntimeCallInitializedEffects.baseSlots layout.toReturnDataLayout,
      slot ∈ cells.map InitializedCell.effectSlot)
    (origin : ∀ cell ∈ cells, Origin sharedCells initial.length cell)
    (creatorAfter : ∀ cell ∈ sharedCells, cell.location < creator)
    (creatorBefore : creator < initial.length) (retainedLength : initial.length ≤ store.length) :
    Inventory layout sharedCells creator ∧
      (∀ cell ∈ sharedCells, cell.effectSlot ∈ cells.map InitializedCell.effectSlot) := by
  have included := shared_included sharedSignature signature origin
  have shared : SharedCells sharedCells (sharedLocations layout) :=
    RuntimeCallInitializedEffects.shared_cells members (fun cell member named => (origin cell member).1 (by
      simp only [dispatchSharedNames, List.mem_cons, List.not_mem_nil, or_false] at named
      rcases named with named | named | named | named | named
      all_goals simp [named, sharedSlotTypes]))
  refine ⟨⟨sharedSignature, shared, separate.subset included, ?_, ?_, ?_,
    ambient_outside included separate members, creator_outside creatorBefore creatorAfter origin members⟩,
    fun cell member => List.mem_map_of_mem (included cell member)⟩
  · intro cell member
    rw [boundary]
    exact stored.location_bound (included cell member)
  · rw [boundary]
    exact Nat.lt_of_lt_of_le creatorBefore retainedLength
  · exact fun cell member => Nat.ne_of_lt (creatorAfter cell member)

/-- A callback's original captured reference expressions still denote the
same five runtime locations identified by the actual frame allocator. -/
theorem inventory_references {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    (inventory : Inventory layout cells creator)
    {depth : Nat} {environment : Environment} {shared : AccountRuntime.References}
    (references : RuntimeReferences depth environment shared cells) :
    AccountCallCorrespondence.SharedReferences depth environment shared (sharedLocations layout) :=
  inventory.shared.references inventory.unique references

/-- Context initialization follows the shared allocation's real contents and
the actual optional creator cell, even after subsequent frame allocations. -/
theorem initialized_context {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    (inventory : Inventory layout cells creator) {initial store : Store}
    (stored : InitializedCells cells initial) (creatorPresent : ∃ value, initial.read? creator = some value)
    (retained : StoreRetains initial store) :
    (ChildCallbackContextCorrespondence.context inventory).valid (prefixRead layout.boundary store) := by
  apply ChildCallbackContextCorrespondence.initial inventory (stored.retained retained)
  obtain ⟨value, found⟩ := creatorPresent
  exact ⟨value, (retained.read creator (List.getElem?_eq_some_iff.mp found).1).trans found⟩

end Solcore.Frontend.RustHull.ContractChildCallCorrespondence
end
