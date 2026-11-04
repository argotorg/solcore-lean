import Solcore.Frontend.RustHull.ContractStateTheorems
import Solcore.Frontend.RustHull.Internal.AccountLayers
import Solcore.Frontend.RustHull.Internal.RuntimeObjects

/-!
# Hull contract meaning preservation: code and return data

The public theorems for supplied code images and compiled catalogs, and for return data. Main
theorems: `ContractCodeCorrespondence.compileObject_resumes_exact`,
`ContractReturnDataCorrespondence.compileObject_resumes_exact`,
`ContractReturnDataCorrespondence.prepare_resumes_exact`.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractExtendedEnvironmentRuntimeFacts
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractExtendedRuntimeInitializationCorrespondence
/-! The actual frame initializer accepts the compiler's optional code slots,
code image and closure catalog. Shared resource observations remain independent
of those additional immutable inputs. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractRuntimeEffectsCorrespondence
open Correspondence ScalarExecution CodeBuilder

theorem shared_initializers_valid_extended {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {context : Code} {shared : AccountRuntime.References} {cells known : List InitializedCell}
    {accounts : StorageCorrespondence.Accounts} {address : Core.Word} {complete isStatic : Bool}
    {balances : StorageSemantics.Words} {ambient : List Core.Value} {worldLocation balancesLocation : Nat}
    {slots : List (String × Core.Ty)}
    (allowed : ∀ slot ∈ slots, slot ∈ Effects.slots ++ Effects.codeSlots)
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
    FrameSharedValid depth environment store slots shared
      (fun cell => initializedObservation accounts address complete isStatic balances worldLocation balancesLocation cell ∧ cell ∈ known) := by
  intro slot slotMember foundName reference found
  obtain ⟨cell, member, named, related⟩ := references.find found
  have typed := sharedSlotTypes_compatible (allowed slot slotMember)
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

theorem creator_initialized_valid_extended {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {creator : Code} {location : Nat} {value : Core.Value} {known : List InitializedCell}
    {slots : List (String × Core.Ty)}
    (allowed : ∀ slot ∈ slots, slot ∈ Effects.slots ++ Effects.codeSlots)
    (related : CodeValue depth environment creator (.cellRef (Core.OptionalCell.cellType Creation.callbackType) location))
    (stored : store.read? location = some value) (member : creatorCell location value ∈ known)
    (accounts : StorageCorrespondence.Accounts) (address : Core.Word) (complete isStatic : Bool)
    (balances : StorageSemantics.Words) (worldLocation balancesLocation : Nat) :
    FrameCreatorValid depth environment store slots creator
      (fun cell => initializedObservation accounts address complete isStatic balances worldLocation balancesLocation cell ∧ cell ∈ known) := by
  intro type present
  have typed : ∀ slot ∈ Effects.slots ++ Effects.codeSlots, slot.1 = "createHandler" → slot.2 = Core.OptionalCell.cellType Creation.callbackType := by decide
  cases typed ("createHandler", type) (allowed _ present) rfl
  refine ⟨creatorCell location value, rfl, rfl, related, stored, ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, member⟩⟩
  · intro expected impossible; cases impossible
  · intro name present named
    simp only [RuntimeEffectsFrameCorrespondence.passiveSnapshotNames, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl <;> simp [creatorCell] at named
  · intro impossible; simp [creatorCell] at impossible
  · intro impossible; simp [creatorCell] at impossible

/-- The extended initializer also identifies the create-handler slot: it is a
shared cell or the installed creator cell. -/
theorem objectFrame_initializes_creator
    {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {contextCode functions dispatcher creator : Code} {shared : AccountRuntime.References}
    {slots : List (String × Core.Ty)} {count : Nat}
    {images : List (Nat × List UInt8)} {codeBytes : Option (List UInt8)}
    (allowed : ∀ slot ∈ slots, slot ∈ Effects.slots ++ Effects.codeSlots)
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
      (constant (Core.WordMapping.literal (Memory.packBytes (codeBytes.getD []))))
      (number (codeBytes.getD []).length) (CodeBuilder.boolean codeBytes.isSome) shared property)
    (sharedExtra : ∀ cell ∈ sharedCells, property cell)
    (creatorExtra : ∀ value, initial.read? creatorLocation = some value → property (creatorCell creatorLocation value))
    (continued : ∀ extra suffix frameReferences cells worldLocation balancesLocation,
      CodeValues (depth + extra.length) (extra ++ environment) frameReferences (cells.map InitializedCell.reference) →
      InitializedCells cells (initial ++ suffix) →
      cells.map (fun cell => (cell.name, cell.type)) = slots →
      (∀ cell ∈ cells, initializedObservation
        (StorageCorrespondence.canonical (object.initialWorld context)) context.address context.completeWorld context.isStatic
        (Core.WordMapping.insertEntries context.address context.balance context.accounts) worldLocation balancesLocation cell ∧ property cell) →
      CellLocations cells →
      (∀ cell ∈ cells, cell.name = "createHandler" → cell ∈ sharedCells ∨ cell.location = creatorLocation) →
      CodeValue depth environment (AccountRuntime.reference shared "world") (.cellRef AccountState.type worldLocation) →
      CodeValue depth environment (AccountRuntime.reference shared "balances") (.cellRef Core.WordMapping.type balancesLocation) →
      initial.read? balancesLocation = some (Core.WordMapping.encode (Core.WordMapping.insertEntries context.address context.balance context.accounts)) →
      ∃ value final, Core.Evaluates (extra ++ environment) (initial ++ suffix)
        (bind (apply (part 0 count functions) (packet frameReferences))
          (fun framed => AccountRuntime.completeMessage shared images (part 4 12 contextCode) (part 11 12 contextCode) framed)
          (depth + extra.length)) value final ∧ observes value final) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectFrame slots count images codeBytes contextCode functions shared dispatcher creator depth)
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
      (constant (Core.WordMapping.literal (Memory.packBytes (codeBytes.getD []))))
      (number (codeBytes.getD []).length) (CodeBuilder.boolean codeBytes.isSome) shared
      (initializedObservation accounts context.address context.completeWorld context.isStatic balances worldLocation balancesLocation) :=
    fresh_initializers_observation (ContractMemoryCorrespondence.request_related object context contextRelated) rfl rfl rfl
      (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes (codeBytes.getD [])) depth environment)
      (CodeValue.number (codeBytes.getD []).length depth environment) (CodeValue.boolean codeBytes.isSome depth environment) references description'
  have sharedBase := shared_initializers_valid_extended (address := context.address) (isStatic := context.isStatic) (known := known) allowed references initialized
    (fun _ member => List.mem_append_left _ member) description' worldReference balancesReference
  have creatorBase := creator_initialized_valid_extended allowed creatorRelated creatorStored
    (show creatorCell creatorLocation creatorValue ∈ known from List.mem_append_right _ (.head _))
    accounts context.address context.completeWorld context.isStatic balances worldLocation balancesLocation
  have freshBoth := FrameInitializersValid.and fresh freshExtra
  have sharedReady : FrameSharedValid depth environment initial slots shared
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
  have creatorReady : FrameCreatorValid depth environment initial slots creator
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
  obtain ⟨extra, suffix, frameReferences, cells, referenceValues, stored, signature, observed, locations, creators, allocated⟩ :=
    allocateFrameSlots_creates freshBoth sharedReady creatorReady (previous := []) (previousCells := []) .nil
      (by intro cell member; cases member) (by intro cell member; cases member)
      (known_initialized initialized creatorStored)
      (by simpa only [List.append_nil] using known_separate separate creatorAfter (value := creatorValue))
  simp only [List.reverse_nil, List.nil_append] at referenceValues stored observed locations allocated
  have cellLocations : CellLocations cells := locations.subset (fun _ member => List.mem_append_right _ member)
  have creatorCells : ∀ cell ∈ cells, cell.name = "createHandler" → cell ∈ sharedCells ∨ cell.location = creatorLocation := by
    intro cell member named
    rcases List.mem_append.mp (creators cell member named) with shared | creatorMember
    · exact Or.inl shared
    · have same : cell = creatorCell creatorLocation creatorValue := by simpa using creatorMember
      exact Or.inr (by rw [same]; rfl)
  obtain ⟨value, final, evaluated, observedResult⟩ := continued extra suffix frameReferences cells worldLocation balancesLocation
    referenceValues stored signature observed cellLocations creatorCells worldReference balancesReference balancesFound
  exact ⟨value, final, allocated _ _ _ evaluated, observedResult⟩


theorem objectFrame_initializes_extended
    {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {contextCode functions dispatcher creator : Code} {shared : AccountRuntime.References}
    {slots : List (String × Core.Ty)} {count : Nat}
    {images : List (Nat × List UInt8)} {codeBytes : Option (List UInt8)}
    (allowed : ∀ slot ∈ slots, slot ∈ Effects.slots ++ Effects.codeSlots)
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
      (constant (Core.WordMapping.literal (Memory.packBytes (codeBytes.getD []))))
      (number (codeBytes.getD []).length) (CodeBuilder.boolean codeBytes.isSome) shared property)
    (sharedExtra : ∀ cell ∈ sharedCells, property cell)
    (creatorExtra : ∀ value, initial.read? creatorLocation = some value → property (creatorCell creatorLocation value))
    (continued : ∀ extra suffix frameReferences cells worldLocation balancesLocation,
      CodeValues (depth + extra.length) (extra ++ environment) frameReferences (cells.map InitializedCell.reference) →
      InitializedCells cells (initial ++ suffix) →
      cells.map (fun cell => (cell.name, cell.type)) = slots →
      (∀ cell ∈ cells, initializedObservation
        (StorageCorrespondence.canonical (object.initialWorld context)) context.address context.completeWorld context.isStatic
        (Core.WordMapping.insertEntries context.address context.balance context.accounts) worldLocation balancesLocation cell ∧ property cell) →
      CellLocations cells →
      CodeValue depth environment (AccountRuntime.reference shared "world") (.cellRef AccountState.type worldLocation) →
      CodeValue depth environment (AccountRuntime.reference shared "balances") (.cellRef Core.WordMapping.type balancesLocation) →
      initial.read? balancesLocation = some (Core.WordMapping.encode (Core.WordMapping.insertEntries context.address context.balance context.accounts)) →
      ∃ value final, Core.Evaluates (extra ++ environment) (initial ++ suffix)
        (bind (apply (part 0 count functions) (packet frameReferences))
          (fun framed => AccountRuntime.completeMessage shared images (part 4 12 contextCode) (part 11 12 contextCode) framed)
          (depth + extra.length)) value final ∧ observes value final) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectFrame slots count images codeBytes contextCode functions shared dispatcher creator depth)
      value final ∧ observes value final := by
  apply objectFrame_initializes_creator allowed object context contextRelated references initialized separate description
    creatorRelated creatorFound creatorAfter property observes freshExtra sharedExtra creatorExtra
  intro extra suffix frameReferences cells worldLocation balancesLocation referenceValues stored signature observed
    cellLocations _ worldReference balancesReference balancesFound
  exact continued extra suffix frameReferences cells worldLocation balancesLocation referenceValues stored signature
    observed cellLocations worldReference balancesReference balancesFound

end Solcore.Frontend.RustHull.ContractRuntimeEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractCodeRuntimeFacts
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractCodeInitializedExecution
/-! Actual public frame initialization supplies the linked code image and all
shared runtime observations before independent source execution begins. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractCodeCorrespondence
open Correspondence ScalarExecution CodeBuilder ContractRuntimeEffectsCorrespondence ContractEnvironmentCorrespondence

def contextInitialState (image : Option (List UInt8)) (object : Contract.CompiledObject)
    (context : Contract.Context) : RuntimeCodeEffectsSemantics.State :=
  let initial := ContractAccountCorrespondence.contextInitialState object context
  {initial with runtime := {initial.runtime with runtime :=
    {initial.runtime.runtime with environment := contextEnvironment context image}}}

private theorem known_observed {cells : List InitializedCell} {context : Contract.Context}
    {image : Option (List UInt8)}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots ++ Effects.codeSlots)
    (observed : ∀ cell ∈ cells, ContractEnvironmentCorrespondence.initializedValue (contextEnvironment context image) cell) :
    ∀ cell ∈ cells, cell.name = "codeKnown" → cell.value = .bool image.isSome := by
  intro cell member named
  have present : (cell.name, cell.type) ∈ Effects.slots ++ Effects.codeSlots := by
    rw [← signature]
    exact List.mem_map_of_mem member
  have types : ∀ slot ∈ Effects.slots ++ Effects.codeSlots,
      slot.1 = "codeKnown" → slot.2 = Core.Ty.bool := by decide
  have typed : cell.type = .bool := types _ present named
  apply observed cell member
  simp only [EnvironmentBuiltinCorrespondence.observation, named, typed, contextEnvironment]

theorem objectFrame_evaluates {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (Effects.slots ++ Effects.codeSlots) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment captured : Core.Environment} {initial : Core.Store}
    {contextCode functions dispatcher creator : Code} {count : Nat}
    {images : List (Nat × List UInt8)} {image : Option (List UInt8)} {shared : AccountRuntime.References}
    {closure : Core.Value} (closureRelated : CapturedClosure compiled captured closure)
    (functionsRelated : CodeValue depth environment (part 0 count functions) closure)
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
    {finalSource : Semantics.State RuntimeCodeEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCodeEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectFrame (Effects.slots ++ Effects.codeSlots) count images image contextCode functions shared dispatcher creator depth)
      value final ∧ MessageRel sourceResult finalSource.external context.address value := by
  let accounts := StorageCorrespondence.canonical (object.initialWorld context)
  let balances := Core.WordMapping.insertEntries context.address context.balance context.accounts
  have description' : sharedCells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip
        (ContractMemoryCorrespondence.sharedValues accounts context.completeWorld balances (ambientValues context.ambient))).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse := description
  have fresh : FrameInitializersValid depth environment initial
      (ContractMemoryCorrespondence.requestCode contextCode) dispatcher (part 5 12 contextCode)
      (constant (Core.WordMapping.literal (Memory.packBytes (image.getD []))))
      (number (image.getD []).length) (CodeBuilder.boolean image.isSome) shared
      (ContractEnvironmentCorrespondence.initializedValue (contextEnvironment context image)) :=
    ContractEnvironmentCorrespondence.fresh_initializers_observation_image context image (ContractMemoryCorrespondence.request_related object context contextRelated)
      (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes (image.getD [])) depth environment)
      (CodeValue.number (image.getD []).length depth environment) (CodeValue.boolean image.isSome depth environment) references description'
  have freshCode := fresh_code_observation (store := initial) (dispatcher := dispatcher) (shared := shared) image
    (ContractMemoryCorrespondence.request_related object context contextRelated) rfl
    (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes (image.getD [])) depth environment)
    (CodeValue.number (image.getD []).length depth environment) (CodeValue.boolean image.isSome depth environment)
  apply ContractRuntimeEffectsCorrespondence.objectFrame_initializes_extended (fun _ member => member) object context contextRelated references initialized separate
    description creatorRelated creatorFound creatorAfter
    (fun cell => ContractEnvironmentCorrespondence.initializedValue (contextEnvironment context image) cell ∧ initializedCode image cell)
    (fun value _ => MessageRel sourceResult finalSource.external context.address value)
    (FrameInitializersValid.and fresh freshCode)
    (fun cell member => ⟨ContractEnvironmentCorrespondence.shared_initialized_value context image description' cell member,
      shared_code_observation image description' cell member⟩)
    (by
      intro value _
      constructor
      · intro _ impossible
        cases impossible
      · exact creator_code_observation image creatorLocation value)
  intro extra suffix frameReferences cells worldLocation balancesLocation referenceValues stored signature observations cellLocations
    worldReference balancesReference balancesFound
  have observed := fun cell member => (observations cell member).1
  have environmentObserved := fun cell member => (observations cell member).2.1
  have codeObserved := fun cell member => (observations cell member).2.2
  have knownObserved := known_observed signature environmentObserved
  obtain ⟨ready, logReady, accountReady⟩ := RuntimeExtendedInitializedEffects.ready signature stored cellLocations
    (fun cell member => (observed cell member).1.1) rfl
    (words := []) (cursor := Core.Word.zero) (balances := balances)
    (fun cell member named => (observed cell member).1.2 "logs" (by decide) named)
    (fun cell member named => (observed cell member).1.2 "logSize" (by decide) named)
    (fun cell member named => (observed cell member).1.2 "balances" (by decide) named)
  obtain ⟨accountReady⟩ := accountReady
  obtain ⟨codeReady⟩ := RuntimeCodeInitializedEffects.ready signature stored cellLocations accountReady
    (image := image) codeObserved knownObserved
  have memoryLocation : codeReady.layout.memory = ready.memory := by
    change codeReady.layout.toAccountLayout.memory = ready.memory
    rw [codeReady.base]
    exact
    (congrArg (fun layout : RuntimeLogEffectsCorrespondence.Layout => layout.memory) accountReady.base).trans
      (congrArg RuntimeEffectsCorrespondence.Layout.memory logReady.base)
  have storageLocations : codeReady.layout.storage = ready.locations := by
    change codeReady.layout.toAccountLayout.storage = ready.locations
    rw [codeReady.base]
    exact
    (congrArg (fun layout : RuntimeLogEffectsCorrespondence.Layout => layout.storage) accountReady.base).trans
      (congrArg RuntimeEffectsCorrespondence.Layout.storage logReady.base)
  have boundary : codeReady.layout.boundary = (initial ++ suffix).length := by
    change codeReady.layout.toAccountLayout.boundary = (initial ++ suffix).length
    rw [codeReady.base]
    exact
    (congrArg (fun layout : RuntimeLogEffectsCorrespondence.Layout => layout.boundary) accountReady.base).trans
      (congrArg RuntimeEffectsCorrespondence.Layout.boundary logReady.base)
  let slots := cells.map InitializedCell.effectSlot
  have slotTypes : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots ++ Effects.codeSlots := by
    simpa only [RuntimeEffectsFrameCorrespondence.slotTypes, MemoryFrameCorrespondence.slotTypes,
      slots, List.map_map, Function.comp_def, InitializedCell.effectSlot] using signature
  have environmentRelated := initialized_environment cells (RuntimeExtendedInitializedEffects.initialized_unique (withCode := true) signature)
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
  have balanceSame : codeReady.layout.balances = balancesLocation := by
    change codeReady.layout.toAccountLayout.balances = balancesLocation
    rw [codeReady.base]
    obtain ⟨cell, member, same⟩ := List.mem_map.mp accountReady.balancesMember
    have named := congrArg EffectSlot.name same
    have atLocation := congrArg EffectSlot.location same
    exact atLocation.symm.trans ((observed cell member).2.2 named)
  have environmentInitial := initialized_related stored environmentObserved
  have initialRelated : StateRel (RuntimeCodeEffectsCorrespondence.model codeReady.layout
      (prefixRead codeReady.layout.boundary (initial ++ suffix)) slots image) []
      ⟨[], contextInitialState image object context⟩ (initial ++ suffix) := by
    apply RuntimeCodeEffectsCorrespondence.initial_state
    · rw [codeReady.base]
      apply RuntimeAccountEffectsCorrespondence.initial_state
      · rw [accountReady.base]
        apply RuntimeLogEffectsCorrespondence.initial_state
        · simpa only [logReady.base, RuntimeEffectsCorrespondence.initialLayout] using
            RuntimeEnvironmentEffectsCorrespondence.initial_state ready.memoryRelated ready.storageRelated ready.distinct environmentInitial
        · exact logReady.logsRead
        · exact logReady.logSizeRead
      · exact accountReady.balancesRead
    · exact codeReady.readCode
    · exact codeReady.readKnown
  have passiveEnvironment : RuntimeLogEffectsCorrespondence.Passive codeReady.layout.toLogLayout slots := by
    apply RuntimeLogEffectsCorrespondence.Passive.of_names
      (memoryMember := by simpa only [memoryLocation] using ready.memoryMember)
      (worldMember := by simpa only [storageLocations] using ready.worldMember)
      (memorySizeMember := by simpa only [storageLocations] using ready.sizeMember)
      (exitMember := by simpa only [storageLocations] using ready.exitMember)
      (offsetMember := by simpa only [storageLocations] using ready.offsetMember)
      (sizeMember := by simpa only [storageLocations] using ready.returnSizeMember)
      (logsMember := by simpa only [codeReady.base, accountReady.base] using logReady.logsMember) (logSizeMember := by simpa only [codeReady.base, accountReady.base] using logReady.logSizeMember)
    intro first firstMember second secondMember same
    obtain ⟨left, leftMember, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨right, rightMember, rfl⟩ := List.mem_map.mp secondMember
    exact cellLocations left leftMember right rightMember same
  obtain ⟨value, final, completed, resultRelated⟩ := frameCall_message_evaluates
    (by simpa only [slotTypes] using accepted)
    (by simpa only [supported_actual slotTypes] using eligible) closureRelated
    ((functionsRelated.prepend extra).evaluates (initial ++ suffix))
    ((CodeValue.packet referenceValues).evaluates (initial ++ suffix))
    (by simp [slots]) runtime (RuntimeExtendedInitializedEffects.initialized_separate (withCode := true) signature)
    (by simpa only [memoryLocation] using ready.memoryMember)
    (by simpa only [storageLocations] using ready.worldMember)
    (by simpa only [storageLocations] using ready.addressMember)
    (by simpa only [storageLocations] using ready.completeMember)
    (by simpa only [storageLocations] using ready.staticMember)
    (by simpa only [storageLocations] using ready.sizeMember)
    (by simpa only [storageLocations] using ready.exitMember)
    (by simpa only [storageLocations] using ready.offsetMember)
    (by simpa only [storageLocations] using ready.returnSizeMember)
    (by simpa only [codeReady.base, accountReady.base] using logReady.logsMember)
    (by simpa only [codeReady.base, accountReady.base] using logReady.logSizeMember)
    (by simpa only [codeReady.base] using accountReady.balancesMember) codeReady.codeMember codeReady.knownMember initialRelated passiveEnvironment evaluated context.address
    (by simpa only [storageLocations, worldSame] using worldReference.prepend extra) (by simpa only [balanceSame] using balancesReference.prepend extra)
    ((contextRelated.part (index := 4) rfl).prepend extra)
    (by simpa only [notDeploying] using (contextRelated.part (index := 11) rfl).prepend extra)
  exact ⟨value, final, completed, resultRelated⟩

end Solcore.Frontend.RustHull.ContractCodeCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractCodeExecutionCorrespondence
/-! Supplied code images and compiled catalogs reach the public contract
runner through actual compilation, closure capture and initialization. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractCodeCorrespondence
open Correspondence ScalarExecution CodeBuilder ContractRuntimeEffectsCorrespondence

theorem objectRuntime_preserves {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {others : List Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (Effects.slots ++ Effects.codeSlots) fuel = .ok compiled)
    (catalogCompiled : ContractCatalogCorrespondence.CompiledCatalog (Effects.slots ++ Effects.codeSlots) fuel catalog others)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment : Core.Environment} {initial : Core.Store} {contextCode : Code}
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    {finalSource : Semantics.State RuntimeCodeEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCodeEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime (Effects.slots ++ Effects.codeSlots) compiled others
        (ContractCatalogCorrespondence.images image catalog) image catalog contextCode depth) value final ∧
      MessageRel sourceResult finalSource.external context.address value := by
  obtain ⟨closure, captured⟩ := compileFrame_captures accepted environment
  obtain ⟨values, captures⟩ := catalogCompiled.captures environment
  apply objectRuntime_evaluates_separated
    (fun value _ => MessageRel sourceResult finalSource.external context.address value)
    (.cons captured captures) (ContractMemoryCorrespondence.sharedValues_related object context contextRelated)
  intro functions shared dispatcher creator extra allocated cells _ creatorLocation functionsRelated references initialized separate description _ _ creatorRelated creatorFound creatorAfter
  have entry := ContractCatalogCorrespondence.entry_reference captures functionsRelated
  exact objectFrame_evaluates accepted eligible captured entry object context notDeploying
    (contextRelated.prepend extra) references initialized separate description creatorRelated creatorFound creatorAfter evaluated

def PublicMessageRel (context : Contract.Context) (result : Semantics.Result Semantics.Value)
    (state : RuntimeCodeEffectsSemantics.State) (value : Core.Value) : Prop :=
  MessageRel result state (Contract.normalizeContext context).address value

/-- The actual compiler supplies every catalog closure. The independent entry
evaluation determines the result, including code availability and copy faults. -/
theorem compileObject_preserves {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {object : Contract.CompiledObject}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel image catalog = .ok object)
    (hasCode : (image.isSome || !catalog.isEmpty) = true)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (context : Contract.Context) (notDeploying : context.deploying = false)
    {finalSource : Semantics.State RuntimeCodeEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCodeEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates [] [] (object.instantiate context).expression value final ∧
      PublicMessageRel context sourceResult finalSource.external value := by
  have compiled : AccountRuntime.compileObject program path fuel image catalog = .ok object.expression := by
    unfold Contract.compileObject at accepted
    obtain ⟨expression, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
    cases returned
    exact compiled
  obtain ⟨frame, others, frameCompiled, catalogCompiled, objectExpression⟩ :=
    ContractCatalogCorrespondence.compileObject_selected selected compiled
  have signature : ContractCatalogCorrespondence.slots image catalog = Effects.slots ++ Effects.codeSlots := by
    simp only [ContractCatalogCorrespondence.slots, hasCode, ↓reduceIte]
  rw [signature] at frameCompiled catalogCompiled objectExpression
  have normalized : (Contract.normalizeContext context).deploying = false := notDeploying
  obtain ⟨value, final, executed, related⟩ := objectRuntime_preserves frameCompiled
    (ContractCatalogCorrespondence.compiledCatalog catalogCompiled) eligible object
    (Contract.normalizeContext context) normalized
    (CodeValue.bound 0 [] (bundleValues (contextValues object (Contract.normalizeContext context)))) evaluated
  refine ⟨value, final, instantiate_evaluates context (parameter := AccountRuntime.contextType)
    (resultType := AccountRuntime.resultType) ?_ executed, related⟩
  rw [objectExpression]
  rfl

/-- Every genuine public resumption chain reaches the independently derived
message exactly when its cumulative fuel covers the required transitions. -/
theorem compileObject_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {object : Contract.CompiledObject}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel image catalog = .ok object)
    (hasCode : (image.isSome || !catalog.isEmpty) = true)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (context : Contract.Context) (notDeploying : context.deploying = false)
    {finalSource : Semantics.State RuntimeCodeEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCodeEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value, PublicMessageRel context sourceResult finalSource.external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨value, _, executed, related⟩ :=
    compileObject_preserves selected accepted hasCode eligible context notDeploying evaluated
  exact ⟨value, related, Contract.evaluation_resumes_exact executed⟩

end Solcore.Frontend.RustHull.ContractCodeCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractReturnDataRuntimeFacts
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeReturnDataInitializedEffects
/-! The real frame cells establish return-data resources with or without code
slots. The account layout is retained, and optional code cells come from the
existing code initializer proof. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeReturnDataInitializedEffects
open Correspondence ScalarExecution RuntimeInitializedEffects

structure Ready {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {runtime : StateReady cells store state}
    {words : LogsSemantics.Words} {cursor : Core.Word} {logs : RuntimeLogInitializedEffects.Ready runtime words cursor}
    {balances : StorageSemantics.Words} (accounts : RuntimeAccountInitializedEffects.Ready logs balances)
    (withCode : Bool) (image : Option (List UInt8)) (data : MemorySemantics.Entries) (size : Core.Word) where
  layout : RuntimeReturnDataEffectsCorrespondence.Layout
  base : layout.toAccountLayout = accounts.layout
  mode : layout.codeCells.isSome = withCode
  dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ cells.map InitializedCell.effectSlot
  dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ cells.map InitializedCell.effectSlot
  readData : store.read? layout.returnData = some (Core.WordMapping.encode data)
  readSize : store.read? layout.returnDataSize = some (.word size)
  codeMembers : ∀ code, layout.codeCells = some code →
    ⟨"code", Core.WordMapping.type, code.code⟩ ∈ cells.map InitializedCell.effectSlot ∧
    ⟨"codeKnown", .bool, code.known⟩ ∈ cells.map InitializedCell.effectSlot
  readCode : ∀ code, layout.codeCells = some code →
    store.read? code.code = some (Core.WordMapping.encode (Memory.packBytes (image.getD []))) ∧
    store.read? code.known = some (.bool image.isSome)

private theorem optional_code {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {runtime : StateReady cells store state}
    {words : LogsSemantics.Words} {cursor : Core.Word} {logs : RuntimeLogInitializedEffects.Ready runtime words cursor}
    {balances : StorageSemantics.Words} {withCode : Bool} {image : Option (List UInt8)}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = RuntimeExtendedInitializedEffects.slots withCode)
    (initialized : InitializedCells cells store) (separate : CellLocations cells)
    (accounts : RuntimeAccountInitializedEffects.Ready logs balances)
    (codeObserved : withCode = true → ∀ cell ∈ cells, cell.name = "code" →
      cell.value = Core.WordMapping.encode (Memory.packBytes (image.getD [])))
    (knownObserved : withCode = true → ∀ cell ∈ cells, cell.name = "codeKnown" → cell.value = .bool image.isSome) :
    ∃ codeCells : Option (RuntimeReturnDataEffectsCorrespondence.CodeCells accounts.layout),
      codeCells.isSome = withCode ∧ ∀ code, codeCells = some code →
        (⟨"code", Core.WordMapping.type, code.code⟩ ∈ cells.map InitializedCell.effectSlot ∧
          ⟨"codeKnown", .bool, code.known⟩ ∈ cells.map InitializedCell.effectSlot) ∧
        (store.read? code.code = some (Core.WordMapping.encode (Memory.packBytes (image.getD []))) ∧
          store.read? code.known = some (.bool image.isSome)) := by
  cases withCode with
  | false => exact ⟨none, rfl, by intro _ impossible; cases impossible⟩
  | true =>
      obtain ⟨ready⟩ := RuntimeCodeInitializedEffects.ready signature initialized separate accounts
        (codeObserved rfl) (knownObserved rfl)
      let code : RuntimeReturnDataEffectsCorrespondence.CodeCells accounts.layout := {
        code := ready.layout.code
        known := ready.layout.known
        codeBelow := by simpa only [ready.base] using ready.layout.codeBelow
        knownBelow := by simpa only [ready.base] using ready.layout.knownBelow
        codeOutside := by simpa only [ready.base] using ready.layout.codeOutside
        knownOutside := by simpa only [ready.base] using ready.layout.knownOutside }
      refine ⟨some code, rfl, ?_⟩
      intro actual same
      cases Option.some.inj same
      exact ⟨⟨ready.codeMember, ready.knownMember⟩, ready.readCode, ready.readKnown⟩

private theorem cell_outside {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {runtime : StateReady cells store state}
    {words : LogsSemantics.Words} {cursor : Core.Word} (logs : RuntimeLogInitializedEffects.Ready runtime words cursor)
    (separate : CellLocations cells) {cell : InitializedCell} (member : cell ∈ cells)
    (outside : cell.name ∉ ["logs", "logSize", "memory", "memorySize", "world", "exit", "returnOffset", "returnSize"]) :
    cell.location ∉ RuntimeLogEffectsCorrespondence.mutable logs.layout := by
  intro inside
  change cell.location ∈ logs.layout.logs :: logs.layout.logSize ::
    RuntimeEffectsCorrespondence.mutable logs.layout.toLayout at inside
  rcases List.mem_cons.mp inside with same | inside
  · exact cell_location_ne separate member logs.logsMember (fun named => outside (by simp [named])) same
  rcases List.mem_cons.mp inside with same | inside
  · exact cell_location_ne separate member logs.logSizeMember (fun named => outside (by simp [named])) same
  rw [logs.base] at inside
  simp only [RuntimeEffectsCorrespondence.mutable, RuntimeEffectsCorrespondence.initialLayout,
    StorageBuiltinCorrespondence.Locations.mutable, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at inside
  rcases inside with (same | same) | same | same | same | same
  · exact cell_location_ne separate member runtime.memoryMember (fun named => outside (by simp [named])) same
  · exact cell_location_ne separate member runtime.sizeMember (fun named => outside (by simp [named])) same
  · exact cell_location_ne separate member runtime.worldMember (fun named => outside (by simp [named])) same
  · exact cell_location_ne separate member runtime.exitMember (fun named => outside (by simp [named])) same
  · exact cell_location_ne separate member runtime.offsetMember (fun named => outside (by simp [named])) same
  · exact cell_location_ne separate member runtime.returnSizeMember (fun named => outside (by simp [named])) same

/-- Initialization supplies both caller cells and optional image cells. All
bounds and separation facts follow from the actual named allocation. -/
theorem ready {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {runtime : StateReady cells store state}
    {words : LogsSemantics.Words} {cursor : Core.Word} {logs : RuntimeLogInitializedEffects.Ready runtime words cursor}
    {balances : StorageSemantics.Words} {withCode : Bool} {image : Option (List UInt8)}
    {data : MemorySemantics.Entries} {size : Core.Word}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = RuntimeExtendedInitializedEffects.slots withCode)
    (initialized : InitializedCells cells store) (separate : CellLocations cells)
    (accounts : RuntimeAccountInitializedEffects.Ready logs balances)
    (dataObserved : ∀ cell ∈ cells, cell.name = "returnData" → cell.value = Core.WordMapping.encode data)
    (sizeObserved : ∀ cell ∈ cells, cell.name = "returnDataSize" → cell.type = .word → cell.value = .word size)
    (codeObserved : withCode = true → ∀ cell ∈ cells, cell.name = "code" →
      cell.value = Core.WordMapping.encode (Memory.packBytes (image.getD [])))
    (knownObserved : withCode = true → ∀ cell ∈ cells, cell.name = "codeKnown" → cell.value = .bool image.isSome) :
    Nonempty (Ready accounts withCode image data size) := by
  obtain ⟨dataCell⟩ := ContractReturnDataCorrespondence.observe_base signature initialized
    (name := "returnData") (type := Core.WordMapping.type) (by simp [Effects.slots])
    (fun cell member named _ => dataObserved cell member named)
  obtain ⟨sizeCell⟩ := ContractReturnDataCorrespondence.observe_base signature initialized
    (name := "returnDataSize") (type := .word) (by simp [Effects.slots]) sizeObserved
  obtain ⟨codeCells, mode, codes⟩ := optional_code signature initialized separate accounts codeObserved knownObserved
  have boundary : accounts.layout.boundary = store.length := by
    change accounts.layout.toLogLayout.toLayout.boundary = store.length
    rw [accounts.base, logs.base]
    rfl
  let layout : RuntimeReturnDataEffectsCorrespondence.Layout := {
    toAccountLayout := accounts.layout
    codeCells := codeCells
    returnData := dataCell.cell.location
    returnDataSize := sizeCell.cell.location
    dataBelow := by rw [boundary]; exact initialized.location_bound dataCell.member
    sizeBelow := by rw [boundary]; exact initialized.location_bound sizeCell.member
    dataOutside := by
      change dataCell.cell.location ∉ RuntimeLogEffectsCorrespondence.mutable accounts.layout.toLogLayout
      rw [accounts.base]
      exact cell_outside logs separate dataCell.member (by rw [dataCell.named]; decide)
    sizeOutside := by
      change sizeCell.cell.location ∉ RuntimeLogEffectsCorrespondence.mutable accounts.layout.toLogLayout
      rw [accounts.base]
      exact cell_outside logs separate sizeCell.member (by rw [sizeCell.named]; decide)
    dataDistinct := ContractReturnDataCorrespondence.cells_distinct separate dataCell sizeCell }
  exact ⟨layout, rfl, mode, dataCell.slot, sizeCell.slot, dataCell.stored, sizeCell.stored,
    fun code present => (codes code present).1, fun code present => (codes code present).2⟩

end Solcore.Frontend.RustHull.RuntimeReturnDataInitializedEffects
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractReturnDataInitializedExecution
/-! Actual frame initialization supplies empty caller return data and optional
code cells before independent source execution reaches message completion. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractReturnDataCorrespondence
open Correspondence ScalarExecution CodeBuilder ContractRuntimeEffectsCorrespondence ContractEnvironmentCorrespondence

def contextInitialState (image : Option (List UInt8)) (object : Contract.CompiledObject)
    (context : Contract.Context) : RuntimeReturnDataEffectsSemantics.State :=
  ⟨ContractCodeCorrespondence.contextInitialState image object context, []⟩

private theorem known_observed {cells : List InitializedCell} {context : Contract.Context}
    {image : Option (List UInt8)} {withCode : Bool}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = RuntimeExtendedInitializedEffects.slots withCode)
    (observed : ∀ cell ∈ cells, ContractEnvironmentCorrespondence.initializedValue (contextEnvironment context image) cell) :
    ∀ cell ∈ cells, cell.name = "codeKnown" → cell.value = .bool image.isSome := by
  intro cell member named
  have present : (cell.name, cell.type) ∈ Effects.slots ++ Effects.codeSlots := by
    apply RuntimeExtendedInitializedEffects.slots_allowed withCode
    rw [← signature]
    exact List.mem_map_of_mem member
  have types : ∀ slot ∈ Effects.slots ++ Effects.codeSlots,
      slot.1 = "codeKnown" → slot.2 = Core.Ty.bool := by decide
  have typed : cell.type = .bool := types _ present named
  apply observed cell member
  simp only [EnvironmentBuiltinCorrespondence.observation, named, typed, contextEnvironment]

theorem objectFrame_evaluates {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (RuntimeExtendedInitializedEffects.slots withCode) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment captured : Core.Environment} {initial : Core.Store}
    {contextCode functions dispatcher creator : Code} {count : Nat}
    {images : List (Nat × List UInt8)} {image : Option (List UInt8)} {shared : AccountRuntime.References}
    {closure : Core.Value} (closureRelated : CapturedClosure compiled captured closure)
    (functionsRelated : CodeValue depth environment (part 0 count functions) closure)
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
    {finalSource : Semantics.State RuntimeReturnDataEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeReturnDataEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectFrame (RuntimeExtendedInitializedEffects.slots withCode) count images image contextCode functions shared dispatcher creator depth)
      value final ∧ MessageRel sourceResult finalSource.external context.address value := by
  let accounts := StorageCorrespondence.canonical (object.initialWorld context)
  let balances := Core.WordMapping.insertEntries context.address context.balance context.accounts
  have description' : sharedCells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers contextCode).zip
        (ContractMemoryCorrespondence.sharedValues accounts context.completeWorld balances (ambientValues context.ambient))).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse := description
  have fresh : FrameInitializersValid depth environment initial
      (ContractMemoryCorrespondence.requestCode contextCode) dispatcher (part 5 12 contextCode)
      (constant (Core.WordMapping.literal (Memory.packBytes (image.getD []))))
      (number (image.getD []).length) (CodeBuilder.boolean image.isSome) shared
      (ContractEnvironmentCorrespondence.initializedValue (contextEnvironment context image)) :=
    ContractEnvironmentCorrespondence.fresh_initializers_observation_image context image (ContractMemoryCorrespondence.request_related object context contextRelated)
      (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes (image.getD [])) depth environment)
      (CodeValue.number (image.getD []).length depth environment) (CodeValue.boolean image.isSome depth environment) references description'
  have freshCode := ContractCodeCorrespondence.fresh_code_observation (store := initial) (dispatcher := dispatcher) (shared := shared) image
    (ContractMemoryCorrespondence.request_related object context contextRelated) rfl
    (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes (image.getD [])) depth environment)
    (CodeValue.number (image.getD []).length depth environment) (CodeValue.boolean image.isSome depth environment)
  have freshData := fresh_returnData_observation (store := initial) (dispatcher := dispatcher) (shared := shared)
    (ContractMemoryCorrespondence.request_related object context contextRelated) rfl
    (contextRelated.part (index := 5) rfl) (CodeValue.mapping (Memory.packBytes (image.getD [])) depth environment)
    (CodeValue.number (image.getD []).length depth environment) (CodeValue.boolean image.isSome depth environment)
  apply ContractRuntimeEffectsCorrespondence.objectFrame_initializes_extended (fun _ member => RuntimeExtendedInitializedEffects.slots_allowed withCode member) object context contextRelated references initialized separate
    description creatorRelated creatorFound creatorAfter
    (fun cell => ContractEnvironmentCorrespondence.initializedValue (contextEnvironment context image) cell ∧ ContractCodeCorrespondence.initializedCode image cell ∧ initializedReturnData cell)
    (fun value _ => MessageRel sourceResult finalSource.external context.address value)
    (FrameInitializersValid.and fresh (FrameInitializersValid.and freshCode freshData))
    (fun cell member => ⟨ContractEnvironmentCorrespondence.shared_initialized_value context image description' cell member,
      ContractCodeCorrespondence.shared_code_observation image description' cell member,
      shared_returnData_observation description' cell member⟩)
    (by
      intro value _
      constructor
      · intro _ impossible
        cases impossible
      · exact ⟨ContractCodeCorrespondence.creator_code_observation image creatorLocation value,
          creator_returnData_observation creatorLocation value⟩)
  intro extra suffix frameReferences cells worldLocation balancesLocation referenceValues stored signature observations cellLocations
    worldReference balancesReference balancesFound
  have observed := fun cell member => (observations cell member).1
  have environmentObserved := fun cell member => (observations cell member).2.1
  have codeObserved := fun cell member => (observations cell member).2.2.1
  have dataObserved := fun cell member => (observations cell member).2.2.2
  have knownObserved := known_observed signature environmentObserved
  obtain ⟨ready, logReady, accountReady⟩ := RuntimeExtendedInitializedEffects.ready signature stored cellLocations
    (fun cell member => (observed cell member).1.1) rfl
    (words := []) (cursor := Core.Word.zero) (balances := balances)
    (fun cell member named => (observed cell member).1.2 "logs" (by decide) named)
    (fun cell member named => (observed cell member).1.2 "logSize" (by decide) named)
    (fun cell member named => (observed cell member).1.2 "balances" (by decide) named)
  obtain ⟨accountReady⟩ := accountReady
  obtain ⟨codeReady⟩ := RuntimeReturnDataInitializedEffects.ready signature stored cellLocations accountReady
    (image := image) dataObserved
    (fun cell member named typed => initialized_returnDataSize (environmentObserved cell member) named typed)
    (fun _ => codeObserved) (fun _ => knownObserved)
  have memoryLocation : codeReady.layout.memory = ready.memory := by
    change codeReady.layout.toAccountLayout.memory = ready.memory
    rw [codeReady.base]
    exact
    (congrArg (fun layout : RuntimeLogEffectsCorrespondence.Layout => layout.memory) accountReady.base).trans
      (congrArg RuntimeEffectsCorrespondence.Layout.memory logReady.base)
  have storageLocations : codeReady.layout.storage = ready.locations := by
    change codeReady.layout.toAccountLayout.storage = ready.locations
    rw [codeReady.base]
    exact
    (congrArg (fun layout : RuntimeLogEffectsCorrespondence.Layout => layout.storage) accountReady.base).trans
      (congrArg RuntimeEffectsCorrespondence.Layout.storage logReady.base)
  have boundary : codeReady.layout.boundary = (initial ++ suffix).length := by
    change codeReady.layout.toAccountLayout.boundary = (initial ++ suffix).length
    rw [codeReady.base]
    exact
    (congrArg (fun layout : RuntimeLogEffectsCorrespondence.Layout => layout.boundary) accountReady.base).trans
      (congrArg RuntimeEffectsCorrespondence.Layout.boundary logReady.base)
  let slots := cells.map InitializedCell.effectSlot
  have slotTypes : RuntimeEffectsFrameCorrespondence.slotTypes slots = RuntimeExtendedInitializedEffects.slots withCode := by
    simpa only [RuntimeEffectsFrameCorrespondence.slotTypes, MemoryFrameCorrespondence.slotTypes,
      slots, List.map_map, Function.comp_def, InitializedCell.effectSlot] using signature
  have environmentRelated := initialized_environment cells (RuntimeExtendedInitializedEffects.initialized_unique (withCode := withCode) signature)
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
  have balanceSame : codeReady.layout.balances = balancesLocation := by
    change codeReady.layout.toAccountLayout.balances = balancesLocation
    rw [codeReady.base]
    obtain ⟨cell, member, same⟩ := List.mem_map.mp accountReady.balancesMember
    have named := congrArg EffectSlot.name same
    have atLocation := congrArg EffectSlot.location same
    exact atLocation.symm.trans ((observed cell member).2.2 named)
  have environmentInitial := initialized_related stored environmentObserved
  have initialRelated : StateRel (RuntimeReturnDataEffectsCorrespondence.model codeReady.layout
      (prefixRead codeReady.layout.boundary (initial ++ suffix)) slots image) []
      ⟨[], contextInitialState image object context⟩ (initial ++ suffix) := by
    apply RuntimeReturnDataEffectsCorrespondence.initial_state
    · rw [codeReady.base]
      apply RuntimeAccountEffectsCorrespondence.initial_state
      · rw [accountReady.base]
        apply RuntimeLogEffectsCorrespondence.initial_state
        · simpa only [logReady.base, RuntimeEffectsCorrespondence.initialLayout] using
            RuntimeEnvironmentEffectsCorrespondence.initial_state ready.memoryRelated ready.storageRelated ready.distinct environmentInitial
        · exact logReady.logsRead
        · exact logReady.logSizeRead
      · exact accountReady.balancesRead
    · exact codeReady.readData
    · exact codeReady.readSize
    · exact codeReady.readCode
  have passiveEnvironment : RuntimeLogEffectsCorrespondence.Passive codeReady.layout.toLogLayout slots := by
    apply RuntimeLogEffectsCorrespondence.Passive.of_names
      (memoryMember := by simpa only [memoryLocation] using ready.memoryMember)
      (worldMember := by simpa only [storageLocations] using ready.worldMember)
      (memorySizeMember := by simpa only [storageLocations] using ready.sizeMember)
      (exitMember := by simpa only [storageLocations] using ready.exitMember)
      (offsetMember := by simpa only [storageLocations] using ready.offsetMember)
      (sizeMember := by simpa only [storageLocations] using ready.returnSizeMember)
      (logsMember := by simpa only [codeReady.base, accountReady.base] using logReady.logsMember) (logSizeMember := by simpa only [codeReady.base, accountReady.base] using logReady.logSizeMember)
    intro first firstMember second secondMember same
    obtain ⟨left, leftMember, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨right, rightMember, rfl⟩ := List.mem_map.mp secondMember
    exact cellLocations left leftMember right rightMember same
  obtain ⟨value, final, completed, resultRelated⟩ := frameCall_message_evaluates
    (by simpa only [slotTypes] using accepted)
    (by simpa only [supported_actual slotTypes] using eligible) closureRelated
    ((functionsRelated.prepend extra).evaluates (initial ++ suffix))
    ((CodeValue.packet referenceValues).evaluates (initial ++ suffix))
    (by simp [slots]) runtime (RuntimeExtendedInitializedEffects.initialized_separate (withCode := withCode) signature)
    (by simpa only [memoryLocation] using ready.memoryMember)
    (by simpa only [storageLocations] using ready.worldMember)
    (by simpa only [storageLocations] using ready.addressMember)
    (by simpa only [storageLocations] using ready.completeMember)
    (by simpa only [storageLocations] using ready.staticMember)
    (by simpa only [storageLocations] using ready.sizeMember)
    (by simpa only [storageLocations] using ready.exitMember)
    (by simpa only [storageLocations] using ready.offsetMember)
    (by simpa only [storageLocations] using ready.returnSizeMember)
    (by simpa only [codeReady.base, accountReady.base] using logReady.logsMember)
    (by simpa only [codeReady.base, accountReady.base] using logReady.logSizeMember)
    (by simpa only [codeReady.base] using accountReady.balancesMember) codeReady.codeMembers codeReady.dataMember codeReady.dataSizeMember codeReady.mode initialRelated passiveEnvironment evaluated context.address
    (by simpa only [storageLocations, worldSame] using worldReference.prepend extra) (by simpa only [balanceSame] using balancesReference.prepend extra)
    ((contextRelated.part (index := 4) rfl).prepend extra)
    (by simpa only [notDeploying] using (contextRelated.part (index := 11) rfl).prepend extra)
  exact ⟨value, final, completed, resultRelated⟩

end Solcore.Frontend.RustHull.ContractReturnDataCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractReturnDataExecutionCorrespondence
/-! Return-data operations reach the public contract runner through actual
compilation and initialization, including frames without code slots. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractReturnDataCorrespondence
open Correspondence ScalarExecution CodeBuilder ContractRuntimeEffectsCorrespondence

theorem objectRuntime_preserves {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {others : List Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (RuntimeExtendedInitializedEffects.slots withCode) fuel = .ok compiled)
    (catalogCompiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots withCode) fuel catalog others)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment : Core.Environment} {initial : Core.Store} {contextCode : Code}
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    {finalSource : Semantics.State RuntimeReturnDataEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeReturnDataEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime (RuntimeExtendedInitializedEffects.slots withCode) compiled others
        (ContractCatalogCorrespondence.images image catalog) image catalog contextCode depth) value final ∧
      MessageRel sourceResult finalSource.external context.address value := by
  obtain ⟨closure, captured⟩ := compileFrame_captures accepted environment
  obtain ⟨values, captures⟩ := catalogCompiled.captures environment
  apply objectRuntime_evaluates_separated
    (fun value _ => MessageRel sourceResult finalSource.external context.address value)
    (.cons captured captures) (ContractMemoryCorrespondence.sharedValues_related object context contextRelated)
  intro functions shared dispatcher creator extra allocated cells _ creatorLocation functionsRelated references initialized separate description _ _ creatorRelated creatorFound creatorAfter
  have entry := ContractCatalogCorrespondence.entry_reference captures functionsRelated
  exact objectFrame_evaluates accepted eligible captured entry object context notDeploying
    (contextRelated.prepend extra) references initialized separate description creatorRelated creatorFound creatorAfter evaluated

def PublicMessageRel (context : Contract.Context) (result : Semantics.Result Semantics.Value)
    (state : RuntimeReturnDataEffectsSemantics.State) (value : Core.Value) : Prop :=
  MessageRel result state (Contract.normalizeContext context).address value

/-- The actual compiler supplies every catalog closure. The independent entry
evaluation determines the result, including code availability and copy faults. -/
theorem compileObject_preserves {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {object : Contract.CompiledObject}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel image catalog = .ok object)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported (image.isSome || !catalog.isEmpty))
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (context : Contract.Context) (notDeploying : context.deploying = false)
    {finalSource : Semantics.State RuntimeReturnDataEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeReturnDataEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates [] [] (object.instantiate context).expression value final ∧
      PublicMessageRel context sourceResult finalSource.external value := by
  have compiled : AccountRuntime.compileObject program path fuel image catalog = .ok object.expression := by
    unfold Contract.compileObject at accepted
    obtain ⟨expression, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
    cases returned
    exact compiled
  obtain ⟨frame, others, frameCompiled, catalogCompiled, objectExpression⟩ :=
    ContractCatalogCorrespondence.compileObject_selected selected compiled
  have signature : ContractCatalogCorrespondence.slots image catalog =
      RuntimeExtendedInitializedEffects.slots (image.isSome || !catalog.isEmpty) := rfl
  rw [signature] at frameCompiled catalogCompiled objectExpression
  have normalized : (Contract.normalizeContext context).deploying = false := notDeploying
  obtain ⟨value, final, executed, related⟩ := objectRuntime_preserves frameCompiled
    (ContractCatalogCorrespondence.compiledCatalog catalogCompiled) eligible object
    (Contract.normalizeContext context) normalized
    (CodeValue.bound 0 [] (bundleValues (contextValues object (Contract.normalizeContext context)))) evaluated
  refine ⟨value, final, instantiate_evaluates context (parameter := AccountRuntime.contextType)
    (resultType := AccountRuntime.resultType) ?_ executed, related⟩
  rw [objectExpression]
  rfl

/-- Every genuine public resumption chain reaches the independently derived
message exactly when its cumulative fuel covers the required transitions. -/
theorem compileObject_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {object : Contract.CompiledObject}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel image catalog = .ok object)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported (image.isSome || !catalog.isEmpty))
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (context : Contract.Context) (notDeploying : context.deploying = false)
    {finalSource : Semantics.State RuntimeReturnDataEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeReturnDataEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value, PublicMessageRel context sourceResult finalSource.external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨value, _, executed, related⟩ :=
    compileObject_preserves selected accepted eligible context notDeploying evaluated
  exact ⟨value, related, Contract.evaluation_resumes_exact executed⟩

theorem prepare_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {context : Contract.Context} {prepared : Contract.Prepared}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.prepare program path context fuel = .ok prepared)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported false)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (notDeploying : context.deploying = false) :
    ∃ object, Contract.compileObject program path fuel none [] = .ok object ∧
      prepared = object.instantiate context ∧
      ∀ (sourceResult : Semantics.Result Semantics.Value) (finalSource : Semantics.State RuntimeReturnDataEffectsSemantics.State),
        Semantics.EvalFunction (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code])
          (RuntimeReturnDataEffectsSemantics.effects none)
          (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState none object (Contract.normalizeContext context)⟩ sourceResult finalSource →
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

end Solcore.Frontend.RustHull.ContractReturnDataCorrespondence
end
