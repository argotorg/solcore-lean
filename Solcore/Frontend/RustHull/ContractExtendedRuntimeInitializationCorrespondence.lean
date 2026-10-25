import Solcore.Frontend.RustHull.ContractRuntimeInitializationCorrespondence
import Solcore.Frontend.RustHull.RuntimeExtendedInitializedEffects

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
