import Solcore.Frontend.RustHull.ContractRuntimeEffectsRuntimeFacts

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
