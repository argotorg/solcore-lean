import Solcore.Frontend.RustHull.ChildFrameInitializedResources

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
