import Solcore.Frontend.RustHull.ContractRuntimeEffectsRuntimeFacts
import Solcore.Frontend.RustHull.RuntimeObjectLocationsCorrespondence

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
