import Solcore.Frontend.RustHull.ContractMemoryRuntimeFacts

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
