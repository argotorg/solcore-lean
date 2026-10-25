import Solcore.Frontend.RustHull.ContractLogExecutionCorrespondence
import Solcore.Frontend.RustHull.ContractAccountCorrespondence
import Solcore.Frontend.RustHull.ContractHashExecutionCorrespondence
import Solcore.Frontend.RustHull.RuntimeAccountInitializedEffects
import Solcore.Frontend.RustHull.ContractEnvironmentRuntimeFacts
import Solcore.Frontend.RustHull.RuntimeLogInitializedEffects
import Solcore.Frontend.RustHull.RuntimeLogInitializationCorrespondence
import Solcore.Frontend.RustHull.ContractRuntimeInitializationCorrespondence
import Solcore.Frontend.RustHull.RuntimeObjectLocationsCorrespondence

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
