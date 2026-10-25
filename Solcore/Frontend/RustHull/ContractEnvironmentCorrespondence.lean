import Solcore.Frontend.RustHull.ContractRuntimeEffectsCorrespondence
import Solcore.Frontend.RustHull.RuntimeEnvironmentEffectsFrameCorrespondence

/-! Environment observations join memory and storage through the same actual
frame completion and account finalization code. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractEnvironmentCorrespondence
open Correspondence ScalarExecution CodeBuilder ContractRuntimeEffectsCorrespondence

def supported (name : String) : Prop := RuntimeEffectsCorrespondence.supported name ∨
  ∃ operation : EnvironmentSemantics.Operation, operation.name = name ∧
    ∀ input ∈ EnvironmentBuiltinCorrespondence.inputs operation, input ∈ Effects.slots

theorem supported_actual {slots : List EffectSlot}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots) :
    RuntimeEnvironmentEffectsCorrespondence.supported slots = supported := by
  funext name
  apply propext
  constructor
  · rintro (runtime | ⟨operation, named, available⟩)
    · exact .inl runtime
    · refine .inr ⟨operation, named, ?_⟩
      intro input member
      obtain ⟨location, present⟩ := available input.1 input.2 member
      rw [← signature]
      exact List.mem_map.mpr ⟨⟨input.1, input.2, location⟩, present, rfl⟩
  · rintro (runtime | ⟨operation, named, available⟩)
    · exact .inl runtime
    · refine .inr ⟨operation, named, ?_⟩
      intro inputName inputType member
      have present := available (inputName, inputType) member
      rw [← signature] at present
      obtain ⟨slot, slotMember, equal⟩ := List.mem_map.mp present
      obtain ⟨nameEqual, typeEqual⟩ := Prod.mk.inj equal
      exact ⟨slot.location, by simpa only [← nameEqual, ← typeEqual] using slotMember⟩

theorem frameCall_message_evaluates {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (RuntimeEffectsFrameCorrespondence.slotTypes slots) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram (RuntimeEnvironmentEffectsCorrespondence.supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {memoryLocation : Nat} {locations : StorageBuiltinCorrespondence.Locations}
    {initial : RuntimeEnvironmentEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument target deploying : Code} {depth : Nat}
    {shared : AccountRuntime.References} {images : List (Nat × List UInt8)} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before (function depth) closure initialStore)
    (supplied : Core.Evaluates environment initialStore (argument depth) (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (RuntimeEffectsFrameCorrespondence.slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, memoryLocation⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, locations.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, locations.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ slots)
    (memoryInitial : MemoryCorrespondence.StateRel memoryLocation locations.memorySize initial.runtime.memory store)
    (storageInitial : StorageBuiltinCorrespondence.StateRel locations initial.runtime.storage store)
    (distinct : (memoryLocation :: locations.all).Nodup)
    (observationsInitial : EnvironmentBuiltinCorrespondence.StateRel slots initial.environment store)
    (passive : RuntimeEnvironmentEffectsCorrespondence.Passive
      (RuntimeEffectsCorrespondence.initialLayout memoryInitial storageInitial distinct) slots)
    {final : Semantics.State RuntimeEnvironmentEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEnvironmentEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (address : Core.Word) (balances : StorageSemantics.Words)
    (snapshotObserved : ∀ name ∈ RuntimeEffectsFrameCorrespondence.passiveSnapshotNames,
      RuntimeEffectsFrameCorrespondence.PassiveCell
        (RuntimeEffectsCorrespondence.initialLayout memoryInitial storageInitial distinct) slots store name (passiveValues balances name))
    {balancesLocation : Nat}
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type locations.world))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type balancesLocation))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false))
    (balancesFound : store.read? balancesLocation = some (Core.WordMapping.encode balances))
    (balancesOutside : balancesLocation ∉ RuntimeEffectsCorrespondence.mutable
      (RuntimeEffectsCorrespondence.initialLayout memoryInitial storageInitial distinct)) :
    ∃ value finalStore, Core.Evaluates environment before
      (bind (apply function argument) (fun framed => AccountRuntime.completeMessage shared images target deploying framed) depth)
      value finalStore ∧ MessageRel result final.external.runtime address balances value := by
  obtain ⟨extension, status, accounts, bodyStore, represented, statusRelated, executed, related, worldFinal⟩ :=
    RuntimeEnvironmentEffectsFrameCorrespondence.compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length
      runtime separated memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      memoryInitial storageInitial distinct observationsInitial passive evaluated (passiveValues balances) snapshotObserved
  have balancesBound := (List.getElem?_eq_some_iff.mp balancesFound).1
  have balancesFinal : bodyStore.read? balancesLocation = some (Core.WordMapping.encode balances) := by
    have retained := (RuntimeEnvironmentEffectsCorrespondence.runtime_related related).external.2.2.other balancesLocation balancesOutside
    simpa only [prefixRead, RuntimeEffectsCorrespondence.initialLayout, balancesBound, ↓reduceIte, balancesFound] using retained
  let frameResult := frameCompletionValue status (snapshotValues final.external.runtime accounts balances)
    (StorageCorrespondence.get accounts final.external.runtime.storage.address final.external.runtime.storage.complete)
  obtain ⟨finalStore, completed⟩ := message_evaluates result final.external.runtime accounts address balances
    statusRelated (worldReference.prepend [frameResult]) (balancesReference.prepend [frameResult])
    (targetValue.prepend [frameResult]) (deployingValue.prepend [frameResult])
    (CodeValue.bound depth environment frameResult) worldFinal balancesFinal
  exact ⟨_, finalStore, .letE executed completed, accounts, represented, rfl⟩

end Solcore.Frontend.RustHull.ContractEnvironmentCorrespondence
