import Solcore.Frontend.RustHull.ContractHashCorrespondence
import Solcore.Frontend.RustHull.RuntimeAccountEffectsFrameCorrespondence

/-! Account observations and the explicit source balance ledger pass through
actual message finalization and transaction completion. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractAccountCorrespondence
open Correspondence ScalarExecution CodeBuilder

def supported (name : String) : Prop := ContractHashCorrespondence.supported name ∨
  ∃ operation : AccountObservationSemantics.Operation, operation.name = name

theorem supported_actual {slots : List EffectSlot}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots) :
    RuntimeAccountEffectsCorrespondence.supported slots = supported := by
  funext name
  simp only [RuntimeAccountEffectsCorrespondence.supported, supported, ContractHashCorrespondence.supported_actual signature]

def messageValue (result : Semantics.Result Semantics.Value) (state : RuntimeAccountEffectsSemantics.State)
    (accounts : StorageCorrespondence.Accounts) (target : Core.Word) : Core.Value :=
  ContractLogCorrespondence.messageValue result state.runtime accounts target state.balances

def MessageRel (result : Semantics.Result Semantics.Value) (state : RuntimeAccountEffectsSemantics.State)
    (target : Core.Word) (value : Core.Value) : Prop :=
  ContractLogCorrespondence.MessageRel result state.runtime target state.balances value

theorem frameCall_message_evaluates {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (RuntimeLogEffectsFrameCorrespondence.slotTypes slots) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram (RuntimeAccountEffectsCorrespondence.supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : RuntimeAccountEffectsCorrespondence.Layout}
    {initial : RuntimeAccountEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument target deploying : Code} {depth : Nat}
    {shared : AccountRuntime.References} {images : List (Nat × List UInt8)} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before (function depth) closure initialStore)
    (supplied : Core.Evaluates environment initialStore (argument depth) (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (RuntimeLogEffectsFrameCorrespondence.slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (initialRelated : StateRel (RuntimeAccountEffectsCorrespondence.model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {final : Semantics.State RuntimeAccountEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeAccountEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (address : Core.Word)
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type layout.storage.world))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type layout.balances))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false)) :
    ∃ value finalStore, Core.Evaluates environment before
      (bind (apply function argument) (fun framed => AccountRuntime.completeMessage shared images target deploying framed) depth)
      value finalStore ∧ MessageRel result final.external address value := by
  obtain ⟨extension, status, accounts, bodyStore, represented, statusRelated, executed, related, worldFinal⟩ :=
    RuntimeAccountEffectsFrameCorrespondence.compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length
      runtime separated memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember balancesMember initialRelated passive evaluated
  have balancesFinal := RuntimeAccountEffectsCorrespondence.balances_related related
  let frameResult := frameCompletionValue status (ContractLogCorrespondence.snapshotValues final.external.runtime accounts final.external.balances)
    (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.storage.complete)
  obtain ⟨finalStore, completed⟩ := ContractLogCorrespondence.message_evaluates result final.external.runtime accounts address final.external.balances
    statusRelated (worldReference.prepend [frameResult]) (balancesReference.prepend [frameResult])
    (targetValue.prepend [frameResult]) (deployingValue.prepend [frameResult])
    (CodeValue.bound depth environment frameResult) worldFinal balancesFinal
  exact ⟨_, finalStore, .letE executed completed, accounts, represented, rfl⟩

end Solcore.Frontend.RustHull.ContractAccountCorrespondence
