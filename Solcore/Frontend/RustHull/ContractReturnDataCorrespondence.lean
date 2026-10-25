import Solcore.Frontend.RustHull.ContractCodeCorrespondence
import Solcore.Frontend.RustHull.RuntimeReturnDataEffectsFrameCorrespondence
import Solcore.Frontend.RustHull.RuntimeExtendedInitializedEffects

/-! Return-data bounds and identity observations reach actual message
completion with or without linked code cells. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractReturnDataCorrespondence
open Correspondence ScalarExecution CodeBuilder

def supported (withCode : Bool) (name : String) : Prop :=
  (if withCode then ContractCodeCorrespondence.supported name else ContractAccountCorrespondence.supported name) ∨
    name = "returndatacopy" ∨ name = "memoryguard"

theorem supported_actual {slots : List EffectSlot} {withCode : Bool}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = RuntimeExtendedInitializedEffects.slots withCode) :
    RuntimeReturnDataEffectsCorrespondence.supported slots withCode = supported withCode := by
  funext name
  apply propext
  cases withCode with
  | false =>
      have base := congrFun (ContractAccountCorrespondence.supported_actual (by simpa [RuntimeExtendedInitializedEffects.slots] using signature)) name
      simp only [RuntimeReturnDataEffectsCorrespondence.supported, supported, Bool.false_eq_true, ↓reduceIte, false_and, false_or, base]
  | true =>
      have base := congrFun (ContractCodeCorrespondence.supported_actual (by simpa [RuntimeExtendedInitializedEffects.slots] using signature)) name
      simp only [RuntimeCodeEffectsCorrespondence.supported] at base
      simp only [RuntimeReturnDataEffectsCorrespondence.supported, supported, ↓reduceIte, true_and]
      rw [← base]
      simp only [or_assoc]

def messageValue (result : Semantics.Result Semantics.Value) (state : RuntimeReturnDataEffectsSemantics.State)
    (accounts : StorageCorrespondence.Accounts) (target : Core.Word) : Core.Value :=
  ContractAccountCorrespondence.messageValue result state.runtime accounts target

def MessageRel (result : Semantics.Result Semantics.Value) (state : RuntimeReturnDataEffectsSemantics.State)
    (target : Core.Word) (value : Core.Value) : Prop :=
  ContractAccountCorrespondence.MessageRel result state.runtime target value

theorem frameCall_message_evaluates {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (RuntimeLogEffectsFrameCorrespondence.slotTypes slots) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram (RuntimeReturnDataEffectsCorrespondence.supported slots withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : RuntimeReturnDataEffectsCorrespondence.Layout} {image : Option (List UInt8)}
    {initial : RuntimeReturnDataEffectsSemantics.State}
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
    (codeMembers : ∀ cells, layout.codeCells = some cells →
      ⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots)
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode)
    (initialRelated : StateRel (RuntimeReturnDataEffectsCorrespondence.model layout (prefixRead layout.boundary store) slots image) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {final : Semantics.State RuntimeReturnDataEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeReturnDataEffectsSemantics.effects image)
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
    RuntimeReturnDataEffectsFrameCorrespondence.compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length
      runtime separated memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode initialRelated passive evaluated
  have balancesFinal := RuntimeAccountEffectsCorrespondence.balances_related (RuntimeReturnDataEffectsCorrespondence.account_related related)
  let frameResult := frameCompletionValue status (ContractLogCorrespondence.snapshotValues final.external.runtime.runtime accounts final.external.runtime.balances)
    (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.storage.complete)
  obtain ⟨finalStore, completed⟩ := ContractLogCorrespondence.message_evaluates result final.external.runtime.runtime accounts address final.external.runtime.balances
    statusRelated (worldReference.prepend [frameResult]) (balancesReference.prepend [frameResult])
    (targetValue.prepend [frameResult]) (deployingValue.prepend [frameResult])
    (CodeValue.bound depth environment frameResult) worldFinal balancesFinal
  exact ⟨_, finalStore, .letE executed completed, accounts, represented, rfl⟩

end Solcore.Frontend.RustHull.ContractReturnDataCorrespondence
