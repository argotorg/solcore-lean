import Solcore.Frontend.RustHull.ContractReturnDataCorrespondence
import Solcore.Frontend.RustHull.RuntimeCallEffectsFrameCorrespondence
import Solcore.Frontend.RustHull.RuntimeExtendedInitializedEffects

/-! Message calls and their shared state reach actual message
completion with or without linked code cells. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractCallCorrespondence
open Correspondence ScalarExecution CodeBuilder

def supported (withCode : Bool) (name : String) : Prop :=
  ContractReturnDataCorrespondence.supported withCode name ∨ name = "call" ∨ name = "staticcall"

theorem supported_actual {slots : List EffectSlot} {withCode : Bool}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = RuntimeExtendedInitializedEffects.slots withCode) :
    RuntimeCallEffectsCorrespondence.supported slots withCode = supported withCode := by
  funext name
  apply propext
  simp only [RuntimeCallEffectsCorrespondence.supported, supported,
    ContractReturnDataCorrespondence.supported_actual signature]

def messageValue (result : Semantics.Result Semantics.Value) (state : RuntimeCallEffectsSemantics.State)
    (accounts : StorageCorrespondence.Accounts) (target : Core.Word) : Core.Value :=
  ContractAccountCorrespondence.messageValue result state.runtime.runtime accounts target

def MessageRel (result : Semantics.Result Semantics.Value) (state : RuntimeCallEffectsSemantics.State)
    (target : Core.Word) (value : Core.Value) : Prop :=
  ContractAccountCorrespondence.MessageRel result state.runtime.runtime target value

theorem frameCall_message_evaluates {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (RuntimeLogEffectsFrameCorrespondence.slotTypes slots) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram (RuntimeCallEffectsCorrespondence.supported slots withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : RuntimeCallEffectsCorrespondence.Layout} {image : Option (List UInt8)}
    {handlers : RuntimeCallEffectsCorrespondence.Handlers layout}
    {initial : RuntimeCallEffectsSemantics.State}
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
    (callDepthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (callHandlerMember : ⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ slots)
    (initialRelated : StateRel (RuntimeCallEffectsCorrespondence.model layout (prefixRead layout.boundary store) slots image handlers) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : RuntimeCallEffectsCorrespondence.CallPassive layout slots)
    {final : Semantics.State RuntimeCallEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCallEffectsSemantics.effects image)
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
    RuntimeCallEffectsFrameCorrespondence.compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length
      runtime separated memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode callDepthMember callHandlerMember initialRelated passive callPassive evaluated
  have balancesFinal := RuntimeAccountEffectsCorrespondence.balances_related (RuntimeCallEffectsCorrespondence.account_related related)
  let frameResult := frameCompletionValue status (ContractLogCorrespondence.snapshotValues final.external.runtime.runtime.runtime accounts final.external.runtime.runtime.balances)
    (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.runtime.storage.complete)
  obtain ⟨finalStore, completed⟩ := ContractLogCorrespondence.message_evaluates result final.external.runtime.runtime.runtime accounts address final.external.runtime.runtime.balances
    statusRelated (worldReference.prepend [frameResult]) (balancesReference.prepend [frameResult])
    (targetValue.prepend [frameResult]) (deployingValue.prepend [frameResult])
    (CodeValue.bound depth environment frameResult) worldFinal balancesFinal
  exact ⟨_, finalStore, .letE executed completed, accounts, represented, rfl⟩

end Solcore.Frontend.RustHull.ContractCallCorrespondence
