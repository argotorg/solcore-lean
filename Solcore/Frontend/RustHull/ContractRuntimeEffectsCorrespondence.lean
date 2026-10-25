import Solcore.Frontend.RustHull.ContractMemoryCorrespondence
import Solcore.Frontend.RustHull.RuntimeEffectsFrameCorrespondence
import Solcore.Frontend.RustHull.RuntimeEffectsProjectionPreservation

/-! Independent memory and storage outcomes pass through the actual message
completion code, including static-write exit status and account finalization. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractRuntimeEffectsCorrespondence
open Correspondence ScalarExecution CodeBuilder

abbrev resultValue := ContractMemoryCorrespondence.resultValue

def succeeded : Semantics.Result Semantics.Value → Bool
  | .value _ => true
  | .fault _ => false

def passiveValues (balances : StorageSemantics.Words) (name : String) : Core.Value :=
  if name = "balances" then Core.WordMapping.encode balances
  else if name = "logs" then Core.WordMapping.encode []
  else .word (Core.Word.ofNatModulo 0)

def snapshotValues (state : RuntimeEffectsSemantics.State) (accounts : StorageCorrespondence.Accounts)
    (balances : StorageSemantics.Words) : String → Core.Value :=
  RuntimeEffectsFrameCorrespondence.snapshotValues (passiveValues balances) state accounts

def messageValue (result : Semantics.Result Semantics.Value) (state : RuntimeEffectsSemantics.State)
    (accounts : StorageCorrespondence.Accounts) (target : Core.Word) (balances : StorageSemantics.Words) : Core.Value :=
  let snapshot := snapshotValues state accounts balances
  match StorageCorrespondence.get accounts state.storage.address state.storage.complete with
  | .error reason => completedMessageValue (.inLeft .unit (.word reason)) false state.storage.exit
      snapshot (Core.WordMapping.encode []) accounts target balances
  | .ok (account, _) => completedMessageValue (resultValue result) (succeeded result) state.storage.exit
      snapshot (Core.WordMapping.encode account.storage) accounts target balances

def MessageRel (result : Semantics.Result Semantics.Value) (state : RuntimeEffectsSemantics.State)
    (target : Core.Word) (balances : StorageSemantics.Words) (value : Core.Value) : Prop :=
  ∃ accounts : StorageCorrespondence.Accounts,
    accounts.map Prod.fst = state.storage.world ∧ value = messageValue result state accounts target balances

theorem message_evaluates {depth : Nat} {environment : Core.Environment}
    {shared : AccountRuntime.References} {images : List (Nat × List UInt8)} {target deploying framed : Code}
    {worldLocation balancesLocation : Nat} {initial : Core.Store}
    (sourceResult : Semantics.Result Semantics.Value) (state : RuntimeEffectsSemantics.State)
    (accounts : StorageCorrespondence.Accounts) (address : Core.Word) (balances : StorageSemantics.Words)
    {status : Core.Value} (statusRelated : ResultRel .unit sourceResult status)
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type worldLocation))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type balancesLocation))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false))
    (framedValue : CodeValue depth environment framed
      (frameCompletionValue status (snapshotValues state accounts balances)
        (StorageCorrespondence.get accounts state.storage.address state.storage.complete)))
    (worldFound : initial.read? worldLocation = some (StorageCorrespondence.world accounts))
    (balancesFound : initial.read? balancesLocation = some (Core.WordMapping.encode balances)) :
    ∃ final, Core.Evaluates environment initial
      (AccountRuntime.completeMessage shared images target deploying framed depth)
      (messageValue sourceResult state accounts address balances) final := by
  cases got : StorageCorrespondence.get accounts state.storage.address state.storage.complete with
  | error reason =>
      have framedRelated : CodeValue depth environment framed
          (.pair (.inLeft .unit (.word reason))
            (frameSnapshotValue (snapshotValues state accounts balances) (Core.WordMapping.encode []))) := by
        simpa only [got, frameCompletionValue] using framedValue
      obtain ⟨final, evaluated⟩ := completeMessage_evaluates accounts balances worldReference balancesReference
        targetValue deployingValue framedRelated (MessageStatus.failure (.word reason)) rfl worldFound balancesFound
      exact ⟨final, by simpa only [messageValue, got] using evaluated⟩
  | ok pair =>
      rcases pair with ⟨account, identity⟩
      have framedRelated : CodeValue depth environment framed
          (.pair status (frameSnapshotValue (snapshotValues state accounts balances) (Core.WordMapping.encode account.storage))) := by
        simpa only [got, frameCompletionValue] using framedValue
      cases statusRelated with
      | value related =>
          cases related
          obtain ⟨final, evaluated⟩ := completeMessage_evaluates accounts balances worldReference balancesReference
            targetValue deployingValue framedRelated MessageStatus.success rfl worldFound balancesFound
          exact ⟨final, by simpa only [messageValue, got, resultValue, ContractMemoryCorrespondence.resultValue, succeeded] using evaluated⟩
      | language reason =>
          obtain ⟨final, evaluated⟩ := completeMessage_evaluates accounts balances worldReference balancesReference
            targetValue deployingValue framedRelated (MessageStatus.failure (.word reason)) rfl worldFound balancesFound
          exact ⟨final, by simpa only [messageValue, got, resultValue, ContractMemoryCorrespondence.resultValue, succeeded] using evaluated⟩

theorem frameCall_message_evaluates {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (RuntimeEffectsFrameCorrespondence.slotTypes slots) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram RuntimeEffectsCorrespondence.supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {memoryLocation : Nat} {locations : StorageBuiltinCorrespondence.Locations}
    {initial : RuntimeEffectsSemantics.State}
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
    (memoryInitial : MemoryCorrespondence.StateRel memoryLocation locations.memorySize initial.memory store)
    (storageInitial : StorageBuiltinCorrespondence.StateRel locations initial.storage store)
    (distinct : (memoryLocation :: locations.all).Nodup)
    {final : Semantics.State RuntimeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEffectsSemantics.effects
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
      value finalStore ∧ MessageRel result final.external address balances value := by
  obtain ⟨extension, status, accounts, bodyStore, represented, statusRelated, executed, related, worldFinal⟩ :=
    RuntimeEffectsFrameCorrespondence.compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length
      runtime separated memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      memoryInitial storageInitial distinct evaluated (passiveValues balances) snapshotObserved
  have balancesBound := (List.getElem?_eq_some_iff.mp balancesFound).1
  have balancesFinal : bodyStore.read? balancesLocation = some (Core.WordMapping.encode balances) := by
    have retained := related.external.2.2.other balancesLocation balancesOutside
    simpa only [prefixRead, RuntimeEffectsCorrespondence.initialLayout, balancesBound, ↓reduceIte, balancesFound] using retained
  let frameResult := frameCompletionValue status (snapshotValues final.external accounts balances)
    (StorageCorrespondence.get accounts final.external.storage.address final.external.storage.complete)
  obtain ⟨finalStore, completed⟩ := message_evaluates result final.external accounts address balances
    statusRelated (worldReference.prepend [frameResult]) (balancesReference.prepend [frameResult])
    (targetValue.prepend [frameResult]) (deployingValue.prepend [frameResult])
    (CodeValue.bound depth environment frameResult) worldFinal balancesFinal
  exact ⟨_, finalStore, .letE executed completed, accounts, represented, rfl⟩

end Solcore.Frontend.RustHull.ContractRuntimeEffectsCorrespondence
