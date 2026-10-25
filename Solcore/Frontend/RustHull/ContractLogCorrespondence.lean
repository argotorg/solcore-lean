import Solcore.Frontend.RustHull.ContractEnvironmentCorrespondence
import Solcore.Frontend.RustHull.RuntimeLogEffectsFrameCorrespondence

/-! Source event snapshots pass through actual account finalization and
message completion together with the memory/storage result. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractLogCorrespondence
open Correspondence ScalarExecution CodeBuilder
abbrev resultValue := ContractRuntimeEffectsCorrespondence.resultValue
abbrev succeeded := ContractRuntimeEffectsCorrespondence.succeeded
abbrev passiveValues := ContractRuntimeEffectsCorrespondence.passiveValues

def supported (name : String) : Prop := ContractEnvironmentCorrespondence.supported name ∨
  ∃ operation : LogsSemantics.Operation, operation.name = name

theorem supported_actual {slots : List EffectSlot}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots) :
    RuntimeLogEffectsCorrespondence.supported slots = supported := by
  funext name
  simp only [RuntimeLogEffectsCorrespondence.supported, supported, ContractEnvironmentCorrespondence.supported_actual signature]

def snapshotValues (state : RuntimeLogEffectsSemantics.State) (accounts : StorageCorrespondence.Accounts)
    (balances : StorageSemantics.Words) : String → Core.Value :=
  RuntimeLogEffectsFrameCorrespondence.snapshotValues (passiveValues balances) state accounts

def messageValue (result : Semantics.Result Semantics.Value) (state : RuntimeLogEffectsSemantics.State)
    (accounts : StorageCorrespondence.Accounts) (target : Core.Word) (balances : StorageSemantics.Words) : Core.Value :=
  let snapshot := snapshotValues state accounts balances
  match StorageCorrespondence.get accounts state.runtime.runtime.storage.address state.runtime.runtime.storage.complete with
  | .error reason => completedMessageValue (.inLeft .unit (.word reason)) false state.runtime.runtime.storage.exit
      snapshot (Core.WordMapping.encode []) accounts target balances
  | .ok (account, _) => completedMessageValue (resultValue result) (succeeded result) state.runtime.runtime.storage.exit
      snapshot (Core.WordMapping.encode account.storage) accounts target balances

def MessageRel (result : Semantics.Result Semantics.Value) (state : RuntimeLogEffectsSemantics.State)
    (target : Core.Word) (balances : StorageSemantics.Words) (value : Core.Value) : Prop :=
  ∃ accounts : StorageCorrespondence.Accounts,
    accounts.map Prod.fst = state.runtime.runtime.storage.world ∧ value = messageValue result state accounts target balances

theorem message_evaluates {depth : Nat} {environment : Core.Environment}
    {shared : AccountRuntime.References} {images : List (Nat × List UInt8)} {target deploying framed : Code}
    {worldLocation balancesLocation : Nat} {initial : Core.Store}
    (sourceResult : Semantics.Result Semantics.Value) (state : RuntimeLogEffectsSemantics.State)
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
        (StorageCorrespondence.get accounts state.runtime.runtime.storage.address state.runtime.runtime.storage.complete)))
    (worldFound : initial.read? worldLocation = some (StorageCorrespondence.world accounts))
    (balancesFound : initial.read? balancesLocation = some (Core.WordMapping.encode balances)) :
    ∃ final, Core.Evaluates environment initial
      (AccountRuntime.completeMessage shared images target deploying framed depth)
      (messageValue sourceResult state accounts address balances) final := by
  cases got : StorageCorrespondence.get accounts state.runtime.runtime.storage.address state.runtime.runtime.storage.complete with
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
          exact ⟨final, by simpa only [messageValue, got, resultValue, ContractMemoryCorrespondence.resultValue, succeeded, ContractRuntimeEffectsCorrespondence.succeeded] using evaluated⟩
      | language reason =>
          obtain ⟨final, evaluated⟩ := completeMessage_evaluates accounts balances worldReference balancesReference
            targetValue deployingValue framedRelated (MessageStatus.failure (.word reason)) rfl worldFound balancesFound
          exact ⟨final, by simpa only [messageValue, got, resultValue, ContractMemoryCorrespondence.resultValue, succeeded, ContractRuntimeEffectsCorrespondence.succeeded] using evaluated⟩

theorem frameCall_message_evaluates {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (RuntimeLogEffectsFrameCorrespondence.slotTypes slots) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram (RuntimeLogEffectsCorrespondence.supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : RuntimeLogEffectsCorrespondence.Layout}
    {initial : RuntimeLogEffectsSemantics.State}
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
    (initialRelated : StateRel (RuntimeLogEffectsCorrespondence.model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout slots)
    {final : Semantics.State RuntimeLogEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeLogEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (address : Core.Word) (balances : StorageSemantics.Words)
    (snapshotObserved : ∀ name ∈ RuntimeLogEffectsFrameCorrespondence.passiveSnapshotNames,
      RuntimeLogEffectsFrameCorrespondence.PassiveCell layout slots store name (passiveValues balances name))
    {balancesLocation : Nat}
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type layout.storage.world))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type balancesLocation))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false))
    (balancesFound : store.read? balancesLocation = some (Core.WordMapping.encode balances))
    (balancesBound : balancesLocation < layout.boundary)
    (balancesOutside : balancesLocation ∉ RuntimeLogEffectsCorrespondence.mutable layout) :
    ∃ value finalStore, Core.Evaluates environment before
      (bind (apply function argument) (fun framed => AccountRuntime.completeMessage shared images target deploying framed) depth)
      value finalStore ∧ MessageRel result final.external address balances value := by
  obtain ⟨extension, status, accounts, bodyStore, represented, statusRelated, executed, related, worldFinal⟩ :=
    RuntimeLogEffectsFrameCorrespondence.compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length
      runtime separated memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember initialRelated passive evaluated (passiveValues balances) snapshotObserved
  have balancesFinal : bodyStore.read? balancesLocation = some (Core.WordMapping.encode balances) := by
    have retained := RuntimeLogEffectsCorrespondence.other_related related balancesOutside
    simpa only [prefixRead, balancesBound, ↓reduceIte, balancesFound] using retained
  let frameResult := frameCompletionValue status (snapshotValues final.external accounts balances)
    (StorageCorrespondence.get accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete)
  obtain ⟨finalStore, completed⟩ := message_evaluates result final.external accounts address balances
    statusRelated (worldReference.prepend [frameResult]) (balancesReference.prepend [frameResult])
    (targetValue.prepend [frameResult]) (deployingValue.prepend [frameResult])
    (CodeValue.bound depth environment frameResult) worldFinal balancesFinal
  exact ⟨_, finalStore, .letE executed completed, accounts, represented, rfl⟩

end Solcore.Frontend.RustHull.ContractLogCorrespondence
