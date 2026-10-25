import Solcore.Frontend.RustHull.RuntimeObjectInitializationCorrespondence
import Solcore.Frontend.RustHull.MemoryFrameCorrespondence
import Solcore.Frontend.RustHull.ContractInputCorrespondence

/-! Public contract execution of the memory fragment follows the independent
Hull derivation through allocation, frame execution and message finalization. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractMemoryCorrespondence
open Correspondence ScalarExecution CodeBuilder

def resultValue : Semantics.Result Semantics.Value → Core.Value
  | .fault (.language reason) => .inLeft .unit (.word reason)
  | _ => .inRight .word .unit

def snapshotValues (memory : MemorySemantics.State) (accounts : StorageCorrespondence.Accounts)
    (balances : StorageSemantics.Words) (name : String) : Core.Value :=
  if name = "memory" then Core.WordMapping.encode memory.words
  else if name = "world" then StorageCorrespondence.world accounts
  else if name = "balances" then Core.WordMapping.encode balances
  else if name = "logs" then Core.WordMapping.encode []
  else .word (Core.Word.ofNatModulo 0)

def messageValue (result : Semantics.Result Semantics.Value) (memory : MemorySemantics.State)
    (accounts : StorageCorrespondence.Accounts) (address : Core.Word) (complete : Bool)
    (balances : StorageSemantics.Words) : Core.Value :=
  let snapshot := snapshotValues memory accounts balances
  let framed := frameCompletionValue (resultValue result) snapshot (StorageCorrespondence.get accounts address complete)
  match StorageCorrespondence.get accounts address complete, result with
  | .ok _, .value _ =>
      match StorageCorrespondence.get (StorageCorrespondence.finalize accounts balances).1 address true with
      | .ok (account, _) => .pair (resultValue result)
          (finalizedSnapshotValue snapshot account (StorageCorrespondence.finalize accounts balances).1
            (StorageCorrespondence.finalize accounts balances).2)
      | .error _ => framed
  | _, _ => framed

theorem resultValue_eq {result : Semantics.Result Semantics.Value} {value : Core.Value}
    (related : ResultRel .unit result value) : value = resultValue result := by
  cases related with
  | value related => cases related; rfl
  | language reason => rfl

/-- Both completion branches are determined by the independent source result.
Successful messages execute concrete account finalization before exporting;
language failures retain the frame snapshot without changing shared state. -/
theorem message_evaluates {depth : Nat} {environment : Core.Environment}
    {shared : AccountRuntime.References} {images : List (Nat × List UInt8)} {target deploying framed : Code}
    {worldLocation balancesLocation : Nat} {initial : Core.Store}
    (sourceResult : Semantics.Result Semantics.Value) (memory : MemorySemantics.State)
    (accounts : StorageCorrespondence.Accounts) (address : Core.Word) (complete : Bool) (balances : StorageSemantics.Words)
    {status : Core.Value} (statusRelated : ResultRel .unit sourceResult status)
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type worldLocation))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type balancesLocation))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false))
    (framedValue : CodeValue depth environment framed
      (frameCompletionValue status (snapshotValues memory accounts balances)
        (StorageCorrespondence.get accounts address complete)))
    (worldFound : initial.read? worldLocation = some (StorageCorrespondence.world accounts))
    (balancesFound : initial.read? balancesLocation = some (Core.WordMapping.encode balances)) :
    ∃ final, Core.Evaluates environment initial
      (AccountRuntime.completeMessage shared images target deploying framed depth)
      (messageValue sourceResult memory accounts address complete balances) final := by
  have statusEqual := resultValue_eq statusRelated
  cases got : StorageCorrespondence.get accounts address complete with
  | error reason =>
      have framedRelated : CodeValue depth environment framed
          (.pair (.inLeft .unit (.word reason))
            (frameSnapshotValue (snapshotValues memory accounts balances) (Core.WordMapping.encode []))) := by
        simpa only [got, frameCompletionValue] using framedValue
      refine ⟨initial, ?_⟩
      have completed := completeMessage_failure (shared := shared) (images := images) (target := target)
        (deploying := deploying) framedRelated (MessageStatus.failure (.word reason))
        (by rfl : snapshotValues memory accounts balances "exit" = .word (Core.Word.ofNatModulo 0)) (by decide) initial
      simpa only [messageValue, got, frameCompletionValue] using completed
  | ok pair =>
      rcases pair with ⟨account, identity⟩
      have framedRelated : CodeValue depth environment framed
          (.pair status (frameSnapshotValue (snapshotValues memory accounts balances) (Core.WordMapping.encode account.storage))) := by
        simpa only [got, frameCompletionValue] using framedValue
      cases statusRelated with
      | value related =>
          cases related
          obtain ⟨finalAccount, finalIdentity, final, finalGot, completed, _, _, _⟩ :=
            completeMessage_success accounts balances worldReference balancesReference targetValue deployingValue
              framedRelated MessageStatus.success
              (by rfl : snapshotValues memory accounts balances "exit" = .word (Core.Word.ofNatModulo 0))
              (by decide) worldFound balancesFound
          exact ⟨final, by simpa only [messageValue, got, finalGot, resultValue] using completed⟩
      | language reason =>
          refine ⟨initial, ?_⟩
          have completed := completeMessage_failure (shared := shared) (images := images) (target := target)
            (deploying := deploying) framedRelated (MessageStatus.failure (.word reason))
            (by rfl : snapshotValues memory accounts balances "exit" = .word (Core.Word.ofNatModulo 0)) (by decide) initial
          simpa only [messageValue, got, frameCompletionValue, resultValue] using completed

theorem compileObject_selected {program : Program} {path : List String} {code : CodeBlock}
    {fuel : Nat} {codeBytes : Option (List UInt8)} {expression : Core.Expr}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : AccountRuntime.compileObject program path fuel codeBytes [] = .ok expression) :
    ∃ compiled,
      AccountRuntime.compileFrame program code
        (Effects.slots ++ (if codeBytes.isSome then Effects.codeSlots else [])) fuel = .ok compiled ∧
      expression = AccountRuntime.objectExpression
        (Effects.slots ++ (if codeBytes.isSome then Effects.codeSlots else []))
        compiled [] (codeBytes.toList.map (1, ·)) codeBytes [] := by
  unfold AccountRuntime.compileObject at accepted
  obtain ⟨selectedCode, selectedAgain, accepted⟩ := lower_bind_eq_ok.mp accepted
  have same := Except.ok.inj (selectedAgain.symm.trans selected)
  subst selectedCode
  obtain ⟨compiled, compiledOk, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨others, mapped, accepted⟩ := lower_bind_eq_ok.mp accepted
  have empty : others = [] := by simpa using (Except.ok.inj mapped).symm
  subst others
  obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨guard, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  cases guard
  cases accepted
  exact ⟨compiled, by simpa using compiledOk, by simp⟩

/-- A source-driven call of the installed frame continues into the actual
message completion code; its resulting value is determined solely by the
source result, final memory and supplied account data. -/
theorem frameCall_message_evaluates {program : Program} {code : CodeBlock}
    {slots : List EffectSlot} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (MemoryFrameCorrespondence.slotTypes slots) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram MemoryEffectCorrespondence.supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment captured : Core.Environment} {initial : Core.Store}
    {function argument target deploying : Code} {shared : AccountRuntime.References}
    {images : List (Nat × List UInt8)} {closure : Core.Value} {values : List Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment initial (function depth) closure initial)
    (supplied : Core.Evaluates environment initial (argument depth) (bundleValues values) initial)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots
      (AccountRuntime.frameScope (MemoryFrameCorrespondence.slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    {memoryLocation sizeLocation : Nat}
    (memoryMember : ⟨"memory", Core.WordMapping.type, memoryLocation⟩ ∈ slots)
    (sizeMember : ⟨"memorySize", .word, sizeLocation⟩ ∈ slots)
    (memoryInitial : MemoryCorrespondence.StateRel memoryLocation sizeLocation ⟨[], Core.Word.ofNatModulo 0⟩ initial)
    {finalSource : Semantics.State MemorySemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) MemorySemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], ⟨[], Core.Word.ofNatModulo 0⟩⟩ sourceResult finalSource)
    (accounts : StorageCorrespondence.Accounts) (address : Core.Word) (complete : Bool) (balances : StorageSemantics.Words)
    (worldObserved : MemoryFrameCorrespondence.PassiveCell (MemoryEffectCorrespondence.initialLayout memoryInitial)
      slots initial "world" (StorageCorrespondence.world accounts))
    (addressObserved : MemoryFrameCorrespondence.PassiveCell (MemoryEffectCorrespondence.initialLayout memoryInitial)
      slots initial "address" (.word address))
    (completeObserved : MemoryFrameCorrespondence.PassiveCell (MemoryEffectCorrespondence.initialLayout memoryInitial)
      slots initial "worldComplete" (.bool complete))
    (snapshotObserved : ∀ name ∈ frameSnapshotNames, name ≠ "memory" →
      MemoryFrameCorrespondence.PassiveCell (MemoryEffectCorrespondence.initialLayout memoryInitial) slots initial
        name (snapshotValues ⟨[], Core.Word.ofNatModulo 0⟩ accounts balances name))
    {worldLocation balancesLocation : Nat}
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type worldLocation))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type balancesLocation))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false))
    (worldFound : initial.read? worldLocation = some (StorageCorrespondence.world accounts))
    (balancesFound : initial.read? balancesLocation = some (Core.WordMapping.encode balances))
    (worldMemory : worldLocation ≠ memoryLocation) (worldSize : worldLocation ≠ sizeLocation)
    (balancesMemory : balancesLocation ≠ memoryLocation) (balancesSize : balancesLocation ≠ sizeLocation) :
    ∃ final, Core.Evaluates environment initial
      (bind (apply function argument) (fun result => AccountRuntime.completeMessage shared images target deploying result) depth)
      (messageValue sourceResult finalSource.external accounts address complete balances) final := by
  obtain ⟨extension, status, bodyStore, statusRelated, executed, related⟩ :=
    MemoryFrameCorrespondence.compileFrame_call_preserves accepted eligible closureRelated resolved supplied length
      runtime separated memoryMember sizeMember memoryInitial evaluated accounts address complete worldObserved addressObserved
      completeObserved (snapshotValues ⟨[], Core.Word.ofNatModulo 0⟩ accounts balances) snapshotObserved
  have snapshots : MemoryFrameCorrespondence.snapshotValues
      (snapshotValues ⟨[], Core.Word.ofNatModulo 0⟩ accounts balances) finalSource.external =
      snapshotValues finalSource.external accounts balances := by
    funext name
    simp only [MemoryFrameCorrespondence.snapshotValues, snapshotValues]
    split <;> rfl
  rw [snapshots] at executed
  have worldBound := (List.getElem?_eq_some_iff.mp worldFound).1
  have balancesBound := (List.getElem?_eq_some_iff.mp balancesFound).1
  have worldFinal : bodyStore.read? worldLocation = some (StorageCorrespondence.world accounts) := by
    have retained := related.external.2.2.2.2 worldLocation worldMemory worldSize
    simpa only [prefixRead, MemoryEffectCorrespondence.initialLayout, worldBound, ↓reduceIte, worldFound] using retained
  have balancesFinal : bodyStore.read? balancesLocation = some (Core.WordMapping.encode balances) := by
    have retained := related.external.2.2.2.2 balancesLocation balancesMemory balancesSize
    simpa only [prefixRead, MemoryEffectCorrespondence.initialLayout, balancesBound, ↓reduceIte, balancesFound] using retained
  let frameResult := frameCompletionValue status (snapshotValues finalSource.external accounts balances)
    (StorageCorrespondence.get accounts address complete)
  obtain ⟨final, completed⟩ := message_evaluates sourceResult finalSource.external accounts address complete balances
    statusRelated (worldReference.prepend [frameResult]) (balancesReference.prepend [frameResult])
    (targetValue.prepend [frameResult]) (deployingValue.prepend [frameResult])
    (CodeValue.bound depth environment frameResult) worldFinal balancesFinal
  exact ⟨final, .letE executed completed⟩

end Solcore.Frontend.RustHull.ContractMemoryCorrespondence
