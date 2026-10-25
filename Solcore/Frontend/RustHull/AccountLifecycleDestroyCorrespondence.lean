import Solcore.Frontend.RustHull.AccountLifecycleCorrespondence

/-! The actual lifecycle entry evaluates its arguments once, normalizes both
addresses, obtains the current record, and reaches the independently specified
balance and pending-deletion result. Exact account identities are retained. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountLifecycleCorrespondence
open Core Correspondence ScalarExecution CodeBuilder
open AccountCallCorrespondence (retained_read)
open StorageCorrespondence (Accounts)

def argumentsValue (worldLocation balancesLocation : Nat) (current beneficiary : Word) (complete : Bool) : Value :=
  bundleValues [.cellRef AccountState.type worldLocation, .cellRef WordMapping.type balancesLocation,
    .word current, .word beneficiary, .bool complete]

theorem destroy_preserves {environment : Core.Environment} {before store : Core.Store}
    {worldReference balancesReference currentExpr beneficiaryExpr completeExpr : Core.Expr}
    (accounts : Accounts) (balances : StorageSemantics.Words) (worldLocation balancesLocation : Nat)
    (current beneficiary : Word) (complete : Bool)
    (arguments : Core.Evaluates environment before
      (bundle [worldReference, balancesReference, currentExpr, beneficiaryExpr, completeExpr])
      (argumentsValue worldLocation balancesLocation current beneficiary complete) store)
    (worldRead : store.read? worldLocation = some (StorageCorrespondence.world accounts))
    (balancesRead : store.read? balancesLocation = some (WordMapping.encode balances))
    (separate : worldLocation ≠ balancesLocation) :
    ∃ final, Core.Evaluates environment before
      (AccountLifecycle.destroy worldReference balancesReference currentExpr beneficiaryExpr completeExpr)
      (StorageCorrespondence.unitResult (destroyAccounts accounts balances current beneficiary complete)) final ∧
      final.read? worldLocation = some (StorageCorrespondence.world
        (nextAccounts accounts (destroyAccounts accounts balances current beneficiary complete))) ∧
      final.read? balancesLocation = some (WordMapping.encode
        (nextBalances balances (destroyAccounts accounts balances current beneficiary complete))) ∧
      Frame worldLocation balancesLocation store final := by
  let packetValue := argumentsValue worldLocation balancesLocation current beneficiary complete
  let currentAddress := AccountLifecycleSemantics.address current
  let recipientAddress := AccountLifecycleSemantics.address beneficiary
  let args : Code := fun here => .var (here - 0 - 1)
  let currentCode : Code := fun here => .var (here - 1 - 1)
  let recipientCode : Code := fun here => .var (here - 2 - 1)
  let front : Core.Environment := [.word recipientAddress, .word currentAddress, packetValue]
  have argsBound : CodeValue 1 (packetValue :: environment) args packetValue := CodeValue.bound 0 environment packetValue
  have currentEvaluated : Core.Evaluates (packetValue :: environment) store
      (address (part 2 5 args) 1) (.word currentAddress) store :=
    .binary ((argsBound.part (index := 2) rfl).evaluates store) .word rfl
  have currentBound : CodeValue 2 (.word currentAddress :: packetValue :: environment) currentCode (.word currentAddress) :=
    CodeValue.bound 1 (packetValue :: environment) (.word currentAddress)
  have recipientEvaluated : Core.Evaluates (.word currentAddress :: packetValue :: environment) store
      (address (part 3 5 args) 2) (.word recipientAddress) store :=
    .binary (((argsBound.prepend [.word currentAddress]).part (index := 3) rfl).evaluates store) .word rfl
  have recipientBound : CodeValue 3 (front ++ environment) recipientCode (.word recipientAddress) :=
    CodeValue.bound 2 (.word currentAddress :: packetValue :: environment) (.word recipientAddress)
  have currentRelated : CodeValue 3 (front ++ environment) currentCode (.word currentAddress) :=
    currentBound.prepend [.word recipientAddress]
  have argsRelated : CodeValue 3 (front ++ environment) args packetValue :=
    argsBound.prepend [.word recipientAddress, .word currentAddress]
  have worldValue : CodeValue 3 (front ++ environment) (part 0 5 args) (.cellRef AccountState.type worldLocation) :=
    argsRelated.part (index := 0) rfl
  have balancesValue : CodeValue 3 (front ++ environment) (part 1 5 args) (.cellRef WordMapping.type balancesLocation) :=
    argsRelated.part (index := 1) rfl
  have fetched := StorageCorrespondence.get_evaluates accounts currentAddress complete
    (.loadCell (worldValue.evaluates store) worldRead) (currentRelated.evaluates store)
    ((argsRelated.part (index := 4) rfl).evaluates store)
  let fetchedStore := StorageCorrespondence.getStore accounts currentAddress complete (front ++ environment) store
  have retained : StoreRetains store fetchedStore := StoreRetains.append _ _
  cases found : StorageCorrespondence.get accounts currentAddress complete with
  | error reason =>
    have outcome : destroyAccounts accounts balances current beneficiary complete = .error reason := by
      unfold destroyAccounts
      dsimp only
      rw [found]
      rfl
    simp only [outcome, StorageCorrespondence.unitResult, nextAccounts, nextBalances]
    refine ⟨fetchedStore, ?_, retained_read retained worldRead, retained_read retained balancesRead, frame_retained retained⟩
    apply Core.Evaluates.letE arguments
    apply Core.Evaluates.letE currentEvaluated
    apply Core.Evaluates.letE recipientEvaluated
    apply LanguageResult.bind_failure .unit
    simpa only [found, StorageCorrespondence.getValue, front, fetchedStore, args, currentCode, CodeBuilder.load, List.length_cons, List.length_nil, List.cons_append, List.nil_append] using fetched
  | ok pair =>
    rcases pair with ⟨account, identity⟩
    let recordValue := StorageCorrespondence.record account identity
    have recordBound := CodeValue.bound 3 (front ++ environment) recordValue
    obtain ⟨final, evaluated, finalWorld, finalBalances, frame⟩ :=
      destroyRecord_preserves (worldValue.prepend [recordValue]) (balancesValue.prepend [recordValue])
        (currentRelated.prepend [recordValue]) (recipientBound.prepend [recordValue]) recordBound
        (retained_read retained worldRead) (retained_read retained balancesRead) separate
    have outcome : destroyAccounts accounts balances current beneficiary complete =
        recordOutcome accounts balances currentAddress recipientAddress account identity := by
      unfold destroyAccounts
      dsimp only
      rw [found]
      change (do let next ← AccountLifecycleSemantics.balances account.created currentAddress recipientAddress balances; pure (publishAccounts accounts currentAddress account identity, next)) = _
      unfold recordOutcome
      cases AccountLifecycleSemantics.balances account.created currentAddress recipientAddress balances <;> rfl
    simp only [outcome]
    refine ⟨final, ?_, finalWorld, finalBalances, frame_trans (frame_retained retained) frame⟩
    apply Core.Evaluates.letE arguments
    apply Core.Evaluates.letE currentEvaluated
    apply Core.Evaluates.letE recipientEvaluated
    apply LanguageResult.bind_success .unit (by simpa only [found, StorageCorrespondence.getValue, front, fetchedStore, args, currentCode, CodeBuilder.load, List.length_cons, List.length_nil, List.cons_append, List.nil_append] using fetched)
    exact evaluated

end Solcore.Frontend.RustHull.AccountLifecycleCorrespondence
