import Solcore.ContractRuntime.Account
import Solcore.ContractRuntime.WorldState
import Solcore.ContractRuntime.WorldStateBalanceProperties
import Solcore.ContractRuntime.CheckedCoreContract
import Solcore.ContractRuntime.HostStorageAccountPresence
import Solcore.ContractRuntime.ContractCallFailure

/-! Checked, non-wrapping balance transfer between present accounts. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- Total failure reasons for a balance transfer. -/
inductive BalanceTransferFailure where
  | senderAbsent
  | recipientAbsent
  | insufficientBalance
  | recipientOverflow
  deriving Repr, BEq, DecidableEq

namespace Balance

/-- Subtract without wrapping at zero. -/
def checkedDebit?
    (balance amount : Core.Word) : Option Core.Word :=
  if _sufficient : amount.val ≤ balance.val then
    some ⟨balance.val - amount.val,
      Nat.lt_of_le_of_lt (Nat.sub_le balance.val amount.val) balance.isLt⟩
  else
    none

/-- Add without wrapping at the 256-bit word modulus. -/
def checkedCredit?
    (balance amount : Core.Word) : Option Core.Word :=
  Core.Word.ofNat? (balance.val + amount.val)

end Balance

namespace WorldState

/--
Transfer value between two explicitly present accounts.

Failure is total and leaves the caller's immutable input state available
unchanged. Missing accounts are not created; account creation is a separate
semantic operation. Zero and self transfers still require present accounts and
sufficient funds, then return the exact input state.
-/
def transferBalance
    (state : WorldState)
    (sender recipient : Address)
    (amount : Core.Word) : Except BalanceTransferFailure WorldState :=
  match state.account? sender with
  | none => .error .senderAbsent
  | some senderAccount =>
      match state.account? recipient with
      | none => .error .recipientAbsent
      | some recipientAccount =>
          match Balance.checkedDebit? senderAccount.balance amount with
          | none => .error .insufficientBalance
          | some debited =>
              if _zero : amount = Core.Word.zero then
                .ok state
              else if _same : sender = recipient then
                .ok state
              else
                match Balance.checkedCredit? recipientAccount.balance amount with
                | none => .error .recipientOverflow
                | some credited =>
                    .ok <|
                      (state.putAccount sender
                          (senderAccount.withBalance debited)).putAccount
                        recipient (recipientAccount.withBalance credited)

end WorldState

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.BalanceTransferProperties`
-/

/-! Exact arithmetic and frame properties of checked balance transfer. -/
set_option autoImplicit false

namespace Solcore.ContractRuntime
namespace Balance

theorem checkedDebit_eq_some_iff (balance amount result : Core.Word) :
    checkedDebit? balance amount = some result ↔
      amount.val ≤ balance.val ∧ result.val = balance.val - amount.val := by
  unfold checkedDebit?
  split
  · constructor
    · intro h; injection h with h
      exact ⟨by assumption, congrArg Fin.val h.symm⟩
    · rintro ⟨_, h⟩
      apply congrArg some
      apply Fin.ext
      exact h.symm
  · constructor
    · simp
    · intro facts
      omega

theorem checkedDebit_eq_none_iff (balance amount : Core.Word) :
    checkedDebit? balance amount = none ↔ balance.val < amount.val := by
  unfold checkedDebit?; split <;> simp_all

theorem checkedCredit_eq_some_iff (balance amount result : Core.Word) :
    checkedCredit? balance amount = some result ↔
      balance.val + amount.val < Core.wordModulus ∧
        result.val = balance.val + amount.val := by
  unfold checkedCredit? Core.Word.ofNat?
  split
  · constructor
    · intro h; injection h with h
      exact ⟨by assumption, congrArg Fin.val h.symm⟩
    · rintro ⟨_, h⟩
      apply congrArg some
      apply Fin.ext
      exact h.symm
  · constructor
    · simp
    · intro facts
      omega

theorem checkedCredit_eq_none_iff (balance amount : Core.Word) :
    checkedCredit? balance amount = none ↔
      Core.wordModulus ≤ balance.val + amount.val := by
  unfold checkedCredit? Core.Word.ofNat?; split <;> simp_all

end Balance
namespace WorldState

theorem transferBalance_senderAbsent (state : WorldState)
    (sender recipient : Address) (amount : Core.Word)
    (h : state.account? sender = none) :
    state.transferBalance sender recipient amount = .error .senderAbsent := by
  simp [transferBalance, h]

theorem transferBalance_recipientAbsent (state : WorldState)
    (sender recipient : Address) (amount : Core.Word) (senderAccount : Account)
    (hs : state.account? sender = some senderAccount)
    (hr : state.account? recipient = none) :
    state.transferBalance sender recipient amount = .error .recipientAbsent := by
  simp [transferBalance, hs, hr]

theorem transferBalance_insufficient (state : WorldState)
    (sender recipient : Address) (amount : Core.Word)
    (senderAccount recipientAccount : Account)
    (hs : state.account? sender = some senderAccount)
    (hr : state.account? recipient = some recipientAccount)
    (h : senderAccount.balance.val < amount.val) :
    state.transferBalance sender recipient amount = .error .insufficientBalance := by
  have hd := (Balance.checkedDebit_eq_none_iff senderAccount.balance amount).2 h
  rw [transferBalance]; simp [hs, hr, hd]

theorem transferBalance_zero (state : WorldState) (sender recipient : Address)
    (senderAccount recipientAccount : Account)
    (hs : state.account? sender = some senderAccount)
    (hr : state.account? recipient = some recipientAccount) :
    state.transferBalance sender recipient Core.Word.zero = .ok state := by
  rw [transferBalance]; simp only [hs, hr]
  have hd : Balance.checkedDebit? senderAccount.balance Core.Word.zero =
      some senderAccount.balance := by
    apply (Balance.checkedDebit_eq_some_iff _ _ _).2
    change 0 ≤ senderAccount.balance.val ∧
      senderAccount.balance.val = senderAccount.balance.val - 0
    omega
  simp [hd]

theorem transferBalance_self (state : WorldState) (address : Address)
    (amount : Core.Word) (account : Account)
    (hp : state.account? address = some account)
    (h : amount.val ≤ account.balance.val) :
    state.transferBalance address address amount = .ok state := by
  rw [transferBalance]; simp only [hp]
  unfold Balance.checkedDebit?; simp [h]

theorem transferBalance_overflow (state : WorldState)
    (sender recipient : Address) (amount : Core.Word)
    (senderAccount recipientAccount : Account)
    (hs : state.account? sender = some senderAccount)
    (hr : state.account? recipient = some recipientAccount)
    (sufficient : amount.val ≤ senderAccount.balance.val)
    (nonzero : amount ≠ Core.Word.zero) (different : sender ≠ recipient)
    (overflow : Core.wordModulus ≤ recipientAccount.balance.val + amount.val) :
    state.transferBalance sender recipient amount = .error .recipientOverflow := by
  rw [transferBalance]; simp only [hs, hr]
  unfold Balance.checkedDebit?
  have hc := (Balance.checkedCredit_eq_none_iff recipientAccount.balance amount).2
    overflow
  simp [sufficient, nonzero, different, hc]

theorem transferBalance_cross_eq (state : WorldState)
    (sender recipient : Address) (amount : Core.Word)
    (senderAccount recipientAccount : Account)
    (hs : state.account? sender = some senderAccount)
    (hr : state.account? recipient = some recipientAccount)
    (debited credited : Core.Word)
    (hd : Balance.checkedDebit? senderAccount.balance amount = some debited)
    (hc : Balance.checkedCredit? recipientAccount.balance amount = some credited)
    (nonzero : amount ≠ Core.Word.zero) (different : sender ≠ recipient) :
    state.transferBalance sender recipient amount = .ok
      ((state.putAccount sender (senderAccount.withBalance debited)).putAccount
        recipient (recipientAccount.withBalance credited)) := by
  simp [transferBalance, hs, hr, hd, hc, nonzero, different]

theorem transferBalance_cross_balances (state : WorldState)
    (sender recipient : Address) (senderAccount recipientAccount : Account)
    (debited credited : Core.Word) (different : sender ≠ recipient) :
    let next := (state.putAccount sender (senderAccount.withBalance debited)).putAccount
      recipient (recipientAccount.withBalance credited)
    next.balance? sender = some debited ∧ next.balance? recipient = some credited := by
  dsimp; constructor
  · rw [balance?_putAccount_other _ recipient sender _ different]; simp
  · simp

theorem transferBalance_cross_account_other (state : WorldState)
    (sender recipient other : Address) (senderAccount recipientAccount : Account)
    (debited credited : Core.Word) (hos : other ≠ sender) (hor : other ≠ recipient) :
    ((state.putAccount sender (senderAccount.withBalance debited)).putAccount
      recipient (recipientAccount.withBalance credited)).account? other =
      state.account? other := by
  rw [account?_putAccount_other _ recipient other _ hor]
  rw [account?_putAccount_other _ sender other _ hos]

theorem transferBalance_cross_preserves_payload
    (senderAccount recipientAccount : Account) (debited credited : Core.Word) :
    (senderAccount.withBalance debited).code? = senderAccount.code? ∧
      (∀ slot, (senderAccount.withBalance debited).storageValue? slot =
        senderAccount.storageValue? slot) ∧
      (recipientAccount.withBalance credited).code? = recipientAccount.code? ∧
      (∀ slot, (recipientAccount.withBalance credited).storageValue? slot =
        recipientAccount.storageValue? slot) := by simp

theorem transferBalance_cross_conserves
    (senderBalance recipientBalance amount debited credited : Core.Word)
    (hd : Balance.checkedDebit? senderBalance amount = some debited)
    (hc : Balance.checkedCredit? recipientBalance amount = some credited) :
    debited.val + credited.val = senderBalance.val + recipientBalance.val := by
  have hd' := (Balance.checkedDebit_eq_some_iff _ _ _).1 hd
  have hc' := (Balance.checkedCredit_eq_some_iff _ _ _).1 hc
  omega

end WorldState
end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.BalanceTransferInstallationProperties`
-/

/-! Checked contract installation survives balance-only state transitions. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.WorldState

/-- A successful balance transfer preserves every installed checked contract. -/
def transferBalance_preserves_installed
    {state next : WorldState}
    {sender recipient target : Address}
    {amount : Core.Word}
    {contract : CheckedCoreContract}
    (success : state.transferBalance sender recipient amount = .ok next)
    (installed : InstalledCheckedCoreContract state target contract) :
    InstalledCheckedCoreContract next target contract := by
  unfold transferBalance at success
  split at success
  · contradiction
  · rename_i senderAccount senderPresent
    split at success
    · contradiction
    · rename_i recipientAccount recipientPresent
      split at success
      · contradiction
      · rename_i debited debitPresent
        split at success
        · cases success
          exact installed
        · rename_i nonzero
          split at success
          · cases success
            exact installed
          · rename_i different
            split at success
            · contradiction
            · rename_i credited creditPresent
              injection success with nextEq
              subst next
              have payload := transferBalance_cross_preserves_payload
                senderAccount recipientAccount debited credited
              by_cases targetRecipient : target = recipient
              · subst target
                have accountEq : installed.account = recipientAccount := by
                  exact Option.some.inj
                    (installed.account_present.symm.trans recipientPresent)
                refine {
                  account := recipientAccount.withBalance credited
                  account_present := ?_
                  code_present := ?_
                }
                · exact account?_putAccount_same _ _ _
                · calc
                    (recipientAccount.withBalance credited).code? =
                        recipientAccount.code? := payload.2.2.1
                    _ = installed.account.code? := by rw [accountEq]
                    _ = some contract.code := installed.code_present
              · by_cases targetSender : target = sender
                · subst target
                  have accountEq : installed.account = senderAccount := by
                    exact Option.some.inj
                      (installed.account_present.symm.trans senderPresent)
                  refine {
                    account := senderAccount.withBalance debited
                    account_present := ?_
                    code_present := ?_
                  }
                  · rw [account?_putAccount_other _ recipient sender _ different]
                    exact account?_putAccount_same _ _ _
                  · calc
                      (senderAccount.withBalance debited).code? =
                          senderAccount.code? := payload.1
                      _ = installed.account.code? := by rw [accountEq]
                      _ = some contract.code := installed.code_present
                · refine {
                    account := installed.account
                    account_present := ?_
                    code_present := installed.code_present
                  }
                  rw [transferBalance_cross_account_other state sender recipient
                    target senderAccount recipientAccount debited credited
                    targetSender targetRecipient]
                  exact installed.account_present

end Solcore.ContractRuntime.WorldState

/-!
## Consolidated module: `Solcore.ContractRuntime.BalanceTransferPresenceProperties`
-/

/-! Account presence survives successful balance-only transitions. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.WorldState

def transferBalance_preserves_present
    {state next : WorldState}
    {sender recipient target : Address}
    {amount : Core.Word}
    (success : state.transferBalance sender recipient amount = .ok next)
    (present : PresentAccountAt state target) :
    PresentAccountAt next target := by
  unfold transferBalance at success
  split at success
  · contradiction
  · rename_i senderAccount senderPresent
    split at success
    · contradiction
    · rename_i recipientAccount recipientPresent
      split at success
      · contradiction
      · rename_i debited debitPresent
        split at success
        · cases success
          exact present
        · rename_i nonzero
          split at success
          · cases success
            exact present
          · rename_i different
            split at success
            · contradiction
            · rename_i credited creditPresent
              injection success with nextEq
              subst next
              by_cases targetRecipient : target = recipient
              · subst target
                exact ⟨recipientAccount.withBalance credited,
                  account?_putAccount_same _ _ _⟩
              · by_cases targetSender : target = sender
                · subst target
                  refine ⟨senderAccount.withBalance debited, ?_⟩
                  rw [account?_putAccount_other _ recipient sender _ different]
                  exact account?_putAccount_same _ _ _
                · refine ⟨present.account, ?_⟩
                  rw [transferBalance_cross_account_other state sender recipient
                    target senderAccount recipientAccount debited credited
                    targetSender targetRecipient]
                  exact present.present

end Solcore.ContractRuntime.WorldState

/-!
## Consolidated module: `Solcore.ContractRuntime.BalanceTransferCallFailure`
-/

/-! Stable checked-call failures for total balance-transfer failures. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

namespace BalanceTransferFailure

/-- Translate every checked transfer failure into the public call failure ABI. -/
def toContractCallFailure : BalanceTransferFailure → ContractCallFailure
  | .senderAbsent => .unavailable
  | .recipientAbsent => .unavailable
  | .insufficientBalance => .insufficientBalance
  | .recipientOverflow => .balanceOverflow

/-- Inject a checked transfer failure into the typed contract-call result. -/
def toContractCallResult
    (failure : BalanceTransferFailure) : Core.ContractCallWordResult :=
  failure.toContractCallFailure.result

end BalanceTransferFailure

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.BalanceTransferCallFailureProperties`
-/

/-! Exact failure translation laws for value-bearing checked calls. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.BalanceTransferFailure

@[simp] theorem toContractCallFailure_senderAbsent :
    senderAbsent.toContractCallFailure = .unavailable :=
  rfl

@[simp] theorem toContractCallFailure_recipientAbsent :
    recipientAbsent.toContractCallFailure = .unavailable :=
  rfl

@[simp] theorem toContractCallFailure_insufficientBalance :
    insufficientBalance.toContractCallFailure = .insufficientBalance :=
  rfl

@[simp] theorem toContractCallFailure_recipientOverflow :
    recipientOverflow.toContractCallFailure = .balanceOverflow :=
  rfl

@[simp] theorem toContractCallResult_code (failure : BalanceTransferFailure) :
    failure.toContractCallResult =
      .failed failure.toContractCallFailure.code :=
  rfl

end Solcore.ContractRuntime.BalanceTransferFailure
