import Solcore.Semantics.BalanceTransfer
import Solcore.Semantics.WorldStateExtensionalityProperties
import Solcore.Semantics.WorldStateBalanceProperties

/-! Exact arithmetic and frame properties of checked balance transfer. -/
set_option autoImplicit false

namespace Solcore.Semantics
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
end Solcore.Semantics
