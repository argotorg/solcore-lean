import Solcore.ContractRuntime.AccountNonceIncrement
import Solcore.ContractRuntime.AccountNonceProperties

/-! Exact arithmetic and payload laws for checked nonce increment. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.Account

theorem incrementNonce?_isSome_iff (account : Account) :
    account.incrementNonce?.isSome ↔
      account.nonce.val + 1 < Core.wordModulus := by
  unfold incrementNonce? Core.Word.ofNat?
  split <;> simp_all

theorem incrementNonce?_eq_none_iff (account : Account) :
    account.incrementNonce? = none ↔
      Core.wordModulus ≤ account.nonce.val + 1 := by
  simp [incrementNonce?, Core.Word.ofNat?, Nat.not_lt]

theorem incrementNonce?_success_exact
    (account next : Account)
    (success : account.incrementNonce? = some next) :
    next.nonce.val = account.nonce.val + 1 := by
  unfold incrementNonce? Core.Word.ofNat? at success
  split at success
  · injection success with equal
    subst next
    simp
  · contradiction

@[simp] theorem incrementNonce?_maximum (account : Account) :
    (account.withNonce Core.Word.maximum).incrementNonce? = none := by
  apply (incrementNonce?_eq_none_iff _).2
  change Core.wordModulus ≤ (Core.wordModulus - 1) + 1
  omega

theorem incrementNonce?_preserves_payload
    (account next : Account)
    (success : account.incrementNonce? = some next) :
    next.balance = account.balance ∧
      next.code? = account.code? ∧
      ∀ slot, next.storageValue? slot = account.storageValue? slot := by
  unfold incrementNonce? Core.Word.ofNat? at success
  split at success
  · injection success with equal
    subst next
    simp
  · contradiction

theorem incrementNonce?_success_iff (account : Account) :
    (∃ next, account.incrementNonce? = some next ∧
      next.nonce.val = account.nonce.val + 1) ↔
      account.nonce.val + 1 < Core.wordModulus := by
  constructor
  · rintro ⟨next, success, _⟩
    exact (incrementNonce?_isSome_iff account).1 (by simp [success])
  · intro inBounds
    let nextNonce : Core.Word := ⟨account.nonce.val + 1, inBounds⟩
    refine ⟨account.withNonce nextNonce, ?_, ?_⟩
    · simp [incrementNonce?, Core.Word.ofNat?, inBounds, nextNonce]
    · simp [nextNonce]

end Solcore.ContractRuntime.Account
