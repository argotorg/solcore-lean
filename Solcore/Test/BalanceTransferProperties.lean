import Solcore.ContractRuntime.BalanceTransfer

/-! External compile consumers for every public balance-transfer theorem. -/
set_option autoImplicit false

namespace Tests
open Solcore
open Solcore.ContractRuntime

example (balance amount result : Core.Word) :
    Balance.checkedDebit? balance amount = some result ↔
      amount.val ≤ balance.val ∧ result.val = balance.val - amount.val :=
  Balance.checkedDebit_eq_some_iff balance amount result

example (balance amount : Core.Word) :
    Balance.checkedDebit? balance amount = none ↔ balance.val < amount.val :=
  Balance.checkedDebit_eq_none_iff balance amount

example (balance amount result : Core.Word) :
    Balance.checkedCredit? balance amount = some result ↔
      balance.val + amount.val < Core.wordModulus ∧
        result.val = balance.val + amount.val :=
  Balance.checkedCredit_eq_some_iff balance amount result

example (balance amount : Core.Word) :
    Balance.checkedCredit? balance amount = none ↔
      Core.wordModulus ≤ balance.val + amount.val :=
  Balance.checkedCredit_eq_none_iff balance amount

example (state : WorldState) (sender recipient : Address) (amount : Core.Word)
    (h : state.account? sender = none) :
    state.transferBalance sender recipient amount = .error .senderAbsent :=
  WorldState.transferBalance_senderAbsent state sender recipient amount h

example (state : WorldState) (sender recipient : Address) (amount : Core.Word)
    (senderAccount : Account) (hs : state.account? sender = some senderAccount)
    (hr : state.account? recipient = none) :
    state.transferBalance sender recipient amount = .error .recipientAbsent :=
  WorldState.transferBalance_recipientAbsent state sender recipient amount
    senderAccount hs hr

example (state : WorldState) (sender recipient : Address) (amount : Core.Word)
    (senderAccount recipientAccount : Account)
    (hs : state.account? sender = some senderAccount)
    (hr : state.account? recipient = some recipientAccount)
    (h : senderAccount.balance.val < amount.val) :
    state.transferBalance sender recipient amount = .error .insufficientBalance :=
  WorldState.transferBalance_insufficient state sender recipient amount
    senderAccount recipientAccount hs hr h

example (state : WorldState) (sender recipient : Address)
    (senderAccount recipientAccount : Account)
    (hs : state.account? sender = some senderAccount)
    (hr : state.account? recipient = some recipientAccount) :
    state.transferBalance sender recipient Core.Word.zero = .ok state :=
  WorldState.transferBalance_zero state sender recipient senderAccount
    recipientAccount hs hr

example (state : WorldState) (address : Address) (amount : Core.Word)
    (account : Account) (hp : state.account? address = some account)
    (h : amount.val ≤ account.balance.val) :
    state.transferBalance address address amount = .ok state :=
  WorldState.transferBalance_self state address amount account hp h

example (state : WorldState) (sender recipient : Address) (amount : Core.Word)
    (senderAccount recipientAccount : Account)
    (hs : state.account? sender = some senderAccount)
    (hr : state.account? recipient = some recipientAccount)
    (sufficient : amount.val ≤ senderAccount.balance.val)
    (nonzero : amount ≠ Core.Word.zero) (different : sender ≠ recipient)
    (overflow : Core.wordModulus ≤ recipientAccount.balance.val + amount.val) :
    state.transferBalance sender recipient amount = .error .recipientOverflow :=
  WorldState.transferBalance_overflow state sender recipient amount senderAccount
    recipientAccount hs hr sufficient nonzero different overflow

example (state : WorldState) (sender recipient : Address) (amount : Core.Word)
    (senderAccount recipientAccount : Account)
    (hs : state.account? sender = some senderAccount)
    (hr : state.account? recipient = some recipientAccount)
    (debited credited : Core.Word)
    (hd : Balance.checkedDebit? senderAccount.balance amount = some debited)
    (hc : Balance.checkedCredit? recipientAccount.balance amount = some credited)
    (nonzero : amount ≠ Core.Word.zero) (different : sender ≠ recipient) :
    state.transferBalance sender recipient amount = .ok
      ((state.putAccount sender (senderAccount.withBalance debited)).putAccount
        recipient (recipientAccount.withBalance credited)) :=
  WorldState.transferBalance_cross_eq state sender recipient amount senderAccount
    recipientAccount hs hr debited credited hd hc nonzero different

example (state : WorldState) (sender recipient : Address)
    (senderAccount recipientAccount : Account) (debited credited : Core.Word)
    (different : sender ≠ recipient) :
    let next := (state.putAccount sender (senderAccount.withBalance debited)).putAccount
      recipient (recipientAccount.withBalance credited)
    next.balance? sender = some debited ∧ next.balance? recipient = some credited :=
  WorldState.transferBalance_cross_balances state sender recipient senderAccount
    recipientAccount debited credited different

example (state : WorldState) (sender recipient other : Address)
    (senderAccount recipientAccount : Account) (debited credited : Core.Word)
    (hos : other ≠ sender) (hor : other ≠ recipient) :
    ((state.putAccount sender (senderAccount.withBalance debited)).putAccount
      recipient (recipientAccount.withBalance credited)).account? other =
      state.account? other :=
  WorldState.transferBalance_cross_account_other state sender recipient other
    senderAccount recipientAccount debited credited hos hor

example (senderAccount recipientAccount : Account) (debited credited : Core.Word) :
    (senderAccount.withBalance debited).code? = senderAccount.code? ∧
      (∀ slot, (senderAccount.withBalance debited).storageValue? slot =
        senderAccount.storageValue? slot) ∧
      (recipientAccount.withBalance credited).code? = recipientAccount.code? ∧
      (∀ slot, (recipientAccount.withBalance credited).storageValue? slot =
        recipientAccount.storageValue? slot) :=
  WorldState.transferBalance_cross_preserves_payload senderAccount
    recipientAccount debited credited

example (senderBalance recipientBalance amount debited credited : Core.Word)
    (hd : Balance.checkedDebit? senderBalance amount = some debited)
    (hc : Balance.checkedCredit? recipientBalance amount = some credited) :
    debited.val + credited.val = senderBalance.val + recipientBalance.val :=
  WorldState.transferBalance_cross_conserves senderBalance recipientBalance
    amount debited credited hd hc

end Tests
