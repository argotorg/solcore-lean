import Solcore.ContractRuntime.AccountBalanceProperties

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
