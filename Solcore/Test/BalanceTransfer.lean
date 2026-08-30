import Solcore.Core.Primitive
import Solcore.Semantics.BalanceTransfer

/-! Executable boundary tests for checked balance transfer. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Semantics

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def sender : Address := ⟨0, by decide⟩
private def recipient : Address := ⟨1, by decide⟩
private def absent : Address := ⟨2, by decide⟩

private def word (value : Nat) (inBounds : value < Core.wordModulus := by decide) :
    Core.Word :=
  ⟨value, inBounds⟩

private def accountWith (balance : Core.Word) : Account :=
  Account.empty.withBalance balance

private def worldWith
    (senderBalance recipientBalance : Core.Word) : WorldState :=
  (WorldState.empty.putAccount sender (accountWith senderBalance)).putAccount
    recipient (accountWith recipientBalance)

def testBalanceTransfer : IO Unit := do
  assertTrue
    (Balance.checkedDebit? (word 4) (word 5) == none)
    "checked debit must reject underflow"
  assertTrue
    (Balance.checkedDebit? (word 5) (word 4) == some (word 1))
    "checked debit must return the exact mathematical difference"
  assertTrue
    (Balance.checkedCredit? Core.Word.maximum (word 1) == none)
    "checked credit must reject 256-bit overflow"
  assertTrue
    (Balance.checkedCredit? (word 5) (word 4) == some (word 9))
    "checked credit must return the exact mathematical sum"

  let base := worldWith (word 10) (word 3)
  assertTrue
    (match base.transferBalance sender recipient (word 4) with
      | .ok next =>
          next.balance? sender == some (word 6) &&
            next.balance? recipient == some (word 7)
      | .error _ => false)
    "a valid transfer must debit and credit the exact endpoints"
  assertTrue
    (match base.transferBalance absent recipient (word 1) with
      | .error .senderAbsent => true
      | _ => false)
    "an absent sender must be reported without account creation"
  assertTrue
    (match base.transferBalance sender absent (word 1) with
      | .error .recipientAbsent => true
      | _ => false)
    "an absent recipient must be reported without account creation"
  assertTrue
    (match base.transferBalance sender recipient (word 11) with
      | .error .insufficientBalance => true
      | _ => false)
    "a transfer larger than the sender balance must fail"

  let overflowing := worldWith (word 10) Core.Word.maximum
  assertTrue
    (match overflowing.transferBalance sender recipient (word 1) with
      | .error .recipientOverflow => true
      | _ => false)
    "recipient overflow must fail instead of wrapping"
  assertTrue
    (match base.transferBalance sender recipient Core.Word.zero with
      | .ok next =>
          next.balance? sender == base.balance? sender &&
            next.balance? recipient == base.balance? recipient
      | .error _ => false)
    "a zero transfer between present accounts must be exact identity"
  assertTrue
    (match base.transferBalance sender sender (word 10) with
      | .ok next => next.balance? sender == base.balance? sender
      | .error _ => false)
    "a funded self transfer must be exact identity"
  assertTrue
    (match base.transferBalance recipient recipient (word 4) with
      | .error .insufficientBalance => true
      | _ => false)
    "a self transfer must still enforce sufficient balance"

end Tests
