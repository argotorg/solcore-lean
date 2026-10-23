import Solcore.Frontend.RustHull.AccountState

/-! SELFDESTRUCT account updates for the Osaka/EIP-6780 model. Account removal
belongs to transaction finalization. Code, nonce and storage remain observable
after a child frame schedules an account for removal. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountLifecycle
open Core CodeBuilder

def definitions : DataEnvironment := AccountState.definitions
def balanceOverflowReason : Word := Word.ofNatModulo 12

private def publish (world balances current record nextBalances : Code) : Code :=
  choose (part 7 9 record)
    (bindResult .unit (fun depth => AccountState.put (load world depth) (current depth)
      (AccountState.replace (record depth) 8 (.bool true))) fun nextWorld =>
      bind (store balances nextBalances) fun _ => success (store world nextWorld))
    (success (store balances nextBalances))

/-- Transfer the complete balance, or burn it for a newly created account
whose beneficiary is itself. Existing accounts retain their balance for that
self-beneficiary case. Only accounts created in this transaction acquire the
pending-removal flag. The complete-world flag is used only for the current
record; beneficiary balances come from the explicit ledger with zero on miss.
All checked updates precede the two externally visible cell stores. -/
def destroy (worldReference balancesReference currentAddress beneficiary complete : Core.Expr) : Core.Expr :=
  (bind (constant (bundle [worldReference, balancesReference, currentAddress, beneficiary, complete])) fun args =>
    let world := part 0 5 args
    let balances := part 1 5 args
    bind (address (part 2 5 args)) fun current =>
    bind (address (part 3 5 args)) fun recipient =>
    bindResult .unit (fun depth => AccountState.get (load world depth) (current depth)
      (part 4 5 args depth)) fun record =>
    let finish := publish world balances current record
    bindResult .unit (lookup (load balances) current) fun amount =>
    choose (binary .wordEq current recipient)
      (choose (part 7 9 record)
        (choose (binary .wordEq amount (number 0)) (finish (load balances))
          (bindResult .unit (insert (load balances) current (number 0)) finish))
        (success unit))
      (choose (binary .wordEq amount (number 0)) (finish (load balances))
        (bindResult .unit (lookup (load balances) recipient) fun recipientBalance =>
          choose (binary .wordGt recipientBalance (binary .wordSub (number (wordModulus - 1)) amount))
            (failure .unit (constant (.word balanceOverflowReason)))
            (bindResult .unit (insert (load balances) current (number 0)) fun debited =>
              bindResult .unit (insert debited recipient (binary .wordAdd recipientBalance amount)) finish)))) 0

end Solcore.Frontend.RustHull.AccountLifecycle
