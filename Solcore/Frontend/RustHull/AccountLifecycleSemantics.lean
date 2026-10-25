import Solcore.Frontend.RustHull.StorageSemantics

/-! Independent account destruction. Balances move immediately, while account
removal is delayed until successful transaction finalization. Code identities
and Core evaluation do not occur in this description. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountLifecycleSemantics
open Core
open StorageSemantics (World Words readWord writeWord)

def address (value : Word) : Word := value.bitAnd (Word.ofNatModulo (2 ^ 160 - 1))

/-- A zero transfer retains the original ordered ledger. A newly created
account burns its balance when it names itself; an existing account keeps it. -/
def balances (created : Bool) (current beneficiary : Word) (initial : Words) : Except Word Words :=
  let amount := readWord current initial
  if current == beneficiary then
    if created then
      if amount == Word.zero then .ok initial else .ok (writeWord current Word.zero initial)
    else .ok initial
  else if amount == Word.zero then .ok initial
  else
    let recipient := readWord beneficiary initial
    if recipient > Word.maximum.sub amount then .error (Word.ofNatModulo 12)
    else .ok (writeWord beneficiary (recipient.add amount) (writeWord current Word.zero initial))

def publish (world : World) (current : Word) (account : AccountState.Account) : World :=
  if account.created then StorageSemantics.put current {account with destroyed := true} world else world

/-- Missing current accounts are errors in incomplete worlds. Beneficiaries
need only a ledger entry, with an absent balance interpreted as zero. Failed
lookups and overflowing credits make no account or balance update. -/
def destroy (world : World) (initial : Words) (current beneficiary : Word) (complete : Bool) :
    Except Word (World × Words) := do
  let current := address current
  let beneficiary := address beneficiary
  let account ← StorageSemantics.get world current complete
  let next ← balances account.created current beneficiary initial
  return (publish world current account, next)

end Solcore.Frontend.RustHull.AccountLifecycleSemantics
