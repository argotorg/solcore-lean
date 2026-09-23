import Solcore.ContractRuntime.WorldState

/-! Checked, non-wrapping account nonce increment. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.Account

/-- Increment the nonce exactly once, failing instead of wrapping at 2^256. -/
def incrementNonce? (account : Account) : Option Account := do
  let next ← Core.Word.ofNat? (account.nonce.val + 1)
  some (account.withNonce next)

end Solcore.ContractRuntime.Account
