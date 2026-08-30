import Solcore.Semantics.AccountNonceIncrementProperties
import Solcore.Semantics.CreationAddressPolicy

/-! External compile and executable checks for creation foundation APIs. -/

set_option autoImplicit false

namespace Tests.AccountNonceIncrementProperties

open Solcore
open Solcore.Semantics

example := @Account.incrementNonce?_isSome_iff
example := @Account.incrementNonce?_eq_none_iff
example := @Account.incrementNonce?_success_exact
example := @Account.incrementNonce?_maximum
example := @Account.incrementNonce?_preserves_payload
example := @Account.incrementNonce?_success_iff

private def word (value : Nat) (bound : value < Core.wordModulus := by decide) :
    Core.Word := ⟨value, bound⟩

private def policy : CreationAddressPolicy := {
  derive := fun creator nonce =>
    ⟨(creator.val + nonce.val) % addressModulus,
      Nat.mod_lt _ (by decide)⟩
}

private def creator : Address := ⟨7, by decide⟩

private theorem policyBoundaryCompiles :
    policy.derive creator (word 5) = ⟨12, by decide⟩ := by
  native_decide

private theorem checkedIncrementRunsExactly :
    (Account.empty.withNonce (word 5)).incrementNonce?.map Account.nonce =
      some (word 6) := by
  native_decide

private theorem maximumDoesNotWrap :
    (Account.empty.withNonce Core.Word.maximum).incrementNonce? = none := by
  native_decide

def testAccountNonceIncrement : IO Unit := do
  unless (Account.empty.withNonce (word 5)).incrementNonce?.map Account.nonce ==
      some (word 6) do
    throw (IO.userError "checked nonce increment did not return exact successor")
  unless (Account.empty.withNonce Core.Word.maximum).incrementNonce?.isNone do
    throw (IO.userError "maximum nonce wrapped instead of failing")

end Tests.AccountNonceIncrementProperties
