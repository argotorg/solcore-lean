import Solcore.ContractRuntime.AccountBalanceProperties
import Solcore.ContractRuntime.AccountNonceProperties
import Solcore.ContractRuntime.WorldStateCodeProperties
import Solcore.ContractRuntime.WorldStateProperties

/-! Exact laws for replacing checked code on one present Account. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.WorldState

@[simp] theorem writeCode?_of_absent
    (state : WorldState) (address : Address)
    (code : CheckedHostCoreProgram)
    (absent : state.account? address = none) :
    state.writeCode? address code = none := by
  simp [writeCode?, absent]

@[simp] theorem writeCode?_of_present
    (state : WorldState) (address : Address)
    (account : Account) (code : CheckedHostCoreProgram)
    (present : state.account? address = some account) :
    state.writeCode? address code =
      some (state.putAccount address (account.withCode code)) := by
  simp [writeCode?, present]

theorem account?_writeCode?_same
    (state : WorldState) (address : Address)
    (account : Account) (code : CheckedHostCoreProgram)
    (present : state.account? address = some account) :
    (state.writeCode? address code).bind
        (fun next => next.account? address) =
      some (account.withCode code) := by
  rw [writeCode?_of_present state address account code present]
  exact account?_putAccount_same state address (account.withCode code)

theorem code?_writeCode?_same
    (state : WorldState) (address : Address)
    (account : Account) (code : CheckedHostCoreProgram)
    (present : state.account? address = some account) :
    (state.writeCode? address code).bind
        (fun next => next.code? address) = some code := by
  rw [writeCode?_of_present state address account code present]
  simp only [Option.bind_some]
  apply code?_of_present
  · exact account?_putAccount_same _ _ _
  · exact Account.code?_withCode _ _

theorem account?_writeCode?_other
    (state : WorldState) (address other : Address)
    (account : Account) (code : CheckedHostCoreProgram)
    (present : state.account? address = some account)
    (different : other ≠ address) :
    (state.writeCode? address code).bind
        (fun next => next.account? other) = state.account? other := by
  rw [writeCode?_of_present state address account code present]
  exact account?_putAccount_other state address other
    (account.withCode code) different

theorem writeCode?_preserves_payload
    (state : WorldState) (address : Address)
    (account : Account) (code : CheckedHostCoreProgram)
    (present : state.account? address = some account) :
    (state.writeCode? address code).bind (fun next =>
        (next.account? address).map fun updated =>
          (updated.balance, updated.nonce,
            fun slot => updated.storageValue? slot)) =
      some (account.balance, account.nonce,
        fun slot => account.storageValue? slot) := by
  rw [writeCode?_of_present state address account code present]
  simp only [Option.bind_some, account?_putAccount_same, Option.map_some]
  simp

end Solcore.ContractRuntime.WorldState
