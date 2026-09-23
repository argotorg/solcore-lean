import Solcore.ContractRuntime.WorldState
import Solcore.ContractRuntime.CheckedHostCoreProgram
import Solcore.ContractRuntime.Account

/-! Address-selected checked code lookup in explicit WorldState. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.WorldState

/-- Select host-checker-accepted code from the Account at one Address. -/
def code?
    (state : WorldState)
    (codeAddress : Address) : Option CheckedHostCoreProgram := do
  let account ← state.account? codeAddress
  account.code?

end Solcore.ContractRuntime.WorldState

/-!
## Consolidated module: `Solcore.ContractRuntime.WorldStateCodeExecution`
-/

/-! Address-selected execution until the first host boundary. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.WorldState

/-- Execute selected host-aware code until completion or its first boundary. -/
def runCode?
    (state : WorldState)
    (codeAddress : Address)
    (fuel : Nat) : Option Core.HostRunResult :=
  (state.code? codeAddress).map fun code => code.runStateful fuel

end Solcore.ContractRuntime.WorldState

/-!
## Consolidated module: `Solcore.ContractRuntime.WorldStateCodeProperties`
-/

/-! Lookup branches and finite-run safety for selected host-aware code. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.WorldState

@[simp] theorem code?_of_absent
    (state : WorldState)
    (codeAddress : Address)
    (absent : state.account? codeAddress = none) :
    state.code? codeAddress = none := by
  simp [code?, absent]

@[simp] theorem code?_of_account_without_code
    (state : WorldState)
    (codeAddress : Address)
    (account : Account)
    (present : state.account? codeAddress = some account)
    (withoutCode : account.code? = none) :
    state.code? codeAddress = none := by
  simp [code?, present, withoutCode]

@[simp] theorem code?_of_present
    (state : WorldState)
    (codeAddress : Address)
    (account : Account)
    (code : CheckedHostCoreProgram)
    (accountPresent : state.account? codeAddress = some account)
    (codePresent : account.code? = some code) :
    state.code? codeAddress = some code := by
  simp [code?, accountPresent, codePresent]

@[simp] theorem runCode?_of_absent
    (state : WorldState)
    (codeAddress : Address)
    (fuel : Nat)
    (absent : state.account? codeAddress = none) :
    state.runCode? codeAddress fuel = none := by
  simp [runCode?, code?, absent]

@[simp] theorem runCode?_of_account_without_code
    (state : WorldState)
    (codeAddress : Address)
    (account : Account)
    (fuel : Nat)
    (present : state.account? codeAddress = some account)
    (withoutCode : account.code? = none) :
    state.runCode? codeAddress fuel = none := by
  simp [runCode?, code?, present, withoutCode]

@[simp] theorem runCode?_of_present
    (state : WorldState)
    (codeAddress : Address)
    (account : Account)
    (code : CheckedHostCoreProgram)
    (fuel : Nat)
    (accountPresent : state.account? codeAddress = some account)
    (codePresent : account.code? = some code) :
    state.runCode? codeAddress fuel = some (code.runStateful fuel) := by
  simp [runCode?, code?, accountPresent, codePresent]

/-- Address-selected host-checked execution cannot return a machine fault. -/
theorem runCode?_ne_some_fault
    (state : WorldState)
    (codeAddress : Address)
    (fuel : Nat)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    state.runCode? codeAddress fuel ≠ some (.fault error faultState) := by
  unfold runCode?
  cases selected : state.code? codeAddress with
  | none => simp
  | some code =>
      intro same
      exact code.runStateful_ne_fault fuel error faultState
        (Option.some.inj same)

end Solcore.ContractRuntime.WorldState

/-!
## Consolidated module: `Solcore.ContractRuntime.WorldStateCodeWriteProperties`
-/

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
