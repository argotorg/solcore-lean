import Solcore.ContractRuntime.WorldStateCodeExecution
import Solcore.ContractRuntime.CheckedHostCoreProgramProperties

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
