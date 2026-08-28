import Solcore.Semantics.WorldStateCodeExecution
import Solcore.Semantics.CheckedCoreProgramProperties

/-! Explicit lookup branches and execution safety for selected checked code. -/

set_option autoImplicit false

namespace Solcore.Semantics.WorldState

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
    (code : CheckedCoreProgram)
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
    (code : CheckedCoreProgram)
    (fuel : Nat)
    (accountPresent : state.account? codeAddress = some account)
    (codePresent : account.code? = some code) :
    state.runCode? codeAddress fuel = some (code.runStateful fuel) := by
  simp [runCode?, code?, accountPresent, codePresent]

/-- An exactly selected checked-code run cannot return a machine fault. -/
theorem runCode?_ne_some_fault
    (state : WorldState)
    (codeAddress : Address)
    (code : CheckedCoreProgram)
    (fuel : Nat)
    (selected : state.code? codeAddress = some code)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    state.runCode? codeAddress fuel ≠ some (.fault error faultState) := by
  rw [runCode?, selected]
  simpa using code.runStateful_ne_fault fuel error faultState

end Solcore.Semantics.WorldState
