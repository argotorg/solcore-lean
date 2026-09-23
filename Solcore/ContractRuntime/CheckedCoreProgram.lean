import Solcore.Core.Typing
import Solcore.Core.Machine
import Solcore.Core.Safety
import Solcore.ContractRuntime.CheckedHostCoreProgram

/-! Checker-accepted closed Core programs retained by contract semantics. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- A closed Core program together with its executable checker evidence. -/
structure CheckedCoreProgram where
  program : Core.Program
  checked : program.check = true

namespace CheckedCoreProgram

/-- Admit exactly the programs accepted by the existing Core checker. -/
def ofProgram? (program : Core.Program) : Option CheckedCoreProgram :=
  if checked : program.check = true then
    some ⟨program, checked⟩
  else
    none

end CheckedCoreProgram

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedCoreProgramExecution`
-/

/-! Stateful Core-machine execution for checker-accepted programs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.CheckedCoreProgram

/-- Execute retained Core code without erasing its final Core-local store. -/
def runStateful
    (code : CheckedCoreProgram)
    (fuel : Nat) : Core.StatefulRunResult :=
  code.program.runStateful fuel

end Solcore.ContractRuntime.CheckedCoreProgram

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedCoreProgramProperties`
-/

/-! Admission and machine-safety laws for checker-accepted Core programs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.CheckedCoreProgram

@[simp] theorem ofProgram?_of_checked
    (program : Core.Program)
    (checked : program.check = true) :
    ofProgram? program = some ⟨program, checked⟩ := by
  simp [ofProgram?, checked]

@[simp] theorem ofProgram?_of_rejected
    (program : Core.Program)
    (rejected : program.check = false) :
    ofProgram? program = none := by
  simp [ofProgram?, rejected]

/-- Every retained non-recursive Core program completes above some fuel bound. -/
theorem runStateful_has_sufficient_fuel
    (code : CheckedCoreProgram) :
    ∃ required storeTyping finalStore value,
      Core.StoreHasTypes storeTyping finalStore ∧
      Core.RuntimeValueHasType storeTyping value code.program.resultType
        code.program.dataDefinitions ∧
      ∀ fuel, required ≤ fuel →
        code.runStateful fuel = .done value finalStore := by
  simpa [runStateful] using
    Core.Program.checked_runStateful_has_sufficient_fuel code.checked

/-- Checker-accepted Core execution cannot produce a machine fault. -/
theorem runStateful_ne_fault
    (code : CheckedCoreProgram)
    (fuel : Nat)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    code.runStateful fuel ≠ .fault error faultState :=
  Core.Program.checked_runStateful_never_faults code.checked

end Solcore.ContractRuntime.CheckedCoreProgram

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedCoreProgramHostPromotion`
-/

/-! Explicit promotion of closed checked code to the host-aware carrier. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

namespace CheckedCoreProgram

/-- Retain the exact program while admitting its unused host environment. -/
def toHost (code : CheckedCoreProgram) : CheckedHostCoreProgram :=
  ⟨code.program, Core.Program.checkHost_of_check code.checked⟩

@[simp] theorem toHost_program
    (code : CheckedCoreProgram) :
    code.toHost.program = code.program :=
  rfl

end CheckedCoreProgram

end Solcore.ContractRuntime
