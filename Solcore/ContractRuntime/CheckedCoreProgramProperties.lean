import Solcore.ContractRuntime.CheckedCoreProgramExecution
import Solcore.Core.Safety

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
