import Solcore.Core.Host
import Solcore.Core.HostRunner

/-! Checker-accepted Core programs under the fixed host capability context. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

structure CheckedHostCoreProgram where
  program : Core.Program
  checked : program.checkHost = true

namespace CheckedHostCoreProgram

def ofProgram? (program : Core.Program) : Option CheckedHostCoreProgram :=
  if checked : program.checkHost = true then
    some ⟨program, checked⟩
  else
    none

@[simp] theorem ofProgram?_of_checked
    (program : Core.Program)
    (checked : program.checkHost = true) :
    ofProgram? program = some ⟨program, checked⟩ := by
  simp [ofProgram?, checked]

@[simp] theorem ofProgram?_of_rejected
    (program : Core.Program)
    (rejected : program.checkHost = false) :
    ofProgram? program = none := by
  simp [ofProgram?, rejected]

end CheckedHostCoreProgram

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedHostCoreProgramExecution`
-/

/-! Interactive execution for programs checked in the fixed host context. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.CheckedHostCoreProgram

def runStateful
    (code : CheckedHostCoreProgram)
    (fuel : Nat) : Core.HostRunResult :=
  code.program.runHostStateful fuel

end Solcore.ContractRuntime.CheckedHostCoreProgram

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedHostCoreProgramProperties`
-/

/-! Admission and initial-state typing for checker-accepted host-aware Core code. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.CheckedHostCoreProgram

/-- The fixed runtime capability environment realizes the context used by the
host checker. -/
theorem initialState_hasType
    (code : CheckedHostCoreProgram) :
    Core.HostStateHasType
      (Core.State.initial code.program.body Core.hostEnvironment)
      code.program.resultType code.program.dataDefinitions :=
  .eval .nil
    (Core.hostEnvironment_hasTypes [] code.program.dataDefinitions)
    (Core.Program.checkHost_sound code.checked) .nil

/-- Every finite host-aware run has a typed non-fault result. -/
theorem runStateful_hasType
    (code : CheckedHostCoreProgram)
    (fuel : Nat) :
    Core.HostRunResult.HasType (code.runStateful fuel)
      code.program.resultType code.program.dataDefinitions := by
  simpa [runStateful, Core.Program.runHostStateful] using
    Core.hostRun_hasType fuel code.initialState_hasType

theorem runStateful_ne_fault
    (code : CheckedHostCoreProgram)
    (fuel : Nat)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    code.runStateful fuel ≠ .fault error faultState := by
  simpa [runStateful, Core.Program.runHostStateful] using
    Core.hostRun_never_faults
      (fuel := fuel) (faultState := faultState) (error := error)
      code.initialState_hasType

theorem runStateful_done_hasType
    (code : CheckedHostCoreProgram)
    {fuel : Nat} {value : Core.Value} {store : Core.Store}
    (result : code.runStateful fuel = .done value store) :
    ∃ world,
      Core.StoreHasTypes world store ∧
        Core.HostRuntimeValueHasType world value code.program.resultType
          code.program.dataDefinitions := by
  apply Core.hostRun_done_hasType code.initialState_hasType
  simpa [runStateful, Core.Program.runHostStateful] using result

theorem runStateful_outOfFuel_hasType
    (code : CheckedHostCoreProgram)
    {fuel : Nat} {state : Core.State}
    (result : code.runStateful fuel = .outOfFuel state) :
    Core.HostStateHasType state code.program.resultType
      code.program.dataDefinitions := by
  apply Core.hostRun_outOfFuel_hasType code.initialState_hasType
  simpa [runStateful, Core.Program.runHostStateful] using result

theorem runStateful_suspended_hasType
    (code : CheckedHostCoreProgram)
    {fuel remainingFuel : Nat} {suspension : Core.HostSuspension}
    (result : code.runStateful fuel = .suspended suspension remainingFuel) :
    Core.HostSuspensionHasType suspension code.program.resultType
      code.program.dataDefinitions := by
  apply Core.hostRun_suspended_hasType code.initialState_hasType
  simpa [runStateful, Core.Program.runHostStateful] using result

end Solcore.ContractRuntime.CheckedHostCoreProgram
