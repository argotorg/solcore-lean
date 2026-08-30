import Solcore.Semantics.HostDriverCompletenessProperties
import Solcore.Semantics.HostDriverResumptionProperties
import Solcore.Semantics.TransactionHostStorageDriverProperties

/-! Exact fuel continuation laws for transaction storage execution. -/

set_option autoImplicit false

namespace Solcore.Semantics

namespace TransactionHostStorageDriver

/-- Exhaustion resumes with the exact retained transaction context. -/
theorem run_additional_of_outOfFuel
    (context nextContext : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel additional : Nat)
    (state exhausted : Core.State)
    (execution :
      run context inputs fuel state =
        ⟨nextContext, .outOfFuel exhausted⟩) :
    run context inputs (fuel + additional) state =
      run nextContext inputs additional exhausted := by
  simpa only [run] using
    HostDriver.run_additional_of_outOfFuel
      (handler inputs) execution

/-- Split execution and a single summed-budget run retain identical journals. -/
theorem resumeWithFuel_run
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel additional : Nat)
    (state : Core.State) :
    (run context inputs fuel state).resumeWithFuel
        (handler inputs) additional =
      run context inputs (fuel + additional) state := by
  simpa only [run] using
    HostDriverResult.resumeWithFuel_run
      (handler inputs) context fuel additional state

/-- A completed transaction run is stable under a larger fuel budget. -/
theorem run_done_stable
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel largerFuel : Nat}
    (state : Core.State)
    {finalContext : Context}
    {value : Core.Value} {store : Core.Store}
    (execution :
      run context inputs fuel state =
        ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    run context inputs largerFuel state =
      ⟨finalContext, .done value store⟩ := by
  simpa only [run] using
    HostDriver.run_done_stable (handler inputs) execution more

end TransactionHostStorageDriver

namespace CheckedHostCoreProgram

theorem runWithTransactionStorage_done_stable
    (code : CheckedHostCoreProgram)
    (context : TransactionHostStorageDriver.Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel largerFuel : Nat}
    {finalContext : TransactionHostStorageDriver.Context}
    {value : Core.Value} {store : Core.Store}
    (execution :
      code.runWithTransactionStorage context inputs fuel =
        ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    code.runWithTransactionStorage context inputs largerFuel =
      ⟨finalContext, .done value store⟩ := by
  simpa only [runWithTransactionStorage] using
    TransactionHostStorageDriver.run_done_stable context inputs
      (Core.State.initial code.program.body Core.hostEnvironment)
      execution more

/-- Checked transaction execution has the exact additive resumption law. -/
theorem runWithTransactionStorage_resumeWithFuel
    (code : CheckedHostCoreProgram)
    (context : TransactionHostStorageDriver.Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel additional : Nat) :
    (code.runWithTransactionStorage context inputs fuel).resumeWithFuel
        (TransactionHostStorageDriver.handler inputs) additional =
      code.runWithTransactionStorage context inputs (fuel + additional) := by
  simpa only [runWithTransactionStorage] using
    TransactionHostStorageDriver.resumeWithFuel_run context inputs
      fuel additional
      (Core.State.initial code.program.body Core.hostEnvironment)

end CheckedHostCoreProgram

end Solcore.Semantics
