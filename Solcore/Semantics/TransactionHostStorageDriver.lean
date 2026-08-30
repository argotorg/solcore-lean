import Solcore.Semantics.CheckedHostCoreProgramExecution
import Solcore.Semantics.HostDriver
import Solcore.Semantics.TransactionHostStorageHandler

/-! Canonical driver for observable transaction storage execution. -/

set_option autoImplicit false

namespace Solcore.Semantics

namespace TransactionHostStorageDriver

/-- Run Core while preserving and extending the active transaction journal. -/
def run
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) : HostDriverResult Context :=
  HostDriver.run (handler inputs) context fuel state

end TransactionHostStorageDriver

namespace CheckedHostCoreProgram

/-- Start checked code under the observable transaction storage policy. -/
def runWithTransactionStorage
    (code : CheckedHostCoreProgram)
    (context : TransactionHostStorageDriver.Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    HostDriverResult TransactionHostStorageDriver.Context :=
  TransactionHostStorageDriver.run context inputs fuel
    (Core.State.initial code.program.body Core.hostEnvironment)

end CheckedHostCoreProgram

end Solcore.Semantics
