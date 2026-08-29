import Solcore.Semantics.CheckedHostCoreProgramExecution
import Solcore.Semantics.HostDriver
import Solcore.Semantics.HostStorageHandler

/-! Canonical driver for storage-backed host execution. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

namespace HostStorageDriver

/-- Run the current handler using one immutable execution input. -/
def run
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    HostDriverResult (Context RollbackState TraceState) :=
  HostDriver.run (handler inputs) context fuel state

end HostStorageDriver

namespace CheckedHostCoreProgram

/-- Start checked code with one immutable execution input. -/
def runWithStorage
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    HostDriverResult
      (HostStorageDriver.Context RollbackState TraceState) :=
  HostStorageDriver.run context inputs fuel
    (Core.State.initial code.program.body Core.hostEnvironment)

end CheckedHostCoreProgram

end Solcore.Semantics
