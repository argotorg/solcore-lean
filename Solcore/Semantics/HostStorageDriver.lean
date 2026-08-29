import Solcore.Semantics.CheckedHostCoreProgramExecution
import Solcore.Semantics.HostStorageHandler

/-! Fuel-preserving execution with combined working-storage handling. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

namespace HostStorageDriver

/-- Run Core while threading every handled storage-context update. -/
def run
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (state : Core.State) :
    HostDriverResult (Context RollbackState TraceState) :=
  HostDriver.run (handler codeAddress) context fuel state

end HostStorageDriver

namespace CheckedHostCoreProgram

/-- Start checked host-aware code with the combined working-storage handler. -/
def runWithStorage
    {RollbackState : Type u}
    {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat) :
    HostDriverResult
      (HostStorageDriver.Context RollbackState TraceState) :=
  HostStorageDriver.run context codeAddress fuel
    (Core.State.initial code.program.body Core.hostEnvironment)

end CheckedHostCoreProgram

end Solcore.Semantics
