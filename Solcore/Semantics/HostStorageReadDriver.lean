import Solcore.Semantics.CheckedHostCoreProgramExecution
import Solcore.Semantics.HostDriver
import Solcore.Semantics.HostStorageReadHandler

/-! Fuel-preserving execution with handled working-storage reads. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

namespace HostStorageReadDriver

abbrev Context
    (RollbackState : Type u)
    (TraceState : Type v) :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount
    RollbackState TraceState

/-- Read every currently supported request from the selected working Account. -/
def handler
    {RollbackState : Type u}
    {TraceState : Type v} :
    HostHandler (Context RollbackState TraceState) where
  handle context request :=
    match request with
    | .storageRead slot => (context, context.readStorage slot)

/-- Interpret one request through the current proven-present storage context. -/
def handleHostSuspension
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension) :
    Context RollbackState TraceState × Core.State :=
  handleStorageReadSuspension context suspension

@[simp] theorem handler_handleSuspension
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension) :
    handler.handleSuspension context suspension =
      handleHostSuspension context suspension := by
  cases suspension with
  | mk request continuation store =>
      cases request
      rfl

/--
Run Core in chunks and handle every storage-read suspension. A suspension
continues with exactly the remaining fuel returned by the Core runner.
-/
def run
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (fuel : Nat)
    (state : Core.State) :
    HostDriverResult (Context RollbackState TraceState) :=
  HostDriver.run handler context fuel state

end HostStorageReadDriver

namespace CheckedHostCoreProgram

/-- Start checked host-aware code and handle its working-storage reads. -/
def runWithStorageReads
    {RollbackState : Type u}
    {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageReadDriver.Context RollbackState TraceState)
    (fuel : Nat) :
    HostDriverResult
      (HostStorageReadDriver.Context RollbackState TraceState) :=
  HostStorageReadDriver.run context fuel
    (Core.State.initial code.program.body Core.hostEnvironment)

end CheckedHostCoreProgram

end Solcore.Semantics
