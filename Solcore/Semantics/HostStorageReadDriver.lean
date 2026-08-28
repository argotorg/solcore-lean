import Solcore.Core.HostRunner
import Solcore.Semantics.CheckedHostCoreProgramExecution
import Solcore.Semantics.HostStorageReadHandler

/-! Fuel-preserving execution with handled working-storage reads. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

/-- A terminal result after every currently supported host request is handled. -/
inductive HostDriverOutcome where
  | done (value : Core.Value) (store : Core.Store)
  | outOfFuel (state : Core.State)
  | fault (error : Core.MachineFault) (state : Core.State)
  deriving Repr, BEq, DecidableEq

/-- The latest host context together with the terminal Core outcome. -/
structure HostDriverResult (Context : Type u) where
  context : Context
  outcome : HostDriverOutcome

namespace HostStorageReadDriver

abbrev Context
    (RollbackState : Type u)
    (TraceState : Type v) :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount
    RollbackState TraceState

/-- Interpret one request through the current proven-present storage context. -/
def handleHostSuspension
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension) :
    Context RollbackState TraceState × Core.State :=
  handleStorageReadSuspension context suspension

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
  match _execution : Core.hostRun fuel state with
  | .done value store => ⟨context, .done value store⟩
  | .outOfFuel exhausted => ⟨context, .outOfFuel exhausted⟩
  | .fault error faultState => ⟨context, .fault error faultState⟩
  | .suspended suspension remainingFuel =>
      let handled := handleHostSuspension context suspension
      run handled.1 remainingFuel handled.2
termination_by fuel
decreasing_by
  exact Core.HostRunResult.remainingFuel_lt _execution

end HostStorageReadDriver

namespace CheckedHostCoreProgram

/-- Start checked host-aware code and handle its working-storage reads. -/
def runWithStorage
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
