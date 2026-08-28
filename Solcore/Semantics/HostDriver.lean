import Solcore.Core.HostRunner

/-! Generic fuel-preserving execution for handled Core host requests. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u

/-- A terminal result after every encountered host request is handled. -/
inductive HostDriverOutcome where
  | done (value : Core.Value) (store : Core.Store)
  | outOfFuel (state : Core.State)
  | fault (error : Core.MachineFault) (state : Core.State)
  deriving Repr, BEq, DecidableEq

/-- The latest host context together with the terminal Core outcome. -/
structure HostDriverResult (Context : Type u) where
  context : Context
  outcome : HostDriverOutcome

/-- A total interpreter for Core's indexed host-request interface. -/
structure HostHandler (Context : Type u) where
  handle :
    Context → (request : Core.HostRequest) →
      Context × request.Response

namespace HostHandler

/-- Handle a suspension and resume it with the request-indexed response. -/
def handleSuspension
    {Context : Type u}
    (handler : HostHandler Context)
    (context : Context)
    (suspension : Core.HostSuspension) :
    Context × Core.State :=
  let handled := handler.handle context suspension.request
  (handled.1, suspension.resume handled.2)

end HostHandler

namespace HostDriver

/--
Run Core in chunks, threading the context through every handled suspension.
Each suspension continues with exactly the fuel returned by the Core runner.
-/
def run
    {Context : Type u}
    (handler : HostHandler Context)
    (context : Context)
    (fuel : Nat)
    (state : Core.State) :
    HostDriverResult Context :=
  match _execution : Core.hostRun fuel state with
  | .done value store => ⟨context, .done value store⟩
  | .outOfFuel exhausted => ⟨context, .outOfFuel exhausted⟩
  | .fault error faultState => ⟨context, .fault error faultState⟩
  | .suspended suspension remainingFuel =>
      let handled := handler.handleSuspension context suspension
      run handler handled.1 remainingFuel handled.2
termination_by fuel
decreasing_by
  exact Core.HostRunResult.remainingFuel_lt _execution

end HostDriver

end Solcore.Semantics
