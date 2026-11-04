import Solcore.Core.HostMachine
import Solcore.Core.Machine
import Solcore.Core.Syntax
import Solcore.Core.HostRunner
import Solcore.Core.HostTyping
import Solcore.Core.Internal.HostPreservation
import Solcore.ContractRuntime.Frames

/-!
# Host driver

`HostHandler` answers Core's host requests. `HostDriver.run` runs Core, gives each suspension to the
handler, and continues with exactly the fuel the Core runner returned. `HostDriverResult` is the
outcome with the latest context.

`HostDriver.HandledSteps` is the path of a run, `HostDriverResult.FuelSoundWith` relates a result to
the fuel it used, and `HostDriverResult.resumeWithFuel` continues an exhausted run.

Main theorems: `HostDriver.run_hasType`, `HostDriver.run_ne_fault` and
`HostDriverResult.resumeWithFuel_ne_fault`.
-/

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsHostDriver
/-! Generic fuel-preserving execution for handled Core host requests. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u

/-- A total result after every supported host request encountered is handled. -/
inductive HostDriverOutcome where
  | done (value : Core.Value) (store : Core.Store)
  | outOfFuel (state : Core.State)
  | fault (error : Core.MachineFault) (state : Core.State)
  | unsupported (suspension : Core.HostSuspension) (remainingFuel : Nat)
  deriving Repr, BEq, DecidableEq

/-- The latest host context together with the terminal Core outcome. -/
structure HostDriverResult (Context : Type u) where
  context : Context
  outcome : HostDriverOutcome

/-- A total interpreter for Core's indexed host-request interface. -/
structure HostHandler (Context : Type u) where
  /-- Whether this policy can interpret a request without losing effects. -/
  supports : Core.HostRequest → Bool
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
      if handler.supports suspension.request then
        let handled := handler.handleSuspension context suspension
        run handler handled.1 remainingFuel handled.2
      else
        ⟨context, .unsupported suspension remainingFuel⟩
termination_by fuel
decreasing_by
  exact Core.HostRunResult.remainingFuel_lt _execution

end HostDriver

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.HostDriverProperties`
-/

/-! Observation preservation and type safety for generic handled execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

namespace HostDriverOutcome

/-- Typed terminal outcomes exclude the raw fault branch. -/
def HasType
    (outcome : HostDriverOutcome)
    (resultType : Core.Ty)
    (definitions : Core.DataEnvironment := []) : Prop :=
  match outcome with
  | .done value store =>
      ∃ world,
        Core.HostStoreHasTypes world store definitions ∧
          Core.HostRuntimeValueHasType world value resultType definitions
  | .outOfFuel state =>
      Core.HostStateHasType state resultType definitions
  | .fault _ _ => False
  | .unsupported suspension _ =>
      Core.HostSuspensionHasType suspension resultType definitions

@[simp] theorem unsupported_hasType_iff
    {suspension : Core.HostSuspension}
    {remainingFuel : Nat}
    {resultType : Core.Ty}
    {definitions : Core.DataEnvironment} :
    HasType (.unsupported suspension remainingFuel) resultType definitions ↔
      Core.HostSuspensionHasType suspension resultType definitions := by
  rfl

end HostDriverOutcome

namespace HostHandler

/-- Every dependent handler response resumes a typed suspension safely. -/
theorem handleSuspension_state_hasType
    {Context : Type u}
    (handler : HostHandler Context)
    (context : Context)
    (suspension : Core.HostSuspension)
    {definitions : Core.DataEnvironment}
    {resultType : Core.Ty}
    (typing :
      Core.HostSuspensionHasType suspension resultType definitions) :
    Core.HostStateHasType
      (handler.handleSuspension context suspension).2
      resultType definitions := by
  unfold handleSuspension
  exact typing.resume (handler.handle context suspension.request).2

end HostHandler

namespace HostDriver

/-- A request resumes with exactly Core's returned remaining fuel. -/
theorem run_of_suspended
    {Context : Type u}
    (handler : HostHandler Context)
    (context : Context)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (suspension : Core.HostSuspension)
    (execution :
      Core.hostRun fuel state = .suspended suspension remainingFuel) :
    run handler context fuel state =
      if handler.supports suspension.request then
        run handler
          (handler.handleSuspension context suspension).1
          remainingFuel
          (handler.handleSuspension context suspension).2
      else
        ⟨context, .unsupported suspension remainingFuel⟩ := by
  rw [run, execution]

/-- A typed start remains typed across every dependent handled response. -/
theorem run_hasType
    {Context : Type u}
    {definitions : Core.DataEnvironment}
    {resultType : Core.Ty}
    (handler : HostHandler Context)
    (context : Context)
    (fuel : Nat)
    (state : Core.State)
    (stateTyping :
      Core.HostStateHasType state resultType definitions) :
    (run handler context fuel state).outcome.HasType
      resultType definitions := by
  induction fuel using Nat.strongRecOn generalizing context state with
  | ind fuel ih =>
      cases execution : Core.hostRun fuel state with
      | done value store =>
          rw [run, execution]
          exact Core.hostRun_done_hasType stateTyping execution
      | outOfFuel exhausted =>
          rw [run, execution]
          exact Core.hostRun_outOfFuel_hasType stateTyping execution
      | fault error faultState =>
          rw [run, execution]
          exact Core.hostRun_never_faults stateTyping execution
      | suspended suspension remainingFuel =>
          rw [run_of_suspended handler context fuel remainingFuel state suspension
            execution]
          by_cases supported : handler.supports suspension.request = true
          · rw [if_pos supported]
            apply ih remainingFuel
              (Core.HostRunResult.remainingFuel_lt execution)
            apply handler.handleSuspension_state_hasType
            exact Core.hostRun_suspended_hasType stateTyping execution
          · rw [if_neg supported]
            exact Core.hostRun_suspended_hasType stateTyping execution

/-- A generic handled run cannot expose a fault from a typed start. -/
theorem run_ne_fault
    {Context : Type u}
    {definitions : Core.DataEnvironment}
    {resultType : Core.Ty}
    (handler : HostHandler Context)
    (context : Context)
    (fuel : Nat)
    (state faultState : Core.State)
    (error : Core.MachineFault)
    (stateTyping :
      Core.HostStateHasType state resultType definitions) :
    (run handler context fuel state).outcome ≠
      .fault error faultState := by
  intro fault
  have typing := run_hasType handler context fuel state stateTyping
  rw [fault] at typing
  exact typing

end HostDriver

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.HostDriverFuelProperties`
-/

/-! Generic whole-run transition and fuel accounting for handled host execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u

namespace HostDriver

/-- Core transition segments joined by zero-cost handled request boundaries. -/
inductive HandledSteps
    {Context : Type u}
    (handler : HostHandler Context) :
    Nat → Context → Core.State → Context → Core.State → Prop where
  | core
      {steps : Nat}
      {context : Context}
      {start finish : Core.State}
      (path : Core.HostSteps steps start finish) :
      HandledSteps handler steps context start context finish
  | handle
      {prefixSteps suffixSteps : Nat}
      {context nextContext finalContext : Context}
      {start requestState resumed finish : Core.State}
      {suspension : Core.HostSuspension}
      (prefixPath : Core.HostSteps prefixSteps start requestState)
      (emission : Core.HostRequestEmission requestState suspension)
      (supported : handler.supports suspension.request = true)
      (handled :
        handler.handleSuspension context suspension =
          (nextContext, resumed))
      (suffix :
        HandledSteps handler suffixSteps
          nextContext resumed finalContext finish) :
      HandledSteps handler (prefixSteps + 1 + suffixSteps)
        context start finalContext finish

end HostDriver

namespace HostDriverResult

/--
Completion and faults consume at most the supplied budget. Exhaustion consumes
it exactly and retains a state ready for another transition or request. An
unsupported result stops at the rejected request and retains the unused fuel.
-/
def FuelSoundWith
    {Context : Type u}
    (result : HostDriverResult Context)
    (handler : HostHandler Context)
    (fuel : Nat)
    (startContext : Context)
    (start : Core.State) : Prop :=
  match result.outcome with
  | .done value store =>
      ∃ spent,
        spent ≤ fuel ∧
          HostDriver.HandledSteps handler spent startContext start
            result.context (Core.State.final value store)
  | .outOfFuel exhausted =>
      HostDriver.HandledSteps handler fuel startContext start
          result.context exhausted ∧
        ((∃ next, Core.HostTransition exhausted next) ∨
          ∃ suspension, Core.HostRequestEmission exhausted suspension)
  | .fault error faultState =>
      ∃ spent,
        spent ≤ fuel ∧
          HostDriver.HandledSteps handler spent startContext start
            result.context faultState ∧
          Core.hostAdvance faultState = .fault error
  | .unsupported suspension remainingFuel =>
      ∃ spent requestState,
        spent + remainingFuel + 1 = fuel ∧
          HostDriver.HandledSteps handler spent startContext start
            result.context requestState ∧
          Core.HostRequestEmission requestState suspension ∧
          handler.supports suspension.request = false

end HostDriverResult

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.HostDriverCompletenessProperties`
-/

/-! Relational completeness of generic handled host execution. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.HostDriverResumption`
-/

/-! Additional fuel for exhausted or unsupported handled host execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u

namespace HostDriverResult

/--
Resume exhaustion by executing its retained state. An unsupported request stays
suspended while its offered fuel grows. Completed and faulted results stay exact.
-/
def resumeWithFuel
    {Context : Type u}
    (result : HostDriverResult Context)
    (handler : HostHandler Context)
    (additional : Nat) : HostDriverResult Context :=
  match result with
  | ⟨context, .outOfFuel exhausted⟩ =>
      HostDriver.run handler context additional exhausted
  | ⟨context, .unsupported suspension remainingFuel⟩ =>
      ⟨context, .unsupported suspension (remainingFuel + additional)⟩
  | terminal => terminal

@[simp] theorem resumeWithFuel_outOfFuel
    {Context : Type u}
    (context : Context)
    (state : Core.State)
    (handler : HostHandler Context)
    (additional : Nat) :
    resumeWithFuel ⟨context, .outOfFuel state⟩ handler additional =
      HostDriver.run handler context additional state := by
  rfl

@[simp] theorem resumeWithFuel_done
    {Context : Type u}
    (context : Context)
    (value : Core.Value)
    (store : Core.Store)
    (handler : HostHandler Context)
    (additional : Nat) :
    resumeWithFuel ⟨context, .done value store⟩ handler additional =
      ⟨context, .done value store⟩ := by
  rfl

@[simp] theorem resumeWithFuel_unsupported
    {Context : Type u}
    (context : Context)
    (suspension : Core.HostSuspension)
    (remainingFuel : Nat)
    (handler : HostHandler Context)
    (additional : Nat) :
    resumeWithFuel ⟨context, .unsupported suspension remainingFuel⟩
        handler additional =
      ⟨context, .unsupported suspension (remainingFuel + additional)⟩ := by
  rfl

end HostDriverResult

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.HostDriverResumptionProperties`
-/

/-! Exact one-shot and split-fuel laws for generic handled host execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u

namespace HostDriverResult

/-- Resuming a typed result preserves its result type. -/
theorem resumeWithFuel_hasType
    {Context : Type u}
    {definitions : Core.DataEnvironment}
    {resultType : Core.Ty}
    (result : HostDriverResult Context)
    (handler : HostHandler Context)
    (additional : Nat)
    (typing : result.outcome.HasType resultType definitions) :
    (result.resumeWithFuel handler additional).outcome.HasType
      resultType definitions := by
  cases result with
  | mk context outcome =>
      cases outcome with
      | done value store =>
          simpa only [resumeWithFuel_done] using typing
      | outOfFuel state =>
          simpa only [resumeWithFuel_outOfFuel] using
            HostDriver.run_hasType handler context additional state typing
      | fault error state =>
          exact False.elim typing
      | unsupported suspension remainingFuel =>
          simpa only [resumeWithFuel_unsupported,
            HostDriverOutcome.unsupported_hasType_iff] using typing

/-- Resuming a typed result cannot expose a raw machine fault. -/
theorem resumeWithFuel_ne_fault
    {Context : Type u}
    {definitions : Core.DataEnvironment}
    {resultType : Core.Ty}
    (result : HostDriverResult Context)
    (handler : HostHandler Context)
    (additional : Nat)
    (error : Core.MachineFault)
    (faultState : Core.State)
    (typing : result.outcome.HasType resultType definitions) :
    (result.resumeWithFuel handler additional).outcome ≠
      .fault error faultState := by
  intro fault
  have resumedTyping :=
    resumeWithFuel_hasType result handler additional typing
  rw [fault] at resumedTyping
  exact resumedTyping

end HostDriverResult

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.HostDriverFrameContinuation`
-/

/-! Partial frame-continuation construction from completed handled execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.HostDriverResult

universe u v w x

/--
Build continuation inputs only for a completed handled run. The caller owns
both the terminal-context projection and the interpretation of Core's final
value and local store as a frame outcome.
-/
def toFrameContinuationContext?
    {Context : Type x}
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (result : HostDriverResult Context)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason) :
    Option (FrameContinuationContext RollbackState TraceState TrapReason) :=
  match result.outcome with
  | .done value store =>
      some (FrameContinuationContext.fromCheckpointedWorkingPair
        (values result.context)
        (doneOutcome result.context value store))
  | .outOfFuel _ => none
  | .fault _ _ => none
  | .unsupported _ _ => none

end Solcore.ContractRuntime.HostDriverResult
end
