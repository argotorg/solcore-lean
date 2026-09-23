import Solcore.Core.HostRunner
import Solcore.ContractRuntime.FrameContinuationContextFromCheckpointedWorkingPair
import Solcore.ContractRuntime.FrameResolutionResult

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
        Core.StoreHasTypes world store ∧
          Core.HostRuntimeValueHasType world value resultType definitions
  | .outOfFuel state =>
      Core.HostStateHasType state resultType definitions
  | .fault _ _ => False
  | .unsupported suspension _ =>
      Core.HostSuspensionHasType suspension resultType definitions

@[simp] theorem done_hasType_iff
    {value : Core.Value}
    {store : Core.Store}
    {resultType : Core.Ty}
    {definitions : Core.DataEnvironment} :
    HasType (.done value store) resultType definitions ↔
      ∃ world,
        Core.StoreHasTypes world store ∧
          Core.HostRuntimeValueHasType world value resultType definitions := by
  rfl

@[simp] theorem outOfFuel_hasType_iff
    {state : Core.State}
    {resultType : Core.Ty}
    {definitions : Core.DataEnvironment} :
    HasType (.outOfFuel state) resultType definitions ↔
      Core.HostStateHasType state resultType definitions := by
  rfl

@[simp] theorem fault_not_hasType
    {error : Core.MachineFault}
    {state : Core.State}
    {resultType : Core.Ty}
    {definitions : Core.DataEnvironment} :
    ¬ HasType (.fault error state) resultType definitions := by
  simp [HasType]

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

@[simp] theorem run_of_done
    {Context : Type u}
    (handler : HostHandler Context)
    (context : Context)
    (fuel : Nat)
    (state : Core.State)
    (value : Core.Value)
    (store : Core.Store)
    (execution : Core.hostRun fuel state = .done value store) :
    run handler context fuel state =
      ⟨context, .done value store⟩ := by
  rw [run, execution]

@[simp] theorem run_of_outOfFuel
    {Context : Type u}
    (handler : HostHandler Context)
    (context : Context)
    (fuel : Nat)
    (state exhausted : Core.State)
    (execution : Core.hostRun fuel state = .outOfFuel exhausted) :
    run handler context fuel state =
      ⟨context, .outOfFuel exhausted⟩ := by
  rw [run, execution]

@[simp] theorem run_of_fault
    {Context : Type u}
    (handler : HostHandler Context)
    (context : Context)
    (fuel : Nat)
    (state faultState : Core.State)
    (error : Core.MachineFault)
    (execution : Core.hostRun fuel state = .fault error faultState) :
    run handler context fuel state =
      ⟨context, .fault error faultState⟩ := by
  rw [run, execution]

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

@[simp] theorem run_of_unsupported
    {Context : Type u}
    (handler : HostHandler Context)
    (context : Context)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (suspension : Core.HostSuspension)
    (execution :
      Core.hostRun fuel state = .suspended suspension remainingFuel)
    (unsupported : handler.supports suspension.request = false) :
    run handler context fuel state =
      ⟨context, .unsupported suspension remainingFuel⟩ := by
  rw [run_of_suspended handler context fuel remainingFuel state suspension
    execution, unsupported]
  rfl

/-- Any observation preserved by one handler call is preserved by a whole run. -/
theorem run_observe
    {Context : Type u}
    {Observation : Type v}
    (handler : HostHandler Context)
    (observe : Context → Observation)
    (handleObserve :
      ∀ context request,
        observe (handler.handle context request).1 = observe context)
    (context : Context)
    (fuel : Nat)
    (state : Core.State) :
    observe (run handler context fuel state).context = observe context := by
  induction fuel using Nat.strongRecOn generalizing context state with
  | ind fuel ih =>
      cases execution : Core.hostRun fuel state with
      | done value store => rw [run, execution]
      | outOfFuel exhausted => rw [run, execution]
      | fault error faultState => rw [run, execution]
      | suspended suspension remainingFuel =>
          rw [run_of_suspended handler context fuel remainingFuel state suspension
            execution]
          by_cases supported : handler.supports suspension.request = true
          · rw [if_pos supported]
            calc
              observe
                  (run handler
                    (handler.handleSuspension context suspension).1
                    remainingFuel
                    (handler.handleSuspension context suspension).2).context =
                  observe (handler.handleSuspension context suspension).1 :=
                ih remainingFuel
                  (Core.HostRunResult.remainingFuel_lt execution)
                  (handler.handleSuspension context suspension).1
                  (handler.handleSuspension context suspension).2
              _ = observe context := by
                simpa [HostHandler.handleSuspension] using
                  handleObserve context suspension.request
          · rw [if_neg supported]

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

/-- A policy that supports every request never produces an unsupported result. -/
theorem run_ne_unsupported_of_supports_all
    {Context : Type u}
    (handler : HostHandler Context)
    (supportsAll : ∀ request, handler.supports request = true)
    (context : Context)
    (fuel : Nat)
    (state : Core.State)
    (suspension : Core.HostSuspension)
    (remainingFuel : Nat) :
    (run handler context fuel state).outcome ≠
      .unsupported suspension remainingFuel := by
  induction fuel using Nat.strongRecOn generalizing context state with
  | ind fuel ih =>
      cases execution : Core.hostRun fuel state with
      | done value store =>
          rw [run_of_done handler context fuel state value store execution]
          exact HostDriverOutcome.noConfusion
      | outOfFuel exhausted =>
          rw [run_of_outOfFuel handler context fuel state exhausted execution]
          exact HostDriverOutcome.noConfusion
      | fault error faultState =>
          rw [run_of_fault handler context fuel state faultState error execution]
          exact HostDriverOutcome.noConfusion
      | suspended emitted remaining =>
          rw [run_of_suspended handler context fuel remaining state emitted
            execution, if_pos (supportsAll emitted.request)]
          exact ih remaining (Core.HostRunResult.remainingFuel_lt execution)
            (handler.handleSuspension context emitted).1
            (handler.handleSuspension context emitted).2

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

/-- Handled paths compose while retaining the exact intermediate context. -/
theorem HandledSteps.trans
    {Context : Type u}
    {handler : HostHandler Context}
    {leftSteps rightSteps : Nat}
    {startContext middleContext finalContext : Context}
    {start middle finish : Core.State}
    (left :
      HandledSteps handler leftSteps
        startContext start middleContext middle)
    (right :
      HandledSteps handler rightSteps
        middleContext middle finalContext finish) :
    HandledSteps handler (leftSteps + rightSteps)
      startContext start finalContext finish := by
  induction left with
  | core leftPath =>
      cases right with
      | core rightPath =>
          exact .core (leftPath.trans rightPath)
      | @handle prefixSteps suffixSteps context nextContext finalContext
          start requestState resumed finish suspension prefixPath emission
          supported handled suffix =>
          have combinedPrefix := leftPath.trans prefixPath
          have combined :=
            HandledSteps.handle combinedPrefix emission supported handled suffix
          simpa [Nat.add_assoc] using combined
  | @handle prefixSteps suffixSteps context nextContext middleContext
      start requestState resumed middle suspension prefixPath emission
      supported handled suffix suffixIH =>
      have combinedSuffix := suffixIH right
      have combined :=
        HandledSteps.handle prefixPath emission supported handled combinedSuffix
      simpa [Nat.add_assoc] using combined

/-- A typed Core state remains typed across every handled request boundary. -/
theorem HandledSteps.preserve
    {Context : Type u}
    {handler : HostHandler Context}
    {steps : Nat}
    {startContext finalContext : Context}
    {start finish : Core.State}
    {resultType : Core.Ty}
    {definitions : Core.DataEnvironment}
    (path :
      HandledSteps handler steps
        startContext start finalContext finish)
    (typing :
      Core.HostStateHasType start resultType definitions) :
    Core.HostStateHasType finish resultType definitions := by
  induction path with
  | core corePath =>
      exact corePath.preserve typing
  | @handle prefixSteps suffixSteps context nextContext finalContext
      start requestState resumed finish suspension prefixPath emission
      supported handled suffix suffixIH =>
      have requestStateTyping := prefixPath.preserve typing
      have suspensionTyping :=
        Core.hostRequestEmission_hasType requestStateTyping emission
      have resumedTyping :=
        handler.handleSuspension_state_hasType
          context suspension suspensionTyping
      rw [handled] at resumedTyping
      exact suffixIH resumedTyping

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

namespace FuelSoundWith

/-- Prefix a sound driven suffix with one emitted and handled request. -/
theorem prependRequest
    {Context : Type u}
    {result : HostDriverResult Context}
    {handler : HostHandler Context}
    {fuel remainingFuel prefixSteps : Nat}
    {context nextContext : Context}
    {start requestState resumed : Core.State}
    {suspension : Core.HostSuspension}
    (prefixPath : Core.HostSteps prefixSteps start requestState)
    (emission : Core.HostRequestEmission requestState suspension)
    (supported : handler.supports suspension.request = true)
    (handled :
      handler.handleSuspension context suspension =
        (nextContext, resumed))
    (accounting : prefixSteps + remainingFuel + 1 = fuel)
    (suffixSound :
      result.FuelSoundWith handler remainingFuel nextContext resumed) :
    result.FuelSoundWith handler fuel context start := by
  cases result with
  | mk finalContext outcome =>
      cases outcome with
      | done value store =>
          change ∃ spent, spent ≤ remainingFuel ∧ _ at suffixSound
          change ∃ spent, spent ≤ fuel ∧ _
          obtain ⟨suffixSteps, suffixBound, suffix⟩ := suffixSound
          exact ⟨prefixSteps + 1 + suffixSteps, by omega,
            .handle prefixPath emission supported handled suffix⟩
      | outOfFuel exhausted =>
          change
            HostDriver.HandledSteps handler remainingFuel nextContext
                resumed finalContext exhausted ∧ _ at suffixSound
          change
            HostDriver.HandledSteps handler fuel context start
                finalContext exhausted ∧ _
          obtain ⟨suffix, ready⟩ := suffixSound
          have combined :=
            HostDriver.HandledSteps.handle
              prefixPath emission supported handled suffix
          have countEq : prefixSteps + 1 + remainingFuel = fuel := by
            omega
          exact ⟨countEq ▸ combined, ready⟩
      | fault error faultState =>
          change
            ∃ spent,
              spent ≤ remainingFuel ∧
                HostDriver.HandledSteps handler spent nextContext resumed
                  finalContext faultState ∧
                Core.hostAdvance faultState = .fault error at suffixSound
          change
            ∃ spent,
              spent ≤ fuel ∧
                HostDriver.HandledSteps handler spent context start
                  finalContext faultState ∧
                Core.hostAdvance faultState = .fault error
          obtain ⟨suffixSteps, suffixBound, suffix, terminal⟩ := suffixSound
          exact ⟨prefixSteps + 1 + suffixSteps, by omega,
            .handle prefixPath emission supported handled suffix, terminal⟩
      | unsupported suspension unsupportedRemainingFuel =>
          change ∃ spent requestState,
            spent + unsupportedRemainingFuel + 1 = remainingFuel ∧
              HostDriver.HandledSteps handler spent nextContext resumed
                finalContext requestState ∧
              Core.HostRequestEmission requestState suspension ∧
              handler.supports suspension.request = false at suffixSound
          change ∃ spent requestState,
            spent + unsupportedRemainingFuel + 1 = fuel ∧
              HostDriver.HandledSteps handler spent context start
                finalContext requestState ∧
              Core.HostRequestEmission requestState suspension ∧
              handler.supports suspension.request = false
          obtain ⟨suffixSteps, requestState, suffixAccounting, suffix,
            requestEmission, requestUnsupported⟩ := suffixSound
          exact ⟨prefixSteps + 1 + suffixSteps, requestState, by omega,
            .handle prefixPath emission supported handled suffix,
            requestEmission, requestUnsupported⟩

/-- Fuel-sound relational evidence directly preserves outcome typing. -/
theorem hasType
    {Context : Type u}
    {result : HostDriverResult Context}
    {handler : HostHandler Context}
    {fuel : Nat}
    {startContext : Context}
    {start : Core.State}
    {resultType : Core.Ty}
    {definitions : Core.DataEnvironment}
    (sound :
      result.FuelSoundWith handler fuel startContext start)
    (typing :
      Core.HostStateHasType start resultType definitions) :
    result.outcome.HasType resultType definitions := by
  cases result with
  | mk finalContext outcome =>
      cases outcome with
      | done value store =>
          change ∃ spent, spent ≤ fuel ∧ _ at sound
          change ∃ world,
            Core.StoreHasTypes world store ∧
              Core.HostRuntimeValueHasType
                world value resultType definitions
          obtain ⟨spent, bound, path⟩ := sound
          exact (path.preserve typing).final_components
      | outOfFuel exhausted =>
          change HostDriver.HandledSteps handler fuel startContext start
              finalContext exhausted ∧ _ at sound
          change Core.HostStateHasType exhausted resultType definitions
          exact sound.1.preserve typing
      | fault error faultState =>
          change ∃ spent, spent ≤ fuel ∧ _ ∧ _ at sound
          change False
          obtain ⟨spent, bound, path, terminal⟩ := sound
          exact Core.well_typed_host_state_never_faults
            (path.preserve typing) terminal
      | unsupported suspension remainingFuel =>
          change ∃ spent requestState, _ at sound
          change Core.HostSuspensionHasType suspension resultType definitions
          obtain ⟨spent, requestState, accounting, path, emission,
            unsupported⟩ := sound
          exact Core.hostRequestEmission_hasType (path.preserve typing) emission

end FuelSoundWith

end HostDriverResult

namespace HostDriver

/-- The generic executable driver exactly respects Core's finite fuel budget. -/
theorem run_fuelSound
    {Context : Type u}
    (handler : HostHandler Context)
    (context : Context)
    (fuel : Nat)
    (state : Core.State) :
    (run handler context fuel state).FuelSoundWith
      handler fuel context state := by
  induction fuel using Nat.strongRecOn generalizing context state with
  | ind fuel ih =>
      cases execution : Core.hostRun fuel state with
      | done value store =>
          rw [run, execution]
          obtain ⟨steps, bound, path⟩ :=
            Core.hostRun_done_sound execution
          exact ⟨steps, bound, .core path⟩
      | outOfFuel exhausted =>
          rw [run, execution]
          obtain ⟨path, ready⟩ := Core.hostRun_outOfFuel_sound execution
          exact ⟨.core path, ready⟩
      | fault error faultState =>
          rw [run, execution]
          obtain ⟨steps, bound, path, terminal⟩ :=
            Core.hostRun_fault_sound execution
          exact ⟨steps, bound, .core path, terminal⟩
      | suspended suspension remainingFuel =>
          obtain ⟨prefixSteps, requestState, prefixPath, emission, accounting⟩ :=
            Core.hostRun_suspended_sound execution
          cases supported : handler.supports suspension.request with
          | false =>
              rw [HostDriver.run_of_unsupported handler context fuel remainingFuel
                state suspension execution supported]
              exact ⟨prefixSteps, requestState, accounting, .core prefixPath,
                emission, supported⟩
          | true =>
              rw [HostDriver.run_of_suspended handler context fuel remainingFuel
                state suspension execution, supported]
              apply HostDriverResult.FuelSoundWith.prependRequest
                prefixPath emission supported
                (nextContext :=
                  (handler.handleSuspension context suspension).1)
                (resumed :=
                  (handler.handleSuspension context suspension).2)
              · exact
                  (Prod.eta
                    (handler.handleSuspension context suspension)).symm
              · exact accounting
              · exact ih remainingFuel
                  (Core.HostRunResult.remainingFuel_lt execution)
                  (handler.handleSuspension context suspension).1
                  (handler.handleSuspension context suspension).2

end HostDriver

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.HostDriverCompletenessProperties`
-/

/-! Relational completeness of generic handled host execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u

namespace HostDriver

private theorem run_done_complete_of_steps
    {Context : Type u}
    (handler : HostHandler Context)
    {spent fuel : Nat}
    {startContext finalContext : Context}
    {start finish : Core.State}
    {value : Core.Value}
    (path :
      HandledSteps handler spent startContext start finalContext finish)
    (terminal : Core.hostAdvance finish = .done value)
    (enough : spent ≤ fuel) :
    run handler startContext fuel start =
      ⟨finalContext, .done value finish.store⟩ := by
  induction path generalizing fuel with
  | core corePath =>
      apply run_of_done
      exact Core.hostRun_done_complete_of_steps corePath terminal enough
  | @handle prefixSteps suffixSteps context nextContext finalContext
      start requestState resumed finish suspension prefixPath emission
      supported handled suffix ih =>
      let remainingFuel := fuel - prefixSteps - 1
      have accounting :
          prefixSteps + remainingFuel + 1 = fuel := by
        dsimp [remainingFuel]
        omega
      have suffixEnough : suffixSteps ≤ remainingFuel := by
        dsimp [remainingFuel]
        omega
      have execution :
          Core.hostRun fuel start =
            .suspended suspension remainingFuel :=
        Core.hostRun_suspended_complete_of_steps
          prefixPath emission accounting
      rw [run_of_suspended handler context fuel remainingFuel start
        suspension execution]
      rw [supported]
      rw [handled]
      exact ih terminal suffixEnough

/-- A bounded handled path to a final state replays to the exact done result. -/
theorem run_done_complete
    {Context : Type u}
    (handler : HostHandler Context)
    {spent fuel : Nat}
    {startContext finalContext : Context}
    {start : Core.State}
    {value : Core.Value}
    {store : Core.Store}
    (path :
      HandledSteps handler spent startContext start finalContext
        (Core.State.final value store))
    (enough : spent ≤ fuel) :
    run handler startContext fuel start =
      ⟨finalContext, .done value store⟩ := by
  exact run_done_complete_of_steps handler path
    (Core.hostAdvance_done_iff.mpr ⟨store, rfl⟩) enough

/-- A bounded handled path to a raw fault replays to that exact fault result. -/
theorem run_fault_complete
    {Context : Type u}
    (handler : HostHandler Context)
    {spent fuel : Nat}
    {startContext finalContext : Context}
    {start faultState : Core.State}
    {error : Core.MachineFault}
    (path :
      HandledSteps handler spent startContext start finalContext faultState)
    (terminal : Core.hostAdvance faultState = .fault error)
    (enough : spent ≤ fuel) :
    run handler startContext fuel start =
      ⟨finalContext, .fault error faultState⟩ := by
  induction path generalizing fuel with
  | core corePath =>
      apply run_of_fault
      exact Core.hostRun_fault_complete_of_steps corePath terminal enough
  | @handle prefixSteps suffixSteps context nextContext finalContext
      start requestState resumed finish suspension prefixPath emission
      supported handled suffix ih =>
      let remainingFuel := fuel - prefixSteps - 1
      have accounting :
          prefixSteps + remainingFuel + 1 = fuel := by
        dsimp [remainingFuel]
        omega
      have suffixEnough : suffixSteps ≤ remainingFuel := by
        dsimp [remainingFuel]
        omega
      have execution :
          Core.hostRun fuel start =
            .suspended suspension remainingFuel :=
        Core.hostRun_suspended_complete_of_steps
          prefixPath emission accounting
      rw [run_of_suspended handler context fuel remainingFuel start
        suspension execution]
      rw [supported]
      rw [handled]
      exact ih terminal suffixEnough

/--
An exact-length handled path to a transition- or request-ready state replays to
exhaustion.
-/
theorem run_outOfFuel_complete
    {Context : Type u}
    (handler : HostHandler Context)
    {fuel : Nat}
    {startContext finalContext : Context}
    {start exhausted : Core.State}
    (path :
      HandledSteps handler fuel startContext start finalContext exhausted)
    (ready :
      (∃ next, Core.HostTransition exhausted next) ∨
        ∃ suspension, Core.HostRequestEmission exhausted suspension) :
    run handler startContext fuel start =
      ⟨finalContext, .outOfFuel exhausted⟩ := by
  induction path with
  | core corePath =>
      apply run_of_outOfFuel
      exact Core.hostRun_outOfFuel_complete corePath ready
  | @handle prefixSteps suffixSteps context nextContext finalContext
      start requestState resumed finish suspension prefixPath emission
      supported handled suffix ih =>
      have accounting :
          prefixSteps + suffixSteps + 1 =
            prefixSteps + 1 + suffixSteps := by
        omega
      have execution :
          Core.hostRun (prefixSteps + 1 + suffixSteps) start =
            .suspended suspension suffixSteps :=
        Core.hostRun_suspended_complete_of_steps
          prefixPath emission accounting
      rw [run_of_suspended handler context
        (prefixSteps + 1 + suffixSteps) suffixSteps start suspension execution]
      rw [supported]
      rw [handled]
      exact ih ready

/-- An exact path to a policy-rejected request replays that rejection. -/
theorem run_unsupported_complete
    {Context : Type u}
    (handler : HostHandler Context)
    {spent fuel remainingFuel : Nat}
    {startContext finalContext : Context}
    {start requestState : Core.State}
    {suspension : Core.HostSuspension}
    (path :
      HandledSteps handler spent startContext start finalContext requestState)
    (emission : Core.HostRequestEmission requestState suspension)
    (unsupported : handler.supports suspension.request = false)
    (accounting : spent + remainingFuel + 1 = fuel) :
    run handler startContext fuel start =
      ⟨finalContext, .unsupported suspension remainingFuel⟩ := by
  induction path generalizing fuel with
  | core corePath =>
      apply run_of_unsupported
      · exact Core.hostRun_suspended_complete_of_steps
          corePath emission accounting
      · exact unsupported
  | @handle prefixSteps suffixSteps context nextContext finalContext
      start requestState' resumed finish emitted prefixPath requestEmission
      supported handled suffix ih =>
      let nextFuel := fuel - prefixSteps - 1
      have outerAccounting : prefixSteps + nextFuel + 1 = fuel := by
        dsimp [nextFuel]
        omega
      have suffixAccounting : suffixSteps + remainingFuel + 1 = nextFuel := by
        dsimp [nextFuel]
        omega
      have execution :
          Core.hostRun fuel start = .suspended emitted nextFuel :=
        Core.hostRun_suspended_complete_of_steps
          prefixPath requestEmission outerAccounting
      rw [run_of_suspended handler context fuel nextFuel start emitted execution]
      rw [supported, handled]
      exact ih emission suffixAccounting

/-- Any fuel-sound relational witness determines the executable driver result. -/
theorem run_eq_of_fuelSoundWith
    {Context : Type u}
    (handler : HostHandler Context)
    (startContext : Context)
    (fuel : Nat)
    (start : Core.State)
    (result : HostDriverResult Context)
    (sound :
      result.FuelSoundWith handler fuel startContext start) :
    run handler startContext fuel start = result := by
  cases result with
  | mk finalContext outcome =>
      cases outcome with
      | done value store =>
          change ∃ spent, spent ≤ fuel ∧ _ at sound
          obtain ⟨spent, enough, path⟩ := sound
          exact run_done_complete handler path enough
      | outOfFuel exhausted =>
          change _ ∧ _ at sound
          exact run_outOfFuel_complete handler sound.1 sound.2
      | fault error faultState =>
          change ∃ spent, spent ≤ fuel ∧ _ ∧ _ at sound
          obtain ⟨spent, enough, path, terminal⟩ := sound
          exact run_fault_complete handler path terminal enough
      | unsupported suspension remainingFuel =>
          change ∃ spent requestState, _ at sound
          obtain ⟨spent, requestState, accounting, path, emission,
            unsupported⟩ := sound
          exact run_unsupported_complete handler path emission unsupported
            accounting

/-- Executable generic driver results are exactly the fuel-sound results. -/
theorem run_eq_iff_fuelSoundWith
    {Context : Type u}
    (handler : HostHandler Context)
    (startContext : Context)
    (fuel : Nat)
    (start : Core.State)
    (result : HostDriverResult Context) :
    run handler startContext fuel start = result ↔
      result.FuelSoundWith handler fuel startContext start := by
  constructor
  · intro execution
    rw [← execution]
    exact run_fuelSound handler startContext fuel start
  · exact run_eq_of_fuelSoundWith handler startContext fuel start result

/-- A completed result is unchanged when the driver receives more fuel. -/
theorem run_done_stable
    {Context : Type u}
    (handler : HostHandler Context)
    {fuel largerFuel : Nat}
    {startContext finalContext : Context}
    {start : Core.State}
    {value : Core.Value}
    {store : Core.Store}
    (execution :
      run handler startContext fuel start =
        ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    run handler startContext largerFuel start =
      ⟨finalContext, .done value store⟩ := by
  have sound := run_fuelSound handler startContext fuel start
  rw [execution] at sound
  change ∃ spent, spent ≤ fuel ∧ _ at sound
  obtain ⟨spent, enough, path⟩ := sound
  apply run_done_complete handler path
  exact Nat.le_trans enough more

/-- A raw fault result is unchanged when the driver receives more fuel. -/
theorem run_fault_stable
    {Context : Type u}
    (handler : HostHandler Context)
    {fuel largerFuel : Nat}
    {startContext finalContext : Context}
    {start faultState : Core.State}
    {error : Core.MachineFault}
    (execution :
      run handler startContext fuel start =
        ⟨finalContext, .fault error faultState⟩)
    (more : fuel ≤ largerFuel) :
    run handler startContext largerFuel start =
      ⟨finalContext, .fault error faultState⟩ := by
  have sound := run_fuelSound handler startContext fuel start
  rw [execution] at sound
  change ∃ spent, spent ≤ fuel ∧ _ ∧ _ at sound
  obtain ⟨spent, enough, path, terminal⟩ := sound
  apply run_fault_complete handler path terminal
  exact Nat.le_trans enough more

end HostDriver

namespace HostDriverResult.FuelSoundWith

/-- Two fuel-sound witnesses for one exact budget determine the same result. -/
theorem result_unique
    {Context : Type u}
    {handler : HostHandler Context}
    {fuel : Nat}
    {startContext : Context}
    {start : Core.State}
    {left right : HostDriverResult Context}
    (leftSound :
      left.FuelSoundWith handler fuel startContext start)
    (rightSound :
      right.FuelSoundWith handler fuel startContext start) :
    left = right := by
  exact
    (HostDriver.run_eq_of_fuelSoundWith
      handler startContext fuel start left leftSound).symm.trans
    (HostDriver.run_eq_of_fuelSoundWith
      handler startContext fuel start right rightSound)

/-- Done evidence remains valid when its fuel allowance is increased. -/
theorem done_mono
    {Context : Type u}
    {handler : HostHandler Context}
    {fuel largerFuel : Nat}
    {startContext finalContext : Context}
    {start : Core.State}
    {value : Core.Value}
    {store : Core.Store}
    (sound :
      (⟨finalContext, .done value store⟩ :
        HostDriverResult Context).FuelSoundWith
          handler fuel startContext start)
    (more : fuel ≤ largerFuel) :
    (⟨finalContext, .done value store⟩ :
      HostDriverResult Context).FuelSoundWith
        handler largerFuel startContext start := by
  change ∃ spent, spent ≤ fuel ∧ _ at sound
  change ∃ spent, spent ≤ largerFuel ∧ _
  obtain ⟨spent, bound, path⟩ := sound
  exact ⟨spent, Nat.le_trans bound more, path⟩

/-- Raw-fault evidence remains valid when its fuel allowance is increased. -/
theorem fault_mono
    {Context : Type u}
    {handler : HostHandler Context}
    {fuel largerFuel : Nat}
    {startContext finalContext : Context}
    {start faultState : Core.State}
    {error : Core.MachineFault}
    (sound :
      (⟨finalContext, .fault error faultState⟩ :
        HostDriverResult Context).FuelSoundWith
          handler fuel startContext start)
    (more : fuel ≤ largerFuel) :
    (⟨finalContext, .fault error faultState⟩ :
      HostDriverResult Context).FuelSoundWith
        handler largerFuel startContext start := by
  change ∃ spent, spent ≤ fuel ∧ _ ∧ _ at sound
  change ∃ spent, spent ≤ largerFuel ∧ _ ∧ _
  obtain ⟨spent, bound, path, terminal⟩ := sound
  exact ⟨spent, Nat.le_trans bound more, path, terminal⟩

/-- Done witnesses at any two budgets retain the exact same complete result. -/
theorem done_result_unique
    {Context : Type u}
    {handler : HostHandler Context}
    {leftFuel rightFuel : Nat}
    {startContext leftContext rightContext : Context}
    {start : Core.State}
    {leftValue rightValue : Core.Value}
    {leftStore rightStore : Core.Store}
    (leftSound :
      (⟨leftContext, .done leftValue leftStore⟩ :
        HostDriverResult Context).FuelSoundWith
          handler leftFuel startContext start)
    (rightSound :
      (⟨rightContext, .done rightValue rightStore⟩ :
        HostDriverResult Context).FuelSoundWith
          handler rightFuel startContext start) :
    (⟨leftContext, .done leftValue leftStore⟩ :
      HostDriverResult Context) =
      ⟨rightContext, .done rightValue rightStore⟩ := by
  exact result_unique
    (done_mono leftSound (Nat.le_max_left leftFuel rightFuel))
    (done_mono rightSound (Nat.le_max_right leftFuel rightFuel))

/-- Fault witnesses at any two budgets retain the exact same complete result. -/
theorem fault_result_unique
    {Context : Type u}
    {handler : HostHandler Context}
    {leftFuel rightFuel : Nat}
    {startContext leftContext rightContext : Context}
    {start leftFaultState rightFaultState : Core.State}
    {leftError rightError : Core.MachineFault}
    (leftSound :
      (⟨leftContext, .fault leftError leftFaultState⟩ :
        HostDriverResult Context).FuelSoundWith
          handler leftFuel startContext start)
    (rightSound :
      (⟨rightContext, .fault rightError rightFaultState⟩ :
        HostDriverResult Context).FuelSoundWith
          handler rightFuel startContext start) :
    (⟨leftContext, .fault leftError leftFaultState⟩ :
      HostDriverResult Context) =
      ⟨rightContext, .fault rightError rightFaultState⟩ := by
  exact result_unique
    (fault_mono leftSound (Nat.le_max_left leftFuel rightFuel))
    (fault_mono rightSound (Nat.le_max_right leftFuel rightFuel))

end HostDriverResult.FuelSoundWith

end Solcore.ContractRuntime

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

@[simp] theorem resumeWithFuel_fault
    {Context : Type u}
    (context : Context)
    (error : Core.MachineFault)
    (state : Core.State)
    (handler : HostHandler Context)
    (additional : Nat) :
    resumeWithFuel ⟨context, .fault error state⟩ handler additional =
      ⟨context, .fault error state⟩ := by
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

namespace HostDriver

/--
After exact exhaustion, an additional budget continues from the retained
context and Core state without replaying the prefix.
-/
theorem run_additional_of_outOfFuel
    {Context : Type u}
    (handler : HostHandler Context)
    {context nextContext : Context}
    {fuel additional : Nat}
    {state exhausted : Core.State}
    (execution :
      run handler context fuel state =
        ⟨nextContext, .outOfFuel exhausted⟩) :
    run handler context (fuel + additional) state =
      run handler nextContext additional exhausted := by
  have prefixSound := run_fuelSound handler context fuel state
  rw [execution] at prefixSound
  change
    HandledSteps handler fuel context state nextContext exhausted ∧ _
      at prefixSound
  obtain ⟨prefixPath, _prefixReady⟩ := prefixSound
  have suffixSound :=
    run_fuelSound handler nextContext additional exhausted
  cases suffixExecution : run handler nextContext additional exhausted with
  | mk finalContext outcome =>
      apply run_eq_of_fuelSoundWith handler context
        (fuel + additional) state ⟨finalContext, outcome⟩
      rw [suffixExecution] at suffixSound
      cases outcome with
      | done value store =>
          change ∃ spent, spent ≤ additional ∧ _ at suffixSound
          change ∃ spent, spent ≤ fuel + additional ∧ _
          obtain ⟨spent, bound, suffix⟩ := suffixSound
          exact ⟨fuel + spent, Nat.add_le_add_left bound fuel,
            prefixPath.trans suffix⟩
      | outOfFuel finalState =>
          change
            HandledSteps handler additional nextContext exhausted
                finalContext finalState ∧ _ at suffixSound
          change
            HandledSteps handler (fuel + additional) context state
                finalContext finalState ∧ _
          exact ⟨prefixPath.trans suffixSound.1, suffixSound.2⟩
      | fault error faultState =>
          change ∃ spent, spent ≤ additional ∧ _ ∧ _ at suffixSound
          change ∃ spent, spent ≤ fuel + additional ∧ _ ∧ _
          obtain ⟨spent, bound, suffix, terminal⟩ := suffixSound
          exact ⟨fuel + spent, Nat.add_le_add_left bound fuel,
            prefixPath.trans suffix, terminal⟩
      | unsupported suspension remainingFuel =>
          change ∃ spent requestState, _ at suffixSound
          change ∃ spent requestState, _
          obtain ⟨spent, requestState, accounting, suffix, emission,
            unsupported⟩ := suffixSound
          exact ⟨fuel + spent, requestState, by omega,
            prefixPath.trans suffix, emission, unsupported⟩

end HostDriver

namespace HostDriverResult

/-- Splitting an actual run at any fuel boundary agrees with one larger run. -/
theorem resumeWithFuel_run
    {Context : Type u}
    (handler : HostHandler Context)
    (context : Context)
    (fuel additional : Nat)
    (state : Core.State) :
    (HostDriver.run handler context fuel state).resumeWithFuel
        handler additional =
      HostDriver.run handler context (fuel + additional) state := by
  cases execution : HostDriver.run handler context fuel state with
  | mk finalContext outcome =>
      cases outcome with
      | done value store =>
          simp only [resumeWithFuel_done]
          exact
            (HostDriver.run_done_stable handler execution (by omega)).symm
      | outOfFuel exhausted =>
          simp only [resumeWithFuel_outOfFuel]
          exact
            (HostDriver.run_additional_of_outOfFuel handler execution).symm
      | fault error faultState =>
          simp only [resumeWithFuel_fault]
          exact
            (HostDriver.run_fault_stable handler execution (by omega)).symm
      | unsupported suspension remainingFuel =>
          simp only [resumeWithFuel_unsupported]
          have sound := HostDriver.run_fuelSound handler context fuel state
          rw [execution] at sound
          change ∃ spent requestState, _ at sound
          obtain ⟨spent, requestState, accounting, path, emission,
            unsupported⟩ := sound
          exact (HostDriver.run_unsupported_complete handler path emission
            unsupported (by omega)).symm

/-- Zero additional fuel is an identity for every actual driver result. -/
@[simp] theorem resumeWithFuel_run_zero
    {Context : Type u}
    (handler : HostHandler Context)
    (context : Context)
    (fuel : Nat)
    (state : Core.State) :
    (HostDriver.run handler context fuel state).resumeWithFuel handler 0 =
      HostDriver.run handler context fuel state := by
  simpa using resumeWithFuel_run handler context fuel 0 state

/-- Sequential additions associate for every result under one fixed handler. -/
theorem resumeWithFuel_add
    {Context : Type u}
    (result : HostDriverResult Context)
    (handler : HostHandler Context)
    (first second : Nat) :
    (result.resumeWithFuel handler first).resumeWithFuel handler second =
      result.resumeWithFuel handler (first + second) := by
  cases result with
  | mk context outcome =>
      cases outcome with
      | done value store => rfl
      | outOfFuel state =>
          exact resumeWithFuel_run handler context first second state
      | fault error state => rfl
      | unsupported suspension remainingFuel =>
          simp only [resumeWithFuel_unsupported]
          rw [Nat.add_assoc]

/-- Two additions after an actual run equal the corresponding one-shot run. -/
theorem resumeWithFuel_run_add
    {Context : Type u}
    (handler : HostHandler Context)
    (context : Context)
    (fuel first second : Nat)
    (state : Core.State) :
    resumeWithFuel
        ((HostDriver.run handler context fuel state).resumeWithFuel
          handler first)
        handler second =
      HostDriver.run handler context (fuel + first + second) state := by
  rw [resumeWithFuel_run, resumeWithFuel_run]

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

/-!
## Consolidated module: `Solcore.ContractRuntime.HostDriverFrameContinuationProperties`
-/

/-! Exact branch, projection, and resolution laws for handled completion. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.HostDriverResult

universe u v w x

/-- A completed run retains its terminal context, value, and local store. -/
@[simp] theorem toFrameContinuationContext?_done
    {Context : Type x}
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : Context)
    (value : Core.Value)
    (store : Core.Store)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason) :
    toFrameContinuationContext?
        (HostDriverResult.mk context (.done value store))
        values doneOutcome =
      some (FrameContinuationContext.fromCheckpointedWorkingPair
        (values context) (doneOutcome context value store)) := by
  rfl

/-- Exhausted execution does not yet supply a frame continuation. -/
@[simp] theorem toFrameContinuationContext?_outOfFuel
    {Context : Type x}
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : Context)
    (state : Core.State)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason) :
    toFrameContinuationContext?
        (HostDriverResult.mk context (.outOfFuel state))
        values doneOutcome = none := by
  rfl

/-- A raw Core fault receives no implicit frame-trap interpretation. -/
@[simp] theorem toFrameContinuationContext?_fault
    {Context : Type x}
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : Context)
    (error : Core.MachineFault)
    (state : Core.State)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason) :
    toFrameContinuationContext?
        (HostDriverResult.mk context (.fault error state))
        values doneOutcome = none := by
  rfl

/-- A policy-rejected request is not a completed frame. -/
@[simp] theorem toFrameContinuationContext?_unsupported
    {Context : Type x}
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : Context)
    (suspension : Core.HostSuspension)
    (remainingFuel : Nat)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason) :
    toFrameContinuationContext?
        (HostDriverResult.mk context
          (.unsupported suspension remainingFuel))
        values doneOutcome = none := by
  rfl

/-- Completed construction retains the terminal checkpoint state exactly. -/
@[simp] theorem stateCheckpoint_toFrameContinuationContext?_done
    {Context : Type x}
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : Context)
    (value : Core.Value)
    (store : Core.Store)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason) :
    Option.map FrameContinuationContext.stateCheckpoint
        (toFrameContinuationContext?
          (HostDriverResult.mk context (.done value store))
          values doneOutcome) =
      some (values context).checkpoint.state := by
  rfl

/-- Completed construction retains the terminal checkpoint journal exactly. -/
@[simp] theorem effectCheckpoint_toFrameContinuationContext?_done
    {Context : Type x}
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : Context)
    (value : Core.Value)
    (store : Core.Store)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason) :
    Option.map FrameContinuationContext.effectCheckpoint
        (toFrameContinuationContext?
          (HostDriverResult.mk context (.done value store))
          values doneOutcome) =
      some (values context).checkpoint.effects := by
  rfl

/-- Completed construction retains the terminal working journal exactly. -/
@[simp] theorem effectWorking_toFrameContinuationContext?_done
    {Context : Type x}
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : Context)
    (value : Core.Value)
    (store : Core.Store)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason) :
    Option.map FrameContinuationContext.effectWorking
        (toFrameContinuationContext?
          (HostDriverResult.mk context (.done value store))
          values doneOutcome) =
      some (values context).working.2 := by
  rfl

/--
Completed construction pairs the terminal working world with the exact outcome
selected from the terminal context, Core value, and Core-local store.
-/
@[simp] theorem result_toFrameContinuationContext?_done
    {Context : Type x}
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : Context)
    (value : Core.Value)
    (store : Core.Store)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason) :
    Option.map FrameContinuationContext.result
        (toFrameContinuationContext?
          (HostDriverResult.mk context (.done value store))
          values doneOutcome) =
      some (FrameRunResult.mk
        (values context).working.1
        (doneOutcome context value store)) := by
  rfl

/-- A caller-selected return resolves the terminal working values. -/
theorem resolve_toFrameContinuationContext?_done_returned
    {Context : Type x}
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : Context)
    (value : Core.Value)
    (store : Core.Store)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason)
    (data : Bytes)
    (outcomeEq : doneOutcome context value store = .returned data) :
    Option.map FrameContinuationContext.resolve
        (toFrameContinuationContext?
          (HostDriverResult.mk context (.done value store))
          values doneOutcome) =
      some (FrameResolutionResult.returned
        (TrapReason := TrapReason)
        (values context).working.1 (values context).working.2 data) := by
  simp only [toFrameContinuationContext?_done, Option.map_some,
    FrameContinuationContext.resolve]
  rw [outcomeEq]
  rfl

/-- A caller-selected revert restores checkpoint state and rollback effects. -/
theorem resolve_toFrameContinuationContext?_done_reverted
    {Context : Type x}
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : Context)
    (value : Core.Value)
    (store : Core.Store)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason)
    (data : Bytes)
    (outcomeEq : doneOutcome context value store = .reverted data) :
    Option.map FrameContinuationContext.resolve
        (toFrameContinuationContext?
          (HostDriverResult.mk context (.done value store))
          values doneOutcome) =
      some (FrameResolutionResult.reverted
        (TrapReason := TrapReason)
        (values context).checkpoint.state
        ⟨(values context).checkpoint.effects.rollback,
          (values context).working.2.trace⟩
        data) := by
  simp only [toFrameContinuationContext?_done, Option.map_some,
    FrameContinuationContext.resolve]
  rw [outcomeEq]
  rfl

/-- A caller-selected trap resolves without inventing state disposition. -/
theorem resolve_toFrameContinuationContext?_done_trapped
    {Context : Type x}
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : Context)
    (value : Core.Value)
    (store : Core.Store)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason)
    (reason : TrapReason)
    (outcomeEq : doneOutcome context value store = .trapped reason) :
    Option.map FrameContinuationContext.resolve
        (toFrameContinuationContext?
          (HostDriverResult.mk context (.done value store))
          values doneOutcome) =
      some (FrameResolutionResult.trapped
        (RollbackState := RollbackState) (TraceState := TraceState)
        reason) := by
  simp only [toFrameContinuationContext?_done, Option.map_some,
    FrameContinuationContext.resolve]
  rw [outcomeEq]
  rfl

end Solcore.ContractRuntime.HostDriverResult
