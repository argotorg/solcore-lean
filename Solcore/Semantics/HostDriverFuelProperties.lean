import Solcore.Semantics.HostDriverProperties

/-! Generic whole-run transition and fuel accounting for handled host execution. -/

set_option autoImplicit false

namespace Solcore.Semantics

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
it exactly and retains a state ready for another transition or request.
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

end Solcore.Semantics
