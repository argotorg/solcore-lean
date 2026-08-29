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
          handled suffix =>
          have combinedPrefix := leftPath.trans prefixPath
          have combined :=
            HandledSteps.handle combinedPrefix emission handled suffix
          simpa [Nat.add_assoc] using combined
  | @handle prefixSteps suffixSteps context nextContext middleContext
      start requestState resumed middle suspension prefixPath emission
      handled suffix suffixIH =>
      have combinedSuffix := suffixIH right
      have combined :=
        HandledSteps.handle prefixPath emission handled combinedSuffix
      simpa [Nat.add_assoc] using combined

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
            .handle prefixPath emission handled suffix⟩
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
              prefixPath emission handled suffix
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
            .handle prefixPath emission handled suffix, terminal⟩

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
          rw [run, execution]
          obtain ⟨prefixSteps, requestState, prefixPath, emission, accounting⟩ :=
            Core.hostRun_suspended_sound execution
          apply HostDriverResult.FuelSoundWith.prependRequest
            prefixPath emission
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
