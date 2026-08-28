import Solcore.Semantics.HostStorageReadDriverProperties

/-! Whole-run transition and fuel accounting for handled host execution. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

namespace HostStorageReadDriver

/-- Core transition segments joined by handled request boundaries. -/
inductive HandledSteps
    {RollbackState : Type u}
    {TraceState : Type v} :
    Nat →
      Context RollbackState TraceState → Core.State →
      Context RollbackState TraceState → Core.State → Prop where
  | core
      {steps : Nat}
      {context : Context RollbackState TraceState}
      {start finish : Core.State}
      (path : Core.HostSteps steps start finish) :
      HandledSteps steps context start context finish
  | handle
      {prefixSteps suffixSteps : Nat}
      {context nextContext finalContext :
        Context RollbackState TraceState}
      {start requestState resumed finish : Core.State}
      {suspension : Core.HostSuspension}
      (prefixPath : Core.HostSteps prefixSteps start requestState)
      (emission : Core.HostRequestEmission requestState suspension)
      (handled :
        handleHostSuspension context suspension = (nextContext, resumed))
      (suffix :
        HandledSteps suffixSteps nextContext resumed finalContext finish) :
      HandledSteps (prefixSteps + 1 + suffixSteps)
        context start finalContext finish

end HostStorageReadDriver

namespace HostDriverResult

/--
Completion and faults consume at most the supplied budget. Exhaustion consumes
it exactly and retains a state ready for another transition or request.
-/
def FuelSound
    {RollbackState : Type u}
    {TraceState : Type v}
    (result :
      HostDriverResult
        (HostStorageReadDriver.Context RollbackState TraceState))
    (fuel : Nat)
    (startContext :
      HostStorageReadDriver.Context RollbackState TraceState)
    (start : Core.State) : Prop :=
  match result.outcome with
  | .done value store =>
      ∃ spent,
        spent ≤ fuel ∧
          HostStorageReadDriver.HandledSteps spent startContext start
            result.context (Core.State.final value store)
  | .outOfFuel exhausted =>
      HostStorageReadDriver.HandledSteps fuel startContext start
          result.context exhausted ∧
        ((∃ next, Core.HostTransition exhausted next) ∨
          ∃ suspension, Core.HostRequestEmission exhausted suspension)
  | .fault error faultState =>
      ∃ spent,
        spent ≤ fuel ∧
          HostStorageReadDriver.HandledSteps spent startContext start
            result.context faultState ∧
          Core.hostAdvance faultState = .fault error

namespace FuelSound

/-- Prefix a sound driven suffix with one emitted and handled request. -/
theorem prependRequest
    {RollbackState : Type u}
    {TraceState : Type v}
    {result :
      HostDriverResult
        (HostStorageReadDriver.Context RollbackState TraceState)}
    {fuel remainingFuel prefixSteps : Nat}
    {context nextContext :
      HostStorageReadDriver.Context RollbackState TraceState}
    {start requestState resumed : Core.State}
    {suspension : Core.HostSuspension}
    (prefixPath : Core.HostSteps prefixSteps start requestState)
    (emission : Core.HostRequestEmission requestState suspension)
    (handled :
      HostStorageReadDriver.handleHostSuspension context suspension =
        (nextContext, resumed))
    (accounting : prefixSteps + remainingFuel + 1 = fuel)
    (suffixSound : result.FuelSound remainingFuel nextContext resumed) :
    result.FuelSound fuel context start := by
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
            HostStorageReadDriver.HandledSteps remainingFuel nextContext
                resumed finalContext exhausted ∧ _ at suffixSound
          change
            HostStorageReadDriver.HandledSteps fuel context start
                finalContext exhausted ∧ _
          obtain ⟨suffix, ready⟩ := suffixSound
          have combined :=
            HostStorageReadDriver.HandledSteps.handle
              prefixPath emission handled suffix
          have countEq : prefixSteps + 1 + remainingFuel = fuel := by
            omega
          exact ⟨countEq ▸ combined, ready⟩
      | fault error faultState =>
          change
            ∃ spent,
              spent ≤ remainingFuel ∧
                HostStorageReadDriver.HandledSteps spent nextContext resumed
                  finalContext faultState ∧
                Core.hostAdvance faultState = .fault error at suffixSound
          change
            ∃ spent,
              spent ≤ fuel ∧
                HostStorageReadDriver.HandledSteps spent context start
                  finalContext faultState ∧
                Core.hostAdvance faultState = .fault error
          obtain ⟨suffixSteps, suffixBound, suffix, terminal⟩ := suffixSound
          exact ⟨prefixSteps + 1 + suffixSteps, by omega,
            .handle prefixPath emission handled suffix, terminal⟩

end FuelSound

end HostDriverResult

namespace HostStorageReadDriver

/-- The executable driver exactly respects Core's finite fuel accounting. -/
theorem run_fuelSound
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (fuel : Nat)
    (state : Core.State) :
    (run context fuel state).FuelSound fuel context state := by
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
          apply HostDriverResult.FuelSound.prependRequest
            prefixPath emission
            (nextContext := (handleHostSuspension context suspension).1)
            (resumed := (handleHostSuspension context suspension).2)
          · exact (Prod.eta (handleHostSuspension context suspension)).symm
          · exact accounting
          · exact ih remainingFuel
              (Core.HostRunResult.remainingFuel_lt execution)
              (handleHostSuspension context suspension).1
              (handleHostSuspension context suspension).2

end HostStorageReadDriver

namespace CheckedHostCoreProgram

/-- Checked execution inherits the complete handled-step fuel account. -/
theorem runWithStorageReads_fuelSound
    {RollbackState : Type u}
    {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageReadDriver.Context RollbackState TraceState)
    (fuel : Nat) :
    (code.runWithStorageReads context fuel).FuelSound fuel context
      (Core.State.initial code.program.body Core.hostEnvironment) := by
  exact HostStorageReadDriver.run_fuelSound context fuel _

end CheckedHostCoreProgram

end Solcore.Semantics
