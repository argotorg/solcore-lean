import Solcore.Semantics.HostDriverFuelProperties
import Solcore.Semantics.HostStorageReadDriverProperties

/-! Whole-run transition and fuel accounting for handled host execution. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

namespace HostStorageReadDriver

/-- Compatibility name for read-handler transition segments. -/
abbrev HandledSteps
    {RollbackState : Type u}
    {TraceState : Type v} :=
  HostDriver.HandledSteps
    (@handler RollbackState TraceState)

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
  result.FuelSoundWith
    (@HostStorageReadDriver.handler RollbackState TraceState)
    fuel startContext start

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
  have handledGeneric :
      HostStorageReadDriver.handler.handleSuspension context suspension =
        (nextContext, resumed) := by
    simpa only [HostStorageReadDriver.handler_handleSuspension] using handled
  cases result with
  | mk finalContext outcome =>
      cases outcome with
      | done value store =>
          change ∃ spent, spent ≤ remainingFuel ∧ _ at suffixSound
          change ∃ spent, spent ≤ fuel ∧ _
          obtain ⟨suffixSteps, suffixBound, suffix⟩ := suffixSound
          exact ⟨prefixSteps + 1 + suffixSteps, by omega,
            .handle prefixPath emission handledGeneric suffix⟩
      | outOfFuel exhausted =>
          change
            HostStorageReadDriver.HandledSteps remainingFuel nextContext
                resumed finalContext exhausted ∧ _ at suffixSound
          change
            HostStorageReadDriver.HandledSteps fuel context start
                finalContext exhausted ∧ _
          obtain ⟨suffix, ready⟩ := suffixSound
          have combined :=
            HostDriver.HandledSteps.handle
              prefixPath emission handledGeneric suffix
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
            .handle prefixPath emission handledGeneric suffix, terminal⟩

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
  simpa only [run, HostDriverResult.FuelSound] using
    HostDriver.run_fuelSound
      (@handler RollbackState TraceState)
      context fuel state

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
