import Solcore.Semantics.HostDriverFuelProperties
import Solcore.Semantics.HostStorageDriverProperties

/-! Whole-run fuel accounting for combined handled storage execution. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

namespace HostStorageDriver

/-- Transition segments specialized to the combined storage handler. -/
abbrev HandledSteps
    {RollbackState : Type u}
    {TraceState : Type v} :=
  HostDriver.HandledSteps
    (@handler RollbackState TraceState)

/-- Generic fuel soundness specialized without occupying the global dot API. -/
def FuelSound
    {RollbackState : Type u}
    {TraceState : Type v}
    (result : HostDriverResult (Context RollbackState TraceState))
    (fuel : Nat)
    (startContext : Context RollbackState TraceState)
    (start : Core.State) : Prop :=
  result.FuelSoundWith
    (@handler RollbackState TraceState)
    fuel startContext start

namespace FuelSound

/-- Prefix a sound combined-storage suffix with one handled request. -/
theorem prependRequest
    {RollbackState : Type u}
    {TraceState : Type v}
    {result : HostDriverResult (Context RollbackState TraceState)}
    {fuel remainingFuel prefixSteps : Nat}
    {context nextContext : Context RollbackState TraceState}
    {start requestState resumed : Core.State}
    {suspension : Core.HostSuspension}
    (prefixPath : Core.HostSteps prefixSteps start requestState)
    (emission : Core.HostRequestEmission requestState suspension)
    (handled :
      handleSuspension context suspension = (nextContext, resumed))
    (accounting : prefixSteps + remainingFuel + 1 = fuel)
    (suffixSound :
      HostStorageDriver.FuelSound
        result remainingFuel nextContext resumed) :
    HostStorageDriver.FuelSound result fuel context start := by
  apply HostDriverResult.FuelSoundWith.prependRequest
    prefixPath emission (accounting := accounting)
  · simpa only [handleSuspension] using handled
  · exact suffixSound

end FuelSound

/-- The combined storage driver inherits generic finite-fuel accounting. -/
theorem run_fuelSound
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (fuel : Nat)
    (state : Core.State) :
    FuelSound (run context fuel state) fuel context state := by
  simpa only [run, FuelSound] using
    HostDriver.run_fuelSound
      (@handler RollbackState TraceState)
      context fuel state

end HostStorageDriver

namespace CheckedHostCoreProgram

/-- Checked combined execution inherits generic handled-step fuel soundness. -/
theorem runWithStorage_fuelSound
    {RollbackState : Type u}
    {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (fuel : Nat) :
    HostStorageDriver.FuelSound
      (code.runWithStorage context fuel)
      fuel context
      (Core.State.initial code.program.body Core.hostEnvironment) := by
  exact HostStorageDriver.run_fuelSound context fuel _

end CheckedHostCoreProgram

end Solcore.Semantics
