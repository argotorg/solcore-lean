import Solcore.Semantics.HostDriverCompletenessProperties
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

/-- Fuel evidence for the combined handler determines its executable result. -/
theorem run_eq_of_fuelSound
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (fuel : Nat)
    (state : Core.State)
    (result : HostDriverResult (Context RollbackState TraceState))
    (sound : FuelSound result fuel context state) :
    run context fuel state = result := by
  simpa only [run, FuelSound] using
    HostDriver.run_eq_of_fuelSoundWith
      (@handler RollbackState TraceState)
      context fuel state result sound

/-- Combined storage execution is exactly its handled fuel specification. -/
theorem run_eq_iff_fuelSound
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (fuel : Nat)
    (state : Core.State)
    (result : HostDriverResult (Context RollbackState TraceState)) :
    run context fuel state = result ↔
      FuelSound result fuel context state := by
  simpa only [run, FuelSound] using
    HostDriver.run_eq_iff_fuelSoundWith
      (@handler RollbackState TraceState)
      context fuel state result

/-- A completed combined-storage result is stable under additional fuel. -/
theorem run_done_stable
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    {fuel largerFuel : Nat}
    (state : Core.State)
    {finalContext : Context RollbackState TraceState}
    {value : Core.Value}
    {store : Core.Store}
    (execution :
      run context fuel state =
        ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    run context largerFuel state =
      ⟨finalContext, .done value store⟩ := by
  simpa only [run] using
    HostDriver.run_done_stable
      (@handler RollbackState TraceState)
      execution more

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

/-- Checked combined execution is exactly its handled fuel specification. -/
theorem runWithStorage_eq_iff_fuelSound
    {RollbackState : Type u}
    {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (fuel : Nat)
    (result :
      HostDriverResult
        (HostStorageDriver.Context RollbackState TraceState)) :
    code.runWithStorage context fuel = result ↔
      HostStorageDriver.FuelSound
        result fuel context
        (Core.State.initial code.program.body Core.hostEnvironment) := by
  simpa only [runWithStorage] using
    HostStorageDriver.run_eq_iff_fuelSound
      context fuel
      (Core.State.initial code.program.body Core.hostEnvironment)
      result

/-- A checked completed result is unchanged when supplied more fuel. -/
theorem runWithStorage_done_stable
    {RollbackState : Type u}
    {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    {fuel largerFuel : Nat}
    {finalContext :
      HostStorageDriver.Context RollbackState TraceState}
    {value : Core.Value}
    {store : Core.Store}
    (execution :
      code.runWithStorage context fuel =
        ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    code.runWithStorage context largerFuel =
      ⟨finalContext, .done value store⟩ := by
  simpa only [runWithStorage] using
    HostStorageDriver.run_done_stable
      context
      (Core.State.initial code.program.body Core.hostEnvironment)
      execution more

end CheckedHostCoreProgram

end Solcore.Semantics
