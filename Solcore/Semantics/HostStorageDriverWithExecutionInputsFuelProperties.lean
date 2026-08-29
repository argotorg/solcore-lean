import Solcore.Semantics.HostDriverCompletenessProperties
import Solcore.Semantics.HostStorageDriverWithExecutionInputsProperties

/-! Whole-run fuel accounting indexed by immutable execution inputs. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

namespace HostStorageDriver

/-- Handled transition segments under one exact immutable input. -/
abbrev HandledStepsWithInputs
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs) :=
  HostDriver.HandledSteps
    (@handler RollbackState TraceState inputs)

/-- Fuel soundness indexed by one exact immutable input. -/
def FuelSoundWithInputs
    {RollbackState : Type u} {TraceState : Type v}
    (result : HostDriverResult (Context RollbackState TraceState))
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (startContext : Context RollbackState TraceState)
    (start : Core.State) : Prop :=
  result.FuelSoundWith
    (@handler RollbackState TraceState inputs)
    fuel startContext start

namespace FuelSoundWithInputs

/-- Prefix a sound suffix with one request handled under the same input. -/
theorem prependRequest
    {RollbackState : Type u} {TraceState : Type v}
    {inputs : ExecutionInputs}
    {result : HostDriverResult (Context RollbackState TraceState)}
    {fuel remainingFuel prefixSteps : Nat}
    {context nextContext : Context RollbackState TraceState}
    {start requestState resumed : Core.State}
    {suspension : Core.HostSuspension}
    (prefixPath : Core.HostSteps prefixSteps start requestState)
    (emission : Core.HostRequestEmission requestState suspension)
    (handled :
      handleSuspension inputs context suspension =
        (nextContext, resumed))
    (accounting : prefixSteps + remainingFuel + 1 = fuel)
    (suffixSound :
      HostStorageDriver.FuelSoundWithInputs
        result inputs remainingFuel nextContext resumed) :
    HostStorageDriver.FuelSoundWithInputs
      result inputs fuel context start := by
  apply HostDriverResult.FuelSoundWith.prependRequest
    prefixPath emission (accounting := accounting)
  · simpa only [handleSuspension] using handled
  · exact suffixSound

end FuelSoundWithInputs

theorem runWithInputs_fuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    FuelSoundWithInputs (runWithInputs context inputs fuel state) inputs
      fuel context state := by
  simpa only [runWithInputs, FuelSoundWithInputs] using
    HostDriver.run_fuelSound
      (@handler RollbackState TraceState inputs)
      context fuel state

theorem runWithInputs_eq_of_fuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (result : HostDriverResult (Context RollbackState TraceState))
    (sound : FuelSoundWithInputs result inputs fuel context state) :
    runWithInputs context inputs fuel state = result := by
  simpa only [runWithInputs, FuelSoundWithInputs] using
    HostDriver.run_eq_of_fuelSoundWith
      (@handler RollbackState TraceState inputs)
      context fuel state result sound

theorem runWithInputs_eq_iff_fuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (result : HostDriverResult (Context RollbackState TraceState)) :
    runWithInputs context inputs fuel state = result ↔
      FuelSoundWithInputs result inputs fuel context state := by
  simpa only [runWithInputs, FuelSoundWithInputs] using
    HostDriver.run_eq_iff_fuelSoundWith
      (@handler RollbackState TraceState inputs)
      context fuel state result

theorem runWithInputs_done_stable
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    {fuel largerFuel : Nat}
    (state : Core.State)
    {finalContext : Context RollbackState TraceState}
    {value : Core.Value} {store : Core.Store}
    (execution :
      runWithInputs context inputs fuel state =
        ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    runWithInputs context inputs largerFuel state =
      ⟨finalContext, .done value store⟩ := by
  simpa only [runWithInputs] using
    HostDriver.run_done_stable
      (@handler RollbackState TraceState inputs)
      execution more

end HostStorageDriver

namespace CheckedHostCoreProgram

theorem runWithStorageInputs_fuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    HostStorageDriver.FuelSoundWithInputs
      (code.runWithStorageInputs context inputs fuel) inputs fuel context
      (Core.State.initial code.program.body Core.hostEnvironment) := by
  exact HostStorageDriver.runWithInputs_fuelSound context inputs fuel _

theorem runWithStorageInputs_eq_iff_fuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState)) :
    code.runWithStorageInputs context inputs fuel = result ↔
      HostStorageDriver.FuelSoundWithInputs result inputs fuel context
        (Core.State.initial code.program.body Core.hostEnvironment) := by
  simpa only [runWithStorageInputs] using
    HostStorageDriver.runWithInputs_eq_iff_fuelSound context inputs fuel
      (Core.State.initial code.program.body Core.hostEnvironment) result

theorem runWithStorageInputs_done_stable
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel largerFuel : Nat}
    {finalContext : HostStorageDriver.Context RollbackState TraceState}
    {value : Core.Value} {store : Core.Store}
    (execution :
      code.runWithStorageInputs context inputs fuel =
        ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    code.runWithStorageInputs context inputs largerFuel =
      ⟨finalContext, .done value store⟩ := by
  simpa only [runWithStorageInputs] using
    HostStorageDriver.runWithInputs_done_stable context inputs
      (Core.State.initial code.program.body Core.hostEnvironment)
      execution more

end CheckedHostCoreProgram

end Solcore.Semantics
