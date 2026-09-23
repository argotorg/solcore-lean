import Solcore.ContractRuntime.HostDriverCompletenessProperties
import Solcore.ContractRuntime.HostDriverResumptionProperties
import Solcore.ContractRuntime.HostStorageDriverProperties

/-! Whole-run fuel accounting indexed by immutable execution inputs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

namespace HostStorageDriver

/-- Handled transition segments under one exact immutable input. -/
abbrev HandledSteps
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs) :=
  HostDriver.HandledSteps
    (@handler RollbackState TraceState inputs)

/-- Fuel soundness indexed by one exact immutable input. -/
def FuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (result : HostDriverResult (Context RollbackState TraceState))
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (startContext : Context RollbackState TraceState)
    (start : Core.State) : Prop :=
  result.FuelSoundWith
    (@handler RollbackState TraceState inputs)
    fuel startContext start

namespace FuelSound

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
    (supported :
      (@handler RollbackState TraceState inputs).supports
        suspension.request = true)
    (handled :
      handleSuspension inputs context suspension =
        (nextContext, resumed))
    (accounting : prefixSteps + remainingFuel + 1 = fuel)
    (suffixSound :
      HostStorageDriver.FuelSound
        result inputs remainingFuel nextContext resumed) :
    HostStorageDriver.FuelSound
      result inputs fuel context start := by
  apply HostDriverResult.FuelSoundWith.prependRequest
    prefixPath emission supported (accounting := accounting)
  · simpa only [handleSuspension] using handled
  · exact suffixSound

end FuelSound

theorem run_fuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    FuelSound (run context inputs fuel state) inputs
      fuel context state := by
  simpa only [run, FuelSound] using
    HostDriver.run_fuelSound
      (@handler RollbackState TraceState inputs)
      context fuel state

theorem run_eq_of_fuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (result : HostDriverResult (Context RollbackState TraceState))
    (sound : FuelSound result inputs fuel context state) :
    run context inputs fuel state = result := by
  simpa only [run, FuelSound] using
    HostDriver.run_eq_of_fuelSoundWith
      (@handler RollbackState TraceState inputs)
      context fuel state result sound

theorem run_eq_iff_fuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (result : HostDriverResult (Context RollbackState TraceState)) :
    run context inputs fuel state = result ↔
      FuelSound result inputs fuel context state := by
  simpa only [run, FuelSound] using
    HostDriver.run_eq_iff_fuelSoundWith
      (@handler RollbackState TraceState inputs)
      context fuel state result

/-- Exhausted storage execution resumes under the exact same immutable input. -/
theorem run_additional_of_outOfFuel
    {RollbackState : Type u} {TraceState : Type v}
    (context nextContext : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel additional : Nat)
    (state exhausted : Core.State)
    (execution :
      run context inputs fuel state =
        ⟨nextContext, .outOfFuel exhausted⟩) :
    run context inputs (fuel + additional) state =
      run nextContext inputs additional exhausted := by
  simpa only [run] using
    HostDriver.run_additional_of_outOfFuel
      (@handler RollbackState TraceState inputs) execution

/-- Split storage execution agrees with one summed-budget run. -/
theorem resumeWithFuel_run
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel additional : Nat)
    (state : Core.State) :
    (run context inputs fuel state).resumeWithFuel
        (@handler RollbackState TraceState inputs) additional =
      run context inputs (fuel + additional) state := by
  simpa only [run] using
    HostDriverResult.resumeWithFuel_run
      (@handler RollbackState TraceState inputs)
      context fuel additional state

theorem run_done_stable
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    {fuel largerFuel : Nat}
    (state : Core.State)
    {finalContext : Context RollbackState TraceState}
    {value : Core.Value} {store : Core.Store}
    (execution :
      run context inputs fuel state =
        ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    run context inputs largerFuel state =
      ⟨finalContext, .done value store⟩ := by
  simpa only [run] using
    HostDriver.run_done_stable
      (@handler RollbackState TraceState inputs)
      execution more

end HostStorageDriver

namespace CheckedHostCoreProgram

theorem runWithStorage_fuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    HostStorageDriver.FuelSound
      (code.runWithStorage context inputs fuel) inputs fuel context
      (Core.State.initial code.program.body Core.hostEnvironment) := by
  exact HostStorageDriver.run_fuelSound context inputs fuel _

theorem runWithStorage_eq_iff_fuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState)) :
    code.runWithStorage context inputs fuel = result ↔
      HostStorageDriver.FuelSound result inputs fuel context
        (Core.State.initial code.program.body Core.hostEnvironment) := by
  simpa only [runWithStorage] using
    HostStorageDriver.run_eq_iff_fuelSound context inputs fuel
      (Core.State.initial code.program.body Core.hostEnvironment) result

theorem runWithStorage_done_stable
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel largerFuel : Nat}
    {finalContext : HostStorageDriver.Context RollbackState TraceState}
    {value : Core.Value} {store : Core.Store}
    (execution :
      code.runWithStorage context inputs fuel =
        ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    code.runWithStorage context inputs largerFuel =
      ⟨finalContext, .done value store⟩ := by
  simpa only [runWithStorage] using
    HostStorageDriver.run_done_stable context inputs
      (Core.State.initial code.program.body Core.hostEnvironment)
      execution more

/-- Checked storage execution has the same exact split-fuel law. -/
theorem runWithStorage_resumeWithFuel
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel additional : Nat) :
    (code.runWithStorage context inputs fuel).resumeWithFuel
        (@HostStorageDriver.handler RollbackState TraceState inputs)
        additional =
      code.runWithStorage context inputs (fuel + additional) := by
  simpa only [runWithStorage] using
    HostStorageDriver.resumeWithFuel_run context inputs fuel additional
      (Core.State.initial code.program.body Core.hostEnvironment)

end CheckedHostCoreProgram

end Solcore.ContractRuntime
