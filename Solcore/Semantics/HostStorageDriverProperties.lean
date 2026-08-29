import Solcore.Semantics.CheckedHostCoreProgramProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteCodeProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteIsolationProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteProjectionProperties
import Solcore.Semantics.HostStorageDriver
import Solcore.Semantics.HostStorageHandlerProperties

/-! Equations and type safety for combined handled storage execution. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

namespace HostStorageDriver

@[simp] theorem run_of_done
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (state : Core.State)
    (value : Core.Value)
    (store : Core.Store)
    (execution : Core.hostRun fuel state = .done value store) :
    run context codeAddress fuel state = ⟨context, .done value store⟩ := by
  simpa only [run] using
    HostDriver.run_of_done
      (@handler RollbackState TraceState codeAddress)
      context fuel state value store execution

@[simp] theorem run_of_outOfFuel
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (state exhausted : Core.State)
    (execution : Core.hostRun fuel state = .outOfFuel exhausted) :
    run context codeAddress fuel state = ⟨context, .outOfFuel exhausted⟩ := by
  simpa only [run] using
    HostDriver.run_of_outOfFuel
      (@handler RollbackState TraceState codeAddress)
      context fuel state exhausted execution

@[simp] theorem run_of_fault
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (state faultState : Core.State)
    (error : Core.MachineFault)
    (execution : Core.hostRun fuel state = .fault error faultState) :
    run context codeAddress fuel state = ⟨context, .fault error faultState⟩ := by
  simpa only [run] using
    HostDriver.run_of_fault
      (@handler RollbackState TraceState codeAddress)
      context fuel state faultState error execution

/-- A supported host request resumes with exactly Core's returned remaining fuel. -/
theorem run_of_suspended
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (codeAddress : Address)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (suspension : Core.HostSuspension)
    (execution :
      Core.hostRun fuel state = .suspended suspension remainingFuel) :
    run context codeAddress fuel state =
      run (handleSuspension codeAddress context suspension).1 codeAddress
        remainingFuel (handleSuspension codeAddress context suspension).2 := by
  simpa only [run, handleSuspension] using
    HostDriver.run_of_suspended
      (@handler RollbackState TraceState codeAddress)
      context fuel remainingFuel state suspension execution

/--
A storage-selector observation resumes with the exact widened Word and exactly
the remaining fuel returned by Core.
-/
theorem run_of_suspended_storageAddress
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (codeAddress : Address)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.storageAddress, continuation, store⟩ remainingFuel) :
    run context codeAddress fuel state =
      run context codeAddress remainingFuel
        ⟨.ret (.word (addressToWord context.context.storageAddress)),
          continuation, store⟩ := by
  calc
    run context codeAddress fuel state =
        run
          (handleSuspension codeAddress context
            ⟨.storageAddress, continuation, store⟩).1
          codeAddress remainingFuel
          (handleSuspension codeAddress context
            ⟨.storageAddress, continuation, store⟩).2 :=
      run_of_suspended context codeAddress fuel remainingFuel state _ execution
    _ = _ := by rw [handleSuspension_storageAddress]

/--
A code-selector observation resumes with the exact widened Word and exactly
the remaining fuel returned by Core.
-/
theorem run_of_suspended_codeAddress
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (codeAddress : Address)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.codeAddress, continuation, store⟩ remainingFuel) :
    run context codeAddress fuel state =
      run context codeAddress remainingFuel
        ⟨.ret (.word (addressToWord codeAddress)), continuation, store⟩ := by
  calc
    run context codeAddress fuel state =
        run
          (handleSuspension codeAddress context
            ⟨.codeAddress, continuation, store⟩).1
          codeAddress remainingFuel
          (handleSuspension codeAddress context
            ⟨.codeAddress, continuation, store⟩).2 :=
      run_of_suspended context codeAddress fuel remainingFuel state _ execution
    _ = _ := by rw [handleSuspension_codeAddress]

/-- A combined handled run retains the selected storage Address. -/
@[simp] theorem run_storageAddress
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (state : Core.State) :
    (run context codeAddress fuel state).context.context.storageAddress =
      context.context.storageAddress := by
  simpa only [run] using
    HostDriver.run_observe
      (@handler RollbackState TraceState codeAddress)
      (fun current => current.context.storageAddress)
      (by
        intro current request
        cases request <;> simp [handler, handleRequest])
      context fuel state

/-- A combined handled run retains the complete checkpoint. -/
@[simp] theorem run_checkpoint
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (state : Core.State) :
    (run context codeAddress fuel state).context.context.values.checkpoint =
      context.context.values.checkpoint := by
  simpa only [run] using
    HostDriver.run_observe
      (@handler RollbackState TraceState codeAddress)
      (fun current => current.context.values.checkpoint)
      (by
        intro current request
        cases request <;> simp [handler, handleRequest])
      context fuel state

/-- A combined handled run retains the complete working effect journal. -/
@[simp] theorem run_workingEffects
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (state : Core.State) :
    (run context codeAddress fuel state).context.context.values.working.2 =
      context.context.values.working.2 := by
  simpa only [run] using
    HostDriver.run_observe
      (@handler RollbackState TraceState codeAddress)
      (fun current => current.context.values.working.2)
      (by
        intro current request
        cases request <;> simp [handler, handleRequest])
      context fuel state

/-- A combined handled run retains checked code at every working Address. -/
@[simp] theorem run_workingCode?
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (state : Core.State)
    (observedCodeAddress : Address) :
    (run context codeAddress fuel state).context.context.values.working.1.code?
        observedCodeAddress =
      context.context.values.working.1.code? observedCodeAddress := by
  simpa only [run] using
    HostDriver.run_observe
      (@handler RollbackState TraceState codeAddress)
      (fun current => current.context.values.working.1.code? observedCodeAddress)
      (by
        intro current request
        cases request <;> simp [handler, handleRequest])
      context fuel state

end HostStorageDriver

end Solcore.Semantics
