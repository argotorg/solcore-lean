import Solcore.Semantics.HostStorageDriverProperties
import Solcore.Semantics.HostStorageDriverWithExecutionInputs
import Solcore.Semantics.HostStorageHandlerWithExecutionInputsProperties

/-! Execution and preservation laws for the explicit-input driver seam. -/

set_option autoImplicit false

namespace Solcore.Semantics.HostStorageDriver

universe u v

@[simp] theorem runWithInputs_of_done
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (value : Core.Value)
    (store : Core.Store)
    (execution : Core.hostRun fuel state = .done value store) :
    runWithInputs context inputs fuel state =
      ⟨context, .done value store⟩ := by
  exact run_of_done context inputs.codeAddress fuel state value store execution

@[simp] theorem runWithInputs_of_outOfFuel
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state exhausted : Core.State)
    (execution : Core.hostRun fuel state = .outOfFuel exhausted) :
    runWithInputs context inputs fuel state =
      ⟨context, .outOfFuel exhausted⟩ := by
  exact run_of_outOfFuel context inputs.codeAddress fuel state exhausted execution

@[simp] theorem runWithInputs_of_fault
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state faultState : Core.State)
    (error : Core.MachineFault)
    (execution : Core.hostRun fuel state = .fault error faultState) :
    runWithInputs context inputs fuel state =
      ⟨context, .fault error faultState⟩ := by
  exact run_of_fault context inputs.codeAddress fuel state faultState error execution

/-- Every suspension resumes under the same immutable input. -/
theorem runWithInputs_of_suspended
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (suspension : Core.HostSuspension)
    (execution :
      Core.hostRun fuel state = .suspended suspension remainingFuel) :
    runWithInputs context inputs fuel state =
      runWithInputs
        (handleSuspensionWithInputs inputs context suspension).1 inputs
        remainingFuel
        (handleSuspensionWithInputs inputs context suspension).2 := by
  exact run_of_suspended context inputs.codeAddress fuel remainingFuel
    state suspension execution

theorem runWithInputs_of_suspended_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.storageAddress, continuation, store⟩ remainingFuel) :
    runWithInputs context inputs fuel state =
      runWithInputs context inputs remainingFuel
        ⟨.ret (.word (addressToWord context.context.storageAddress)),
          continuation, store⟩ := by
  exact run_of_suspended_storageAddress context inputs.codeAddress fuel
    remainingFuel state continuation store execution

theorem runWithInputs_of_suspended_codeAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.codeAddress, continuation, store⟩ remainingFuel) :
    runWithInputs context inputs fuel state =
      runWithInputs context inputs remainingFuel
        ⟨.ret (.word (addressToWord inputs.codeAddress)), continuation, store⟩ := by
  exact run_of_suspended_codeAddress context inputs.codeAddress fuel
    remainingFuel state continuation store execution

@[simp] theorem runWithInputs_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    (runWithInputs context inputs fuel state).context.context.storageAddress =
      context.context.storageAddress := by
  exact run_storageAddress context inputs.codeAddress fuel state

@[simp] theorem runWithInputs_checkpoint
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    (runWithInputs context inputs fuel state).context.context.values.checkpoint =
      context.context.values.checkpoint := by
  exact run_checkpoint context inputs.codeAddress fuel state

@[simp] theorem runWithInputs_workingEffects
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    (runWithInputs context inputs fuel state).context.context.values.working.2 =
      context.context.values.working.2 := by
  exact run_workingEffects context inputs.codeAddress fuel state

@[simp] theorem runWithInputs_workingCode?
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (observedAddress : Address) :
    (runWithInputs context inputs fuel state).context.context.values.working.1.code?
        observedAddress =
      context.context.values.working.1.code? observedAddress := by
  exact run_workingCode? context inputs.codeAddress fuel state observedAddress

@[simp] theorem runWithInputs_workingAccount?_of_ne_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (observedAddress : Address)
    (different : observedAddress ≠ context.context.storageAddress) :
    (runWithInputs context inputs fuel state).context.context.values.working.1.account?
        observedAddress =
      context.context.values.working.1.account? observedAddress := by
  exact run_workingAccount?_of_ne_storageAddress context inputs.codeAddress
    fuel state observedAddress different

end Solcore.Semantics.HostStorageDriver
