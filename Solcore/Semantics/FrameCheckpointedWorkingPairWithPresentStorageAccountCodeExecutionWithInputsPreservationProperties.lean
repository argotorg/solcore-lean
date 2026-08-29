import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecutionWithInputs
import Solcore.Semantics.HostStorageDriverWithExecutionInputsFuelProperties
import Solcore.Semantics.HostStorageDriverWithExecutionInputsProperties

/-! Preservation and stability laws for explicit-input selected execution. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

namespace FrameCheckpointedWorkingPairWithPresentStorageAccount

theorem runCodeWithStorageWithInputs?_some_workingCode?
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result : HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (executed :
      context.runCodeWithStorageWithInputs? inputs fuel = some result)
    (observedAddress : Address) :
    result.context.context.values.working.1.code? observedAddress =
      context.context.values.working.1.code? observedAddress := by
  unfold runCodeWithStorageWithInputs? at executed
  cases selected :
      context.context.values.working.1.code? inputs.codeAddress with
  | none => simp [selected] at executed
  | some code =>
      rw [selected] at executed
      have resultEq := Option.some.inj executed
      subst result
      simpa only [CheckedHostCoreProgram.runWithStorage] using
        HostStorageDriver.run_workingCode?
          context inputs fuel
          (Core.State.initial code.program.body Core.hostEnvironment)
          observedAddress

theorem runCodeWithStorageWithInputs?_some_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result : HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (executed :
      context.runCodeWithStorageWithInputs? inputs fuel = some result) :
    result.context.context.storageAddress = context.context.storageAddress := by
  unfold runCodeWithStorageWithInputs? at executed
  cases selected :
      context.context.values.working.1.code? inputs.codeAddress with
  | none => simp [selected] at executed
  | some code =>
      rw [selected] at executed
      have resultEq := Option.some.inj executed
      subst result
      simpa only [CheckedHostCoreProgram.runWithStorage] using
        HostStorageDriver.run_storageAddress context inputs fuel
          (Core.State.initial code.program.body Core.hostEnvironment)

theorem runCodeWithStorageWithInputs?_some_checkpoint
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result : HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (executed :
      context.runCodeWithStorageWithInputs? inputs fuel = some result) :
    result.context.context.values.checkpoint =
      context.context.values.checkpoint := by
  unfold runCodeWithStorageWithInputs? at executed
  cases selected :
      context.context.values.working.1.code? inputs.codeAddress with
  | none => simp [selected] at executed
  | some code =>
      rw [selected] at executed
      have resultEq := Option.some.inj executed
      subst result
      simpa only [CheckedHostCoreProgram.runWithStorage] using
        HostStorageDriver.run_checkpoint context inputs fuel
          (Core.State.initial code.program.body Core.hostEnvironment)

theorem runCodeWithStorageWithInputs?_some_workingEffects
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result : HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (executed :
      context.runCodeWithStorageWithInputs? inputs fuel = some result) :
    result.context.context.values.working.2 =
      context.context.values.working.2 := by
  unfold runCodeWithStorageWithInputs? at executed
  cases selected :
      context.context.values.working.1.code? inputs.codeAddress with
  | none => simp [selected] at executed
  | some code =>
      rw [selected] at executed
      have resultEq := Option.some.inj executed
      subst result
      simpa only [CheckedHostCoreProgram.runWithStorage] using
        HostStorageDriver.run_workingEffects context inputs fuel
          (Core.State.initial code.program.body Core.hostEnvironment)

theorem runCodeWithStorageWithInputs?_some_workingAccount?_of_ne_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result : HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (executed :
      context.runCodeWithStorageWithInputs? inputs fuel = some result)
    (observedAddress : Address)
    (different : observedAddress ≠ context.context.storageAddress) :
    result.context.context.values.working.1.account? observedAddress =
      context.context.values.working.1.account? observedAddress := by
  unfold runCodeWithStorageWithInputs? at executed
  cases selected :
      context.context.values.working.1.code? inputs.codeAddress with
  | none => simp [selected] at executed
  | some code =>
      rw [selected] at executed
      have resultEq := Option.some.inj executed
      subst result
      simpa only [CheckedHostCoreProgram.runWithStorage] using
        HostStorageDriver.run_workingAccount?_of_ne_storageAddress
          context inputs fuel
          (Core.State.initial code.program.body Core.hostEnvironment)
          observedAddress different

theorem runCodeWithStorageWithInputs?_some_done_stable
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel largerFuel : Nat}
    {resultContext : HostStorageDriver.Context RollbackState TraceState}
    {value : Core.Value} {store : Core.Store}
    (execution :
      context.runCodeWithStorageWithInputs? inputs fuel =
        some ⟨resultContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    context.runCodeWithStorageWithInputs? inputs largerFuel =
      some ⟨resultContext, .done value store⟩ := by
  unfold runCodeWithStorageWithInputs? at execution ⊢
  cases selected :
      context.context.values.working.1.code? inputs.codeAddress with
  | none =>
      rw [selected] at execution
      simp at execution
  | some code =>
      rw [selected] at execution
      simp only [Option.map_some] at execution ⊢
      exact congrArg some
        (code.runWithStorage_done_stable context inputs
          (Option.some.inj execution) more)

end FrameCheckpointedWorkingPairWithPresentStorageAccount

end Solcore.Semantics
