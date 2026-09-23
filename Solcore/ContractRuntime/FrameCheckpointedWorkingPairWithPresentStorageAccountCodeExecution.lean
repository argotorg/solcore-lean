import Solcore.ContractRuntime.HostStorageDriver
import Solcore.ContractRuntime.WorldStateCode

/-! Address-selected handled execution with one immutable execution input. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

namespace FrameCheckpointedWorkingPairWithPresentStorageAccount

/-- Select and run code using the same immutable code selector and call input. -/
def runCodeWithStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    Option
      (HostDriverResult
        (HostStorageDriver.Context RollbackState TraceState)) :=
  (context.context.values.working.1.code? inputs.codeAddress).map fun code =>
    code.runWithStorage context inputs fuel

end FrameCheckpointedWorkingPairWithPresentStorageAccount

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecutionProperties`
-/

/-! Selection, fuel, and safety laws for explicit-input selected execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

namespace FrameCheckpointedWorkingPairWithPresentStorageAccount

abbrev CodeRunContext
    (RollbackState : Type u) (TraceState : Type v) :=
  HostStorageDriver.Context RollbackState TraceState

@[simp] theorem runCodeWithStorage?_of_absent
    {RollbackState : Type u} {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (absent :
      context.context.values.working.1.account? inputs.codeAddress = none) :
    context.runCodeWithStorage? inputs fuel = none := by
  simp [runCodeWithStorage?, WorldState.code?, absent]

@[simp] theorem runCodeWithStorage?_of_account_without_code
    {RollbackState : Type u} {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (account : Account)
    (fuel : Nat)
    (present :
      context.context.values.working.1.account? inputs.codeAddress =
        some account)
    (withoutCode : account.code? = none) :
    context.runCodeWithStorage? inputs fuel = none := by
  simp [runCodeWithStorage?, WorldState.code?, present, withoutCode]

@[simp] theorem runCodeWithStorage?_of_present
    {RollbackState : Type u} {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (account : Account)
    (code : CheckedHostCoreProgram)
    (fuel : Nat)
    (accountPresent :
      context.context.values.working.1.account? inputs.codeAddress =
        some account)
    (codePresent : account.code? = some code) :
    context.runCodeWithStorage? inputs fuel =
      some (code.runWithStorage context inputs fuel) := by
  simp [runCodeWithStorage?, WorldState.code?,
    accountPresent, codePresent]

@[simp] theorem runCodeWithStorage?_eq_none_iff
    {RollbackState : Type u} {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    context.runCodeWithStorage? inputs fuel = none ↔
      context.context.values.working.1.code? inputs.codeAddress = none := by
  unfold runCodeWithStorage?
  cases selected :
      context.context.values.working.1.code? inputs.codeAddress with
  | none => simp only [Option.map_none]
  | some code => simp only [Option.map_some, reduceCtorEq]

theorem runCodeWithStorage?_some_fuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result : HostDriverResult (CodeRunContext RollbackState TraceState))
    (executed :
      context.runCodeWithStorage? inputs fuel = some result) :
    ∃ code,
      context.context.values.working.1.code? inputs.codeAddress = some code ∧
        HostStorageDriver.FuelSound result inputs fuel context
          (Core.State.initial code.program.body Core.hostEnvironment) := by
  unfold runCodeWithStorage? at executed
  cases selected :
      context.context.values.working.1.code? inputs.codeAddress with
  | none => simp [selected] at executed
  | some code =>
      rw [selected] at executed
      have resultEq := Option.some.inj executed
      subst result
      exact ⟨code, rfl,
        code.runWithStorage_fuelSound context inputs fuel⟩

theorem runCodeWithStorage?_eq_some_iff_fuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result : HostDriverResult (CodeRunContext RollbackState TraceState)) :
    context.runCodeWithStorage? inputs fuel = some result ↔
      ∃ code,
        context.context.values.working.1.code? inputs.codeAddress = some code ∧
          HostStorageDriver.FuelSound result inputs fuel context
            (Core.State.initial code.program.body Core.hostEnvironment) := by
  constructor
  · exact runCodeWithStorage?_some_fuelSound
      context inputs fuel result
  · rintro ⟨code, selected, sound⟩
    unfold runCodeWithStorage?
    rw [selected]
    exact congrArg some
      ((code.runWithStorage_eq_iff_fuelSound
        context inputs fuel result).2 sound)

theorem runCodeWithStorage?_some_hasType
    {RollbackState : Type u} {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result : HostDriverResult (CodeRunContext RollbackState TraceState))
    (executed :
      context.runCodeWithStorage? inputs fuel = some result) :
    ∃ code,
      context.context.values.working.1.code? inputs.codeAddress = some code ∧
        result.outcome.HasType
          code.program.resultType code.program.dataDefinitions := by
  unfold runCodeWithStorage? at executed
  cases selected :
      context.context.values.working.1.code? inputs.codeAddress with
  | none => simp [selected] at executed
  | some code =>
      rw [selected] at executed
      have resultEq := Option.some.inj executed
      subst result
      exact ⟨code, rfl,
        code.runWithStorage_hasType context inputs fuel⟩

theorem runCodeWithStorage?_ne_some_fault
    {RollbackState : Type u} {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (resultContext : CodeRunContext RollbackState TraceState)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    context.runCodeWithStorage? inputs fuel ≠
      some ⟨resultContext, .fault error faultState⟩ := by
  unfold runCodeWithStorage?
  cases selected :
      context.context.values.working.1.code? inputs.codeAddress with
  | none => simp
  | some code =>
      simp only [Option.map_some]
      intro same
      have resultEq := Option.some.inj same
      have outcomeEq := congrArg HostDriverResult.outcome resultEq
      exact code.runWithStorage_ne_fault context inputs fuel
        error faultState outcomeEq

end FrameCheckpointedWorkingPairWithPresentStorageAccount

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecutionPreservationProperties`
-/

/-! Preservation and stability laws for explicit-input selected execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

namespace FrameCheckpointedWorkingPairWithPresentStorageAccount

theorem runCodeWithStorage?_some_workingCode?
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result : HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (executed :
      context.runCodeWithStorage? inputs fuel = some result)
    (observedAddress : Address) :
    result.context.context.values.working.1.code? observedAddress =
      context.context.values.working.1.code? observedAddress := by
  unfold runCodeWithStorage? at executed
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

theorem runCodeWithStorage?_some_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result : HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (executed :
      context.runCodeWithStorage? inputs fuel = some result) :
    result.context.context.storageAddress = context.context.storageAddress := by
  unfold runCodeWithStorage? at executed
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

theorem runCodeWithStorage?_some_checkpoint
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result : HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (executed :
      context.runCodeWithStorage? inputs fuel = some result) :
    result.context.context.values.checkpoint =
      context.context.values.checkpoint := by
  unfold runCodeWithStorage? at executed
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

theorem runCodeWithStorage?_some_workingEffects
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result : HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (executed :
      context.runCodeWithStorage? inputs fuel = some result) :
    result.context.context.values.working.2 =
      context.context.values.working.2 := by
  unfold runCodeWithStorage? at executed
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

theorem runCodeWithStorage?_some_workingAccount?_of_ne_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result : HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (executed :
      context.runCodeWithStorage? inputs fuel = some result)
    (observedAddress : Address)
    (different : observedAddress ≠ context.context.storageAddress) :
    result.context.context.values.working.1.account? observedAddress =
      context.context.values.working.1.account? observedAddress := by
  unfold runCodeWithStorage? at executed
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

theorem runCodeWithStorage?_some_done_stable
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel largerFuel : Nat}
    {resultContext : HostStorageDriver.Context RollbackState TraceState}
    {value : Core.Value} {store : Core.Store}
    (execution :
      context.runCodeWithStorage? inputs fuel =
        some ⟨resultContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    context.runCodeWithStorage? inputs largerFuel =
      some ⟨resultContext, .done value store⟩ := by
  unfold runCodeWithStorage? at execution ⊢
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

end Solcore.ContractRuntime
