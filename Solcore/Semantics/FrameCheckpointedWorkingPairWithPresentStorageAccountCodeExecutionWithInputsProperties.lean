import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecutionWithInputs
import Solcore.Semantics.HostStorageDriverWithExecutionInputsFuelProperties
import Solcore.Semantics.HostStorageDriverWithExecutionInputsSafetyProperties
import Solcore.Semantics.WorldStateCodeProperties

/-! Selection, fuel, and safety laws for explicit-input selected execution. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

namespace FrameCheckpointedWorkingPairWithPresentStorageAccount

abbrev InputCodeRunContext
    (RollbackState : Type u) (TraceState : Type v) :=
  HostStorageDriver.Context RollbackState TraceState

@[simp] theorem runCodeWithStorageWithInputs?_of_absent
    {RollbackState : Type u} {TraceState : Type v}
    (context : InputCodeRunContext RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (absent :
      context.context.values.working.1.account? inputs.codeAddress = none) :
    context.runCodeWithStorageWithInputs? inputs fuel = none := by
  simp [runCodeWithStorageWithInputs?, WorldState.code?, absent]

@[simp] theorem runCodeWithStorageWithInputs?_of_account_without_code
    {RollbackState : Type u} {TraceState : Type v}
    (context : InputCodeRunContext RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (account : Account)
    (fuel : Nat)
    (present :
      context.context.values.working.1.account? inputs.codeAddress =
        some account)
    (withoutCode : account.code? = none) :
    context.runCodeWithStorageWithInputs? inputs fuel = none := by
  simp [runCodeWithStorageWithInputs?, WorldState.code?, present, withoutCode]

@[simp] theorem runCodeWithStorageWithInputs?_of_present
    {RollbackState : Type u} {TraceState : Type v}
    (context : InputCodeRunContext RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (account : Account)
    (code : CheckedHostCoreProgram)
    (fuel : Nat)
    (accountPresent :
      context.context.values.working.1.account? inputs.codeAddress =
        some account)
    (codePresent : account.code? = some code) :
    context.runCodeWithStorageWithInputs? inputs fuel =
      some (code.runWithStorage context inputs fuel) := by
  simp [runCodeWithStorageWithInputs?, WorldState.code?,
    accountPresent, codePresent]

@[simp] theorem runCodeWithStorageWithInputs?_eq_none_iff
    {RollbackState : Type u} {TraceState : Type v}
    (context : InputCodeRunContext RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    context.runCodeWithStorageWithInputs? inputs fuel = none ↔
      context.context.values.working.1.code? inputs.codeAddress = none := by
  unfold runCodeWithStorageWithInputs?
  cases selected :
      context.context.values.working.1.code? inputs.codeAddress with
  | none => simp only [Option.map_none]
  | some code => simp only [Option.map_some, reduceCtorEq]

theorem runCodeWithStorageWithInputs?_some_fuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (context : InputCodeRunContext RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result : HostDriverResult (InputCodeRunContext RollbackState TraceState))
    (executed :
      context.runCodeWithStorageWithInputs? inputs fuel = some result) :
    ∃ code,
      context.context.values.working.1.code? inputs.codeAddress = some code ∧
        HostStorageDriver.FuelSound result inputs fuel context
          (Core.State.initial code.program.body Core.hostEnvironment) := by
  unfold runCodeWithStorageWithInputs? at executed
  cases selected :
      context.context.values.working.1.code? inputs.codeAddress with
  | none => simp [selected] at executed
  | some code =>
      rw [selected] at executed
      have resultEq := Option.some.inj executed
      subst result
      exact ⟨code, rfl,
        code.runWithStorage_fuelSound context inputs fuel⟩

theorem runCodeWithStorageWithInputs?_eq_some_iff_fuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (context : InputCodeRunContext RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result : HostDriverResult (InputCodeRunContext RollbackState TraceState)) :
    context.runCodeWithStorageWithInputs? inputs fuel = some result ↔
      ∃ code,
        context.context.values.working.1.code? inputs.codeAddress = some code ∧
          HostStorageDriver.FuelSound result inputs fuel context
            (Core.State.initial code.program.body Core.hostEnvironment) := by
  constructor
  · exact runCodeWithStorageWithInputs?_some_fuelSound
      context inputs fuel result
  · rintro ⟨code, selected, sound⟩
    unfold runCodeWithStorageWithInputs?
    rw [selected]
    exact congrArg some
      ((code.runWithStorage_eq_iff_fuelSound
        context inputs fuel result).2 sound)

theorem runCodeWithStorageWithInputs?_some_hasType
    {RollbackState : Type u} {TraceState : Type v}
    (context : InputCodeRunContext RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result : HostDriverResult (InputCodeRunContext RollbackState TraceState))
    (executed :
      context.runCodeWithStorageWithInputs? inputs fuel = some result) :
    ∃ code,
      context.context.values.working.1.code? inputs.codeAddress = some code ∧
        result.outcome.HasType
          code.program.resultType code.program.dataDefinitions := by
  unfold runCodeWithStorageWithInputs? at executed
  cases selected :
      context.context.values.working.1.code? inputs.codeAddress with
  | none => simp [selected] at executed
  | some code =>
      rw [selected] at executed
      have resultEq := Option.some.inj executed
      subst result
      exact ⟨code, rfl,
        code.runWithStorage_hasType context inputs fuel⟩

theorem runCodeWithStorageWithInputs?_ne_some_fault
    {RollbackState : Type u} {TraceState : Type v}
    (context : InputCodeRunContext RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (resultContext : InputCodeRunContext RollbackState TraceState)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    context.runCodeWithStorageWithInputs? inputs fuel ≠
      some ⟨resultContext, .fault error faultState⟩ := by
  unfold runCodeWithStorageWithInputs?
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

end Solcore.Semantics
