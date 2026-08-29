import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecution
import Solcore.Semantics.HostStorageDriverFuelProperties
import Solcore.Semantics.WorldStateCodeProperties

/-! Selection laws and safety for address-selected handled host execution. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

namespace FrameCheckpointedWorkingPairWithPresentStorageAccount

abbrev CodeRunContext
    (RollbackState : Type u)
    (TraceState : Type v) :=
  HostStorageDriver.Context RollbackState TraceState

@[simp] theorem runCodeWithStorage?_of_absent
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (absent :
      context.context.values.working.1.account? codeAddress = none) :
    context.runCodeWithStorage? codeAddress fuel = none := by
  simp [runCodeWithStorage?, WorldState.code?, absent]

@[simp] theorem runCodeWithStorage?_of_account_without_code
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (codeAddress : Address)
    (account : Account)
    (fuel : Nat)
    (present :
      context.context.values.working.1.account? codeAddress = some account)
    (withoutCode : account.code? = none) :
    context.runCodeWithStorage? codeAddress fuel = none := by
  simp [runCodeWithStorage?, WorldState.code?, present, withoutCode]

@[simp] theorem runCodeWithStorage?_of_present
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (codeAddress : Address)
    (account : Account)
    (code : CheckedHostCoreProgram)
    (fuel : Nat)
    (accountPresent :
      context.context.values.working.1.account? codeAddress = some account)
    (codePresent : account.code? = some code) :
    context.runCodeWithStorage? codeAddress fuel =
      some (code.runWithStorage context codeAddress fuel) := by
  simp [runCodeWithStorage?, WorldState.code?, accountPresent, codePresent]

/-- Optional selection fails exactly when the working WorldState has no code. -/
@[simp] theorem runCodeWithStorage?_eq_none_iff
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat) :
    context.runCodeWithStorage? codeAddress fuel = none ↔
      context.context.values.working.1.code? codeAddress = none := by
  unfold runCodeWithStorage?
  cases selected :
      context.context.values.working.1.code? codeAddress with
  | none => simp only [Option.map_none]
  | some code => simp only [Option.map_some, reduceCtorEq]

/-- A selected run identifies its checked code and inherits exact fuel accounting. -/
theorem runCodeWithStorage?_some_fuelSound
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (result : HostDriverResult (CodeRunContext RollbackState TraceState))
    (executed :
      context.runCodeWithStorage? codeAddress fuel = some result) :
    ∃ code,
      context.context.values.working.1.code? codeAddress = some code ∧
        HostStorageDriver.FuelSound result codeAddress fuel context
          (Core.State.initial code.program.body Core.hostEnvironment) := by
  unfold runCodeWithStorage? at executed
  cases selected :
      context.context.values.working.1.code? codeAddress with
  | none => simp [selected] at executed
  | some code =>
      rw [selected] at executed
      have resultEq := Option.some.inj executed
      subst result
      exact ⟨code, rfl,
        code.runWithStorage_fuelSound context codeAddress fuel⟩

/-- Successful selection is exactly selected-code handled fuel evidence. -/
theorem runCodeWithStorage?_eq_some_iff_fuelSound
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (result : HostDriverResult (CodeRunContext RollbackState TraceState)) :
    context.runCodeWithStorage? codeAddress fuel = some result ↔
      ∃ code,
        context.context.values.working.1.code? codeAddress = some code ∧
          HostStorageDriver.FuelSound result codeAddress fuel context
            (Core.State.initial code.program.body Core.hostEnvironment) := by
  constructor
  · exact runCodeWithStorage?_some_fuelSound context codeAddress fuel result
  · rintro ⟨code, selected, sound⟩
    unfold runCodeWithStorage?
    rw [selected]
    exact congrArg some
      ((code.runWithStorage_eq_iff_fuelSound
        context codeAddress fuel result).2 sound)

/-- A selected run identifies the checked result type it preserves. -/
theorem runCodeWithStorage?_some_hasType
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (result : HostDriverResult (CodeRunContext RollbackState TraceState))
    (executed :
      context.runCodeWithStorage? codeAddress fuel = some result) :
    ∃ code,
      context.context.values.working.1.code? codeAddress = some code ∧
        result.outcome.HasType
          code.program.resultType code.program.dataDefinitions := by
  unfold runCodeWithStorage? at executed
  cases selected :
      context.context.values.working.1.code? codeAddress with
  | none => simp [selected] at executed
  | some code =>
      rw [selected] at executed
      have resultEq := Option.some.inj executed
      subst result
      exact ⟨code, rfl,
        code.runWithStorage_hasType context codeAddress fuel⟩

end FrameCheckpointedWorkingPairWithPresentStorageAccount

end Solcore.Semantics
