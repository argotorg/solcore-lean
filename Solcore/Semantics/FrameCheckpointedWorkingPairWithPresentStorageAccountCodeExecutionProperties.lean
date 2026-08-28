import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecution
import Solcore.Semantics.HostStorageReadDriverProperties
import Solcore.Semantics.WorldStateCodeProperties

/-! Selection laws and safety for address-selected handled host execution. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

namespace FrameCheckpointedWorkingPairWithPresentStorageAccount

abbrev CodeRunContext
    (RollbackState : Type u)
    (TraceState : Type v) :=
  HostStorageReadDriver.Context RollbackState TraceState

@[simp] theorem runCodeWithStorageReads?_of_absent
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (absent :
      context.context.values.working.1.account? codeAddress = none) :
    context.runCodeWithStorageReads? codeAddress fuel = none := by
  simp [runCodeWithStorageReads?, WorldState.code?, absent]

@[simp] theorem runCodeWithStorageReads?_of_account_without_code
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (codeAddress : Address)
    (account : Account)
    (fuel : Nat)
    (present :
      context.context.values.working.1.account? codeAddress = some account)
    (withoutCode : account.code? = none) :
    context.runCodeWithStorageReads? codeAddress fuel = none := by
  simp [runCodeWithStorageReads?, WorldState.code?, present, withoutCode]

@[simp] theorem runCodeWithStorageReads?_of_present
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
    context.runCodeWithStorageReads? codeAddress fuel =
      some (code.runWithStorageReads context fuel) := by
  simp [runCodeWithStorageReads?, WorldState.code?, accountPresent, codePresent]

/-- Every returned read-only result retains the complete input context. -/
theorem runCodeWithStorageReads?_result_context
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (result : HostDriverResult (CodeRunContext RollbackState TraceState))
    (executed :
      context.runCodeWithStorageReads? codeAddress fuel = some result) :
    result.context = context := by
  unfold runCodeWithStorageReads? at executed
  cases selected : context.context.values.working.1.code? codeAddress with
  | none => simp [selected] at executed
  | some code =>
      rw [selected] at executed
      have same := Option.some.inj executed
      rw [← same]
      exact code.runWithStorageReads_context context fuel

/-- Address-selected checked host execution cannot return a driver fault. -/
theorem runCodeWithStorageReads?_ne_some_fault
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (resultContext : CodeRunContext RollbackState TraceState)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    context.runCodeWithStorageReads? codeAddress fuel ≠
      some ⟨resultContext, .fault error faultState⟩ := by
  unfold runCodeWithStorageReads?
  cases selected : context.context.values.working.1.code? codeAddress with
  | none => simp
  | some code =>
      simp only [Option.map_some]
      intro same
      have resultEq := Option.some.inj same
      have outcomeEq := congrArg HostDriverResult.outcome resultEq
      exact code.runWithStorageReads_ne_fault context fuel error faultState
        outcomeEq

end FrameCheckpointedWorkingPairWithPresentStorageAccount

end Solcore.Semantics
