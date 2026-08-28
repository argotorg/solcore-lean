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

@[simp] theorem runCode?_of_absent
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (absent :
      context.context.values.working.1.account? codeAddress = none) :
    context.runCode? codeAddress fuel = none := by
  simp [runCode?, WorldState.code?, absent]

@[simp] theorem runCode?_of_account_without_code
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (codeAddress : Address)
    (account : Account)
    (fuel : Nat)
    (present :
      context.context.values.working.1.account? codeAddress = some account)
    (withoutCode : account.code? = none) :
    context.runCode? codeAddress fuel = none := by
  simp [runCode?, WorldState.code?, present, withoutCode]

@[simp] theorem runCode?_of_present
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
    context.runCode? codeAddress fuel =
      some (code.runWithStorage context fuel) := by
  simp [runCode?, WorldState.code?, accountPresent, codePresent]

/-- Every returned read-only result retains the complete input context. -/
theorem runCode?_result_context
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (result : HostDriverResult (CodeRunContext RollbackState TraceState))
    (executed : context.runCode? codeAddress fuel = some result) :
    result.context = context := by
  unfold runCode? at executed
  cases selected : context.context.values.working.1.code? codeAddress with
  | none => simp [selected] at executed
  | some code =>
      rw [selected] at executed
      have same := Option.some.inj executed
      rw [← same]
      exact code.runWithStorage_context context fuel

/-- Address-selected checked host execution cannot return a driver fault. -/
theorem runCode?_ne_some_fault
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (resultContext : CodeRunContext RollbackState TraceState)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    context.runCode? codeAddress fuel ≠
      some ⟨resultContext, .fault error faultState⟩ := by
  unfold runCode?
  cases selected : context.context.values.working.1.code? codeAddress with
  | none => simp
  | some code =>
      simp only [Option.map_some]
      intro same
      have resultEq := Option.some.inj same
      have outcomeEq := congrArg HostDriverResult.outcome resultEq
      exact code.runWithStorage_ne_fault context fuel error faultState outcomeEq

end FrameCheckpointedWorkingPairWithPresentStorageAccount

end Solcore.Semantics
