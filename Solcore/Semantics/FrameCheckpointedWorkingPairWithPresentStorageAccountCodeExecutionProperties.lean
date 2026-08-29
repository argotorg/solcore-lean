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
      some (code.runWithStorage context fuel) := by
  simp [runCodeWithStorage?, WorldState.code?, accountPresent, codePresent]

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
        HostStorageDriver.FuelSound result fuel context
          (Core.State.initial code.program.body Core.hostEnvironment) := by
  unfold runCodeWithStorage? at executed
  cases selected :
      context.context.values.working.1.code? codeAddress with
  | none => simp [selected] at executed
  | some code =>
      rw [selected] at executed
      have resultEq := Option.some.inj executed
      subst result
      exact ⟨code, rfl, code.runWithStorage_fuelSound context fuel⟩

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
      exact ⟨code, rfl, code.runWithStorage_hasType context fuel⟩

/-- A selected combined run preserves checked code at every working Address. -/
theorem runCodeWithStorage?_some_workingCode?
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (result : HostDriverResult (CodeRunContext RollbackState TraceState))
    (executed :
      context.runCodeWithStorage? codeAddress fuel = some result)
    (observedAddress : Address) :
    result.context.context.values.working.1.code? observedAddress =
      context.context.values.working.1.code? observedAddress := by
  unfold runCodeWithStorage? at executed
  cases selected :
      context.context.values.working.1.code? codeAddress with
  | none => simp [selected] at executed
  | some code =>
      rw [selected] at executed
      have resultEq := Option.some.inj executed
      subst result
      simpa only [CheckedHostCoreProgram.runWithStorage] using
        HostStorageDriver.run_workingCode?
          context fuel
          (Core.State.initial code.program.body Core.hostEnvironment)
          observedAddress

/-- A selected combined run retains the chosen storage Address. -/
theorem runCodeWithStorage?_some_storageAddress
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (result : HostDriverResult (CodeRunContext RollbackState TraceState))
    (executed :
      context.runCodeWithStorage? codeAddress fuel = some result) :
    result.context.context.storageAddress = context.context.storageAddress := by
  unfold runCodeWithStorage? at executed
  cases selected :
      context.context.values.working.1.code? codeAddress with
  | none => simp [selected] at executed
  | some code =>
      rw [selected] at executed
      have resultEq := Option.some.inj executed
      subst result
      simpa only [CheckedHostCoreProgram.runWithStorage] using
        HostStorageDriver.run_storageAddress context fuel
          (Core.State.initial code.program.body Core.hostEnvironment)

/-- A selected combined run retains the complete checkpoint. -/
theorem runCodeWithStorage?_some_checkpoint
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (result : HostDriverResult (CodeRunContext RollbackState TraceState))
    (executed :
      context.runCodeWithStorage? codeAddress fuel = some result) :
    result.context.context.values.checkpoint =
      context.context.values.checkpoint := by
  unfold runCodeWithStorage? at executed
  cases selected :
      context.context.values.working.1.code? codeAddress with
  | none => simp [selected] at executed
  | some code =>
      rw [selected] at executed
      have resultEq := Option.some.inj executed
      subst result
      simpa only [CheckedHostCoreProgram.runWithStorage] using
        HostStorageDriver.run_checkpoint context fuel
          (Core.State.initial code.program.body Core.hostEnvironment)

/-- A selected combined run retains the complete working effect journal. -/
theorem runCodeWithStorage?_some_workingEffects
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (result : HostDriverResult (CodeRunContext RollbackState TraceState))
    (executed :
      context.runCodeWithStorage? codeAddress fuel = some result) :
    result.context.context.values.working.2 =
      context.context.values.working.2 := by
  unfold runCodeWithStorage? at executed
  cases selected :
      context.context.values.working.1.code? codeAddress with
  | none => simp [selected] at executed
  | some code =>
      rw [selected] at executed
      have resultEq := Option.some.inj executed
      subst result
      simpa only [CheckedHostCoreProgram.runWithStorage] using
        HostStorageDriver.run_workingEffects context fuel
          (Core.State.initial code.program.body Core.hostEnvironment)

/-- A selected combined run preserves every non-storage working Account. -/
theorem runCodeWithStorage?_some_workingAccount?_of_ne_storageAddress
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (result : HostDriverResult (CodeRunContext RollbackState TraceState))
    (executed :
      context.runCodeWithStorage? codeAddress fuel = some result)
    (observedAddress : Address)
    (different : observedAddress ≠ context.context.storageAddress) :
    result.context.context.values.working.1.account? observedAddress =
      context.context.values.working.1.account? observedAddress := by
  unfold runCodeWithStorage? at executed
  cases selected :
      context.context.values.working.1.code? codeAddress with
  | none => simp [selected] at executed
  | some code =>
      rw [selected] at executed
      have resultEq := Option.some.inj executed
      subst result
      simpa only [CheckedHostCoreProgram.runWithStorage] using
        HostStorageDriver.run_workingAccount?_of_ne_storageAddress
          context fuel
          (Core.State.initial code.program.body Core.hostEnvironment)
          observedAddress different

/-- A selected completed run is unchanged when supplied more fuel. -/
theorem runCodeWithStorage?_some_done_stable
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (codeAddress : Address)
    {fuel largerFuel : Nat}
    {resultContext : CodeRunContext RollbackState TraceState}
    {value : Core.Value}
    {store : Core.Store}
    (execution :
      context.runCodeWithStorage? codeAddress fuel =
        some ⟨resultContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    context.runCodeWithStorage? codeAddress largerFuel =
      some ⟨resultContext, .done value store⟩ := by
  unfold runCodeWithStorage? at execution ⊢
  cases selected :
      context.context.values.working.1.code? codeAddress with
  | none =>
      rw [selected] at execution
      simp at execution
  | some code =>
      rw [selected] at execution
      simp only [Option.map_some] at execution ⊢
      exact congrArg some
        (code.runWithStorage_done_stable context
          (Option.some.inj execution) more)

/-- Address-selected checked host execution cannot return a driver fault. -/
theorem runCodeWithStorage?_ne_some_fault
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : CodeRunContext RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (resultContext : CodeRunContext RollbackState TraceState)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    context.runCodeWithStorage? codeAddress fuel ≠
      some ⟨resultContext, .fault error faultState⟩ := by
  unfold runCodeWithStorage?
  cases selected : context.context.values.working.1.code? codeAddress with
  | none => simp
  | some code =>
      simp only [Option.map_some]
      intro same
      have resultEq := Option.some.inj same
      have outcomeEq := congrArg HostDriverResult.outcome resultEq
      exact code.runWithStorage_ne_fault context fuel error faultState
        outcomeEq

end FrameCheckpointedWorkingPairWithPresentStorageAccount

end Solcore.Semantics
