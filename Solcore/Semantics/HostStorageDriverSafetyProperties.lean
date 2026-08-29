import Solcore.Semantics.CheckedHostCoreProgramProperties
import Solcore.Semantics.HostStorageDriverProperties

/-! Type and fault safety for the explicit-input storage driver seam. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

namespace HostStorageDriver

theorem run_hasType
    {RollbackState : Type u} {TraceState : Type v}
    {definitions : Core.DataEnvironment} {resultType : Core.Ty}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (stateTyping : Core.HostStateHasType state resultType definitions) :
    (run context inputs fuel state).outcome.HasType
      resultType definitions := by
  simpa only [run] using
    HostDriver.run_hasType
      (@handler RollbackState TraceState inputs)
      context fuel state stateTyping

theorem run_ne_fault
    {RollbackState : Type u} {TraceState : Type v}
    {definitions : Core.DataEnvironment} {resultType : Core.Ty}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state faultState : Core.State)
    (error : Core.MachineFault)
    (stateTyping : Core.HostStateHasType state resultType definitions) :
    (run context inputs fuel state).outcome ≠
      .fault error faultState := by
  simpa only [run] using
    HostDriver.run_ne_fault
      (@handler RollbackState TraceState inputs)
      context fuel state faultState error stateTyping

end HostStorageDriver

namespace CheckedHostCoreProgram

theorem runWithStorage_hasType
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    (code.runWithStorage context inputs fuel).outcome.HasType
      code.program.resultType code.program.dataDefinitions := by
  exact HostStorageDriver.run_hasType
    context inputs fuel _ code.initialState_hasType

theorem runWithStorage_ne_fault
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    (code.runWithStorage context inputs fuel).outcome ≠
      .fault error faultState := by
  exact HostStorageDriver.run_ne_fault
    context inputs fuel _ faultState error code.initialState_hasType

theorem runWithStorage_done_hasType
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel : Nat} {value : Core.Value} {store : Core.Store}
    (result :
      (code.runWithStorage context inputs fuel).outcome =
        .done value store) :
    ∃ world,
      Core.StoreHasTypes world store ∧
        Core.HostRuntimeValueHasType world value code.program.resultType
          code.program.dataDefinitions := by
  have typing := code.runWithStorage_hasType context inputs fuel
  rw [result] at typing
  exact typing

theorem runWithStorage_outOfFuel_hasType
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel : Nat} {state : Core.State}
    (result :
      (code.runWithStorage context inputs fuel).outcome =
        .outOfFuel state) :
    Core.HostStateHasType state code.program.resultType
      code.program.dataDefinitions := by
  have typing := code.runWithStorage_hasType context inputs fuel
  rw [result] at typing
  exact typing

end CheckedHostCoreProgram

end Solcore.Semantics
