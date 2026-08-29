import Solcore.Semantics.HostStorageDriverWithExecutionInputsProperties

/-! Type and fault safety for the explicit-input storage driver seam. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

namespace HostStorageDriver

theorem runWithInputs_hasType
    {RollbackState : Type u} {TraceState : Type v}
    {definitions : Core.DataEnvironment} {resultType : Core.Ty}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (stateTyping : Core.HostStateHasType state resultType definitions) :
    (runWithInputs context inputs fuel state).outcome.HasType
      resultType definitions := by
  exact run_hasType context inputs.codeAddress fuel state stateTyping

theorem runWithInputs_ne_fault
    {RollbackState : Type u} {TraceState : Type v}
    {definitions : Core.DataEnvironment} {resultType : Core.Ty}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state faultState : Core.State)
    (error : Core.MachineFault)
    (stateTyping : Core.HostStateHasType state resultType definitions) :
    (runWithInputs context inputs fuel state).outcome ≠
      .fault error faultState := by
  exact run_ne_fault context inputs.codeAddress fuel state faultState error
    stateTyping

end HostStorageDriver

namespace CheckedHostCoreProgram

theorem runWithStorageInputs_hasType
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    (code.runWithStorageInputs context inputs fuel).outcome.HasType
      code.program.resultType code.program.dataDefinitions := by
  exact code.runWithStorage_hasType context inputs.codeAddress fuel

theorem runWithStorageInputs_ne_fault
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    (code.runWithStorageInputs context inputs fuel).outcome ≠
      .fault error faultState := by
  exact code.runWithStorage_ne_fault context inputs.codeAddress fuel
    error faultState

theorem runWithStorageInputs_done_hasType
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel : Nat} {value : Core.Value} {store : Core.Store}
    (result :
      (code.runWithStorageInputs context inputs fuel).outcome =
        .done value store) :
    ∃ world,
      Core.StoreHasTypes world store ∧
        Core.HostRuntimeValueHasType world value code.program.resultType
          code.program.dataDefinitions := by
  exact code.runWithStorage_done_hasType context inputs.codeAddress result

theorem runWithStorageInputs_outOfFuel_hasType
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel : Nat} {state : Core.State}
    (result :
      (code.runWithStorageInputs context inputs fuel).outcome =
        .outOfFuel state) :
    Core.HostStateHasType state code.program.resultType
      code.program.dataDefinitions := by
  exact code.runWithStorage_outOfFuel_hasType context inputs.codeAddress result

end CheckedHostCoreProgram

end Solcore.Semantics
