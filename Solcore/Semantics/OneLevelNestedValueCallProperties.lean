import Solcore.Semantics.OneLevelNestedExecutionReachabilityProperties

/-! Public projection laws for the nested value-call scheduler profile. -/

set_option autoImplicit false

namespace Solcore.Semantics.OneLevelNestedExecution.CallProfile

@[simp] theorem request_legacy (target input : Core.Word) :
    (legacy target input).request = .callContractWord target input :=
  rfl

@[simp] theorem request_withValue (target value input : Core.Word) :
    (withValue target value input).request =
      .callContractWordWithValue target value input :=
  rfl

@[simp] theorem target_legacy (target input : Core.Word) :
    (legacy target input).target = target :=
  rfl

@[simp] theorem target_withValue (target value input : Core.Word) :
    (withValue target value input).target = target :=
  rfl

@[simp] theorem invocation_legacy
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) (targetWord input : Core.Word) :
    (legacy targetWord input).invocation parentInputs target =
      TopLevelInvocation.childWord parentInputs target input :=
  rfl

@[simp] theorem invocation_withValue
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) (targetWord value input : Core.Word) :
    (withValue targetWord value input).invocation parentInputs target =
      TopLevelInvocation.childWordWithValue parentInputs target value input :=
  rfl

end Solcore.Semantics.OneLevelNestedExecution.CallProfile
