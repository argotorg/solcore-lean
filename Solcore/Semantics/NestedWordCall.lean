import Solcore.Core.HostMachine
import Solcore.Semantics.CheckedCoreWordOutcome
import Solcore.Semantics.ContractWordCallInput
import Solcore.Semantics.TopLevelExecutionContext

/-! Exact invocation and response derivation for one internal Word call. -/

set_option autoImplicit false

namespace Solcore.Semantics

namespace CheckedCoreWordOutcome

/-- Preserve the exact terminal branch and Word when resuming the caller. -/
def toContractCallResult :
    CheckedCoreWordOutcome → Core.ContractCallWordResult
  | .returned data => .returned data
  | .reverted data => .reverted data
  | .trapped reason => .trapped reason

end CheckedCoreWordOutcome

namespace TopLevelInvocation

/-- Derive the fixed depth-one child-call profile from its parent inputs. -/
def childWord
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address)
    (input : Core.Word) : TopLevelInvocation := {
  target := target
  caller := parentInputs.currentAddress
  callValue := Core.Word.zero
  inputData := HostStorageDriver.InputData.ofWord input
}

/-- Derive a value-bearing child invocation in target/value/input order. -/
def childWordWithValue
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address)
    (value input : Core.Word) : TopLevelInvocation := {
  target := target
  caller := parentInputs.currentAddress
  callValue := value
  inputData := HostStorageDriver.InputData.ofWord input
}

@[simp] theorem childWord_target
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) (input : Core.Word) :
    (childWord parentInputs target input).target = target :=
  rfl

@[simp] theorem childWord_caller
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) (input : Core.Word) :
    (childWord parentInputs target input).caller =
      parentInputs.currentAddress :=
  rfl

@[simp] theorem childWord_callValue
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) (input : Core.Word) :
    (childWord parentInputs target input).callValue = Core.Word.zero :=
  rfl

@[simp] theorem childWord_inputBytes
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) (input : Core.Word) :
    (childWord parentInputs target input).inputData.bytes =
      encodeWordBytesBE input :=
  rfl

@[simp] theorem childWord_executionInputs
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) (input : Core.Word) :
    (childWord parentInputs target input).executionInputs = {
      codeAddress := target
      callValue := Core.Word.zero
      callerAddress := parentInputs.currentAddress
      inputData := HostStorageDriver.InputData.ofWord input
      currentAddress := target
    } :=
  rfl

@[simp] theorem childWordWithValue_target
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) (value input : Core.Word) :
    (childWordWithValue parentInputs target value input).target = target :=
  rfl

@[simp] theorem childWordWithValue_caller
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) (value input : Core.Word) :
    (childWordWithValue parentInputs target value input).caller =
      parentInputs.currentAddress :=
  rfl

@[simp] theorem childWordWithValue_callValue
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) (value input : Core.Word) :
    (childWordWithValue parentInputs target value input).callValue = value :=
  rfl

@[simp] theorem childWordWithValue_inputBytes
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) (value input : Core.Word) :
    (childWordWithValue parentInputs target value input).inputData.bytes =
      encodeWordBytesBE input :=
  rfl

@[simp] theorem childWordWithValue_executionInputs
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) (value input : Core.Word) :
    (childWordWithValue parentInputs target value input).executionInputs = {
      codeAddress := target
      callValue := value
      callerAddress := parentInputs.currentAddress
      inputData := HostStorageDriver.InputData.ofWord input
      currentAddress := target
    } :=
  rfl

end TopLevelInvocation

end Solcore.Semantics
