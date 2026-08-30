import Solcore.Semantics.CheckedHostCoreProgramProperties
import Solcore.Semantics.HostStorageDriverProperties
import Solcore.Semantics.ParentIndexedFrameInitializationSelectedExecutionResumptionProperties

/-! Compile-only consumers for run-fixed current-address proof contracts. -/

set_option autoImplicit false

namespace Solcore.Test.CurrentAddressObservationProperties

open Semantics
universe u v w x

variable (codeAddress callerAddress currentAddress : Address)
variable (callValue : Core.Word) (inputData : HostStorageDriver.InputData)

example :
    (HostStorageDriver.ExecutionInputs.mk codeAddress callValue callerAddress
      inputData currentAddress).codeAddress = codeAddress :=
  HostStorageDriver.ExecutionInputs.mk_codeAddress
    codeAddress callValue callerAddress inputData currentAddress

example :
    (HostStorageDriver.ExecutionInputs.mk codeAddress callValue callerAddress
      inputData currentAddress).callValue = callValue :=
  HostStorageDriver.ExecutionInputs.mk_callValue
    codeAddress callValue callerAddress inputData currentAddress

example :
    (HostStorageDriver.ExecutionInputs.mk codeAddress callValue callerAddress
      inputData currentAddress).callerAddress = callerAddress :=
  HostStorageDriver.ExecutionInputs.mk_callerAddress
    codeAddress callValue callerAddress inputData currentAddress

example :
    (HostStorageDriver.ExecutionInputs.mk codeAddress callValue callerAddress
      inputData currentAddress).inputData = inputData :=
  HostStorageDriver.ExecutionInputs.mk_inputData
    codeAddress callValue callerAddress inputData currentAddress

example :
    (HostStorageDriver.ExecutionInputs.mk codeAddress callValue callerAddress
      inputData currentAddress).currentAddress = currentAddress :=
  HostStorageDriver.ExecutionInputs.mk_currentAddress
    codeAddress callValue callerAddress inputData currentAddress

example : Core.HostFunction.parameterType .currentAddress = .unit :=
  Core.HostFunction.parameterType_currentAddress

example : Core.HostFunction.resultType .currentAddress = .word :=
  Core.HostFunction.resultType_currentAddress

example : Core.HostFunction.currentAddress ∈ Core.HostFunction.all :=
  Core.HostFunction.mem_all .currentAddress

example : Core.HostFunction.currentAddress.index = 9 :=
  Core.HostFunction.index_currentAddress

example : Core.HostFunction.all.length = 14 :=
  Core.HostFunction.all_length

example : Core.HostFunction.all[9]? = some .currentAddress := by
  simpa using Core.HostFunction.getElem?_all_index .currentAddress

example : Core.hostContext[9]? =
    some (Core.HostFunction.functionType .currentAddress) := by
  simpa using Core.hostContext_currentAddress

example : Core.hostEnvironment[9]? =
    some (.hostFunction .currentAddress) := by
  simpa using Core.hostEnvironment_currentAddress

example : Core.hostContext.length = 14 :=
  Core.hostContext_length

example : Core.hostEnvironment.length = 14 :=
  Core.hostEnvironment_length

example : Core.hostContext[14]? = none :=
  Core.hostContext_firstUnbound

example : Core.hostEnvironment[14]? = none :=
  Core.hostEnvironment_firstUnbound

variable (response : Core.Word)
variable (continuation : List Core.Frame) (store : Core.Store)

example : Core.HostRequest.responseType .currentAddress = .word :=
  Core.HostRequest.responseType_currentAddress

example : Core.HostRequest.responseValue .currentAddress response =
    .word response :=
  Core.HostRequest.responseValue_currentAddress response

example :
    (Core.HostRequest.responseValue .currentAddress response).type =
      Core.HostRequest.responseType .currentAddress :=
  Core.HostRequest.responseValue_type .currentAddress response

example :
    (Core.HostSuspension.mk .currentAddress continuation store).resume response =
      ⟨.ret (.word response), continuation, store⟩ :=
  Core.HostSuspension.resume_currentAddress response continuation store

variable (argument : Core.Expr) (environment : Core.Environment)

example :
    Core.hostAdvance
        ⟨.ret (.hostFunction .currentAddress),
          .applyArgument argument environment :: continuation, store⟩ =
      .next ⟨.eval argument environment,
        .hostApply .currentAddress :: continuation, store⟩ :=
  Core.hostAdvance_begin_currentAddress
    argument environment continuation store

example : Core.HostTransition
    ⟨.ret (.hostFunction .currentAddress),
      .applyArgument argument environment :: continuation, store⟩
    ⟨.eval argument environment,
      .hostApply .currentAddress :: continuation, store⟩ := by
  apply Core.hostAdvance_next_iff.mp
  exact Core.hostAdvance_begin_currentAddress
    argument environment continuation store

example :
    Core.hostAdvance
        ⟨.ret .unit, .hostApply .currentAddress :: continuation, store⟩ =
      .suspended ⟨.currentAddress, continuation, store⟩ :=
  Core.hostAdvance_suspend_currentAddress continuation store

example : Core.HostRequestEmission
    ⟨.ret .unit, .hostApply .currentAddress :: continuation, store⟩
    ⟨.currentAddress, continuation, store⟩ := by
  apply Core.hostAdvance_suspended_iff.mp
  exact Core.hostAdvance_suspend_currentAddress continuation store

variable (actual : Core.Value) (notUnit : actual ≠ .unit)

example : Core.hostAdvance
      ⟨.ret actual, .hostApply .currentAddress :: continuation, store⟩ =
    .fault (.invalidHostArgument .currentAddress actual) :=
  Core.hostAdvance_invalid_currentAddress_argument
    actual notUnit continuation store

variable {definitions : Core.DataEnvironment} {world : Core.StoreTyping}
variable {value : Core.Value} {resultType : Core.Ty}
variable (valueTyping : Core.HostRuntimeValueHasType world value
  Core.HostFunction.currentAddress.parameterType definitions)

example : ∃ suspension,
    Core.HostRequestEmission
      ⟨.ret value, .hostApply .currentAddress :: continuation, store⟩
      suspension :=
  Core.typed_currentAddress_emits valueTyping

example : Core.HostRuntimeValueHasType world
    (Core.HostRequest.responseValue .currentAddress response)
    (Core.HostRequest.responseType .currentAddress) definitions :=
  Core.HostRequest.responseValue_hasType
    .currentAddress response world definitions

variable (requestStateTyping : Core.HostStateHasType
  ⟨.ret .unit, .hostApply .currentAddress :: continuation, store⟩
  resultType definitions)

example : Core.HostSuspensionHasType
    ⟨.currentAddress, continuation, store⟩ resultType definitions :=
  Core.hostRequestEmission_hasType requestStateTyping .currentAddress

example :
    (∃ returnedValue returnedStore,
      (⟨.ret .unit, .hostApply .currentAddress :: continuation, store⟩ :
        Core.State) = Core.State.final returnedValue returnedStore) ∨
    (∃ next, Core.HostTransition
      ⟨.ret .unit, .hostApply .currentAddress :: continuation, store⟩ next) ∨
    ∃ suspension, Core.HostRequestEmission
      ⟨.ret .unit, .hostApply .currentAddress :: continuation, store⟩
      suspension :=
  Core.host_state_progress requestStateTyping

example (error : Core.MachineFault) :
    Core.hostAdvance
      ⟨.ret .unit, .hostApply .currentAddress :: continuation, store⟩ ≠
        .fault error :=
  Core.well_typed_host_state_never_faults requestStateTyping

variable (code : CheckedHostCoreProgram) (fuel : Nat)
variable (error : Core.MachineFault) (faultState : Core.State)

example : code.runStateful fuel ≠ .fault error faultState :=
  CheckedHostCoreProgram.runStateful_ne_fault code fuel error faultState

variable {RollbackState : Type u} {TraceState : Type v}
variable (inputs leftInputs rightInputs : HostStorageDriver.ExecutionInputs)
variable (context : HostStorageDriver.Context RollbackState TraceState)

example : HostStorageDriver.handleRequest inputs context .currentAddress =
    (context, addressToWord inputs.currentAddress) :=
  HostStorageDriver.handleRequest_currentAddress inputs context

example : HostStorageDriver.handleSuspension inputs context
      ⟨.currentAddress, continuation, store⟩ =
    (context, ⟨.ret (.word (addressToWord inputs.currentAddress)),
      continuation, store⟩) :=
  HostStorageDriver.handleSuspension_currentAddress
    inputs context continuation store

example : (HostStorageDriver.handleSuspension inputs context
    ⟨.currentAddress, continuation, store⟩).1 = context :=
  HostStorageDriver.handleSuspension_currentAddress_context
    inputs context continuation store

example : (HostStorageDriver.handleSuspension leftInputs context
      ⟨.currentAddress, continuation, store⟩).1 =
    (HostStorageDriver.handleSuspension rightInputs context
      ⟨.currentAddress, continuation, store⟩).1 :=
  HostStorageDriver.handleSuspension_currentAddress_context_independent
    leftInputs rightInputs context continuation store

example : (HostStorageDriver.handleSuspension inputs context
      ⟨.currentAddress, continuation, store⟩).2.control =
    .ret (.word (addressToWord inputs.currentAddress)) :=
  HostStorageDriver.handleSuspension_currentAddress_control
    inputs context continuation store

example :
    (HostStorageDriver.handleSuspension leftInputs context
        ⟨.currentAddress, continuation, store⟩).2.control =
      (HostStorageDriver.handleSuspension rightInputs context
        ⟨.currentAddress, continuation, store⟩).2.control ↔
    leftInputs.currentAddress = rightInputs.currentAddress :=
  HostStorageDriver.handleSuspension_currentAddress_control_eq_iff
    leftInputs rightInputs context continuation store

example : (HostStorageDriver.handleSuspension inputs context
      ⟨.currentAddress, continuation, store⟩).2.continuation = continuation :=
  HostStorageDriver.handleSuspension_currentAddress_continuation
    inputs context continuation store

example : (HostStorageDriver.handleSuspension inputs context
      ⟨.currentAddress, continuation, store⟩).2.store = store :=
  HostStorageDriver.handleSuspension_currentAddress_store
    inputs context continuation store

example : wordToAddress?
      ((HostStorageDriver.handler inputs).handle context .currentAddress).2 =
    some inputs.currentAddress :=
  HostStorageDriver.wordToAddress?_handler_currentAddress inputs context

variable (remainingFuel : Nat) (state : Core.State)
variable (execution : Core.hostRun fuel state =
  .suspended ⟨.currentAddress, continuation, store⟩ remainingFuel)

example : HostStorageDriver.run context inputs fuel state =
    HostStorageDriver.run context inputs remainingFuel
      ⟨.ret (.word (addressToWord inputs.currentAddress)),
        continuation, store⟩ :=
  HostStorageDriver.run_of_suspended_currentAddress
    context inputs fuel remainingFuel state continuation store execution

variable {Event : Type w} {TrapReason : Type x}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
variable (initialization : ParentIndexedFrameInitialization
  RollbackState Event parentWorking)
variable (storageAddress : Address) (additional : Nat)
variable (doneOutcome : HostStorageDriver.Context
  RollbackState (FrameTrace Event) →
    Core.Value → Core.Store → FrameOutcome TrapReason)

example :
    (initialization.runCodeWithStorageParentIndexedResult
      storageAddress inputs fuel doneOutcome).resumeWithFuel
        initialization inputs doneOutcome additional =
      initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs (fuel + additional) doneOutcome :=
  ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_resumeWithFuel
    initialization storageAddress inputs fuel additional doneOutcome

end Solcore.Test.CurrentAddressObservationProperties
