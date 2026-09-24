import Solcore.ContractRuntime.HostStorageContext
import Solcore.ContractRuntime.HostStorageExecutionInputs
import Solcore.ContractRuntime.TransactionJournal
import Solcore.ContractRuntime.HostStorageHandler
import Solcore.ContractRuntime.CheckedHostCoreProgram
import Solcore.ContractRuntime.HostDriver
import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-! Transaction-scoped host-storage context, handler, driver, and laws. -/

/-!
## Consolidated module: `Solcore.ContractRuntime.TransactionHostStorageContext`
-/

/-! Storage execution context with rollback-scoped transaction observations. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.TransactionHostStorageDriver

/-- The concrete effect policy used by observable checked execution. -/
abbrev Context :=
  HostStorageDriver.Context TransactionJournal Unit

namespace Context

/-- The transaction observations accumulated by the active frame. -/
def workingJournal (context : Context) : TransactionJournal :=
  context.context.values.working.2.rollback

/-- Replace only the active frame's rollback-scoped transaction journal. -/
def withWorkingJournal
    (context : Context)
    (journal : TransactionJournal) : Context :=
  context.rebaseWorkingWithEffects
    context.context.values.working.1
    {
      rollback := journal
      trace := context.context.values.working.2.trace
    }
    context.storageAccount context.storageAccount_present

/-- Append one already-attributed log to the active transaction journal. -/
def recordLog
    (context : Context)
    (entry : CheckedCoreWordLog) : Context :=
  context.withWorkingJournal (context.workingJournal.recordLog entry)

end Context

/-- Attribute a raw word log to the immutable active invocation address. -/
def wordLog
    (inputs : HostStorageDriver.ExecutionInputs)
    (topic payload : Core.Word) : CheckedCoreWordLog := {
  emitter := inputs.currentAddress
  topic := topic
  payload := payload
}

end Solcore.ContractRuntime.TransactionHostStorageDriver

/-!
## Consolidated module: `Solcore.ContractRuntime.TransactionHostStorageContextProperties`
-/

/-! Exact preservation and append laws for transaction storage contexts. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.TransactionHostStorageDriver

namespace Context

@[simp] theorem workingJournal_withWorkingJournal
    (context : Context)
    (journal : TransactionJournal) :
    (context.withWorkingJournal journal).workingJournal = journal :=
  rfl

@[simp] theorem withWorkingJournal_workingWorld
    (context : Context)
    (journal : TransactionJournal) :
    (context.withWorkingJournal journal).context.values.working.1 =
      context.context.values.working.1 :=
  rfl

@[simp] theorem withWorkingJournal_storageAccount
    (context : Context)
    (journal : TransactionJournal) :
    (context.withWorkingJournal journal).storageAccount =
      context.storageAccount :=
  rfl

@[simp] theorem withWorkingJournal_storageAddress
    (context : Context)
    (journal : TransactionJournal) :
    (context.withWorkingJournal journal).context.storageAddress =
      context.context.storageAddress :=
  rfl

@[simp] theorem withWorkingJournal_checkpoint
    (context : Context)
    (journal : TransactionJournal) :
    (context.withWorkingJournal journal).context.values.checkpoint =
      context.context.values.checkpoint :=
  rfl

@[simp] theorem withWorkingJournal_trace
    (context : Context)
    (journal : TransactionJournal) :
    (context.withWorkingJournal journal).context.values.working.2.trace =
      context.context.values.working.2.trace :=
  rfl

@[simp] theorem workingJournal_recordLog
    (context : Context)
    (entry : CheckedCoreWordLog) :
    (context.recordLog entry).workingJournal =
      context.workingJournal.recordLog entry :=
  rfl

@[simp] theorem logList_recordLog
    (context : Context)
    (entry : CheckedCoreWordLog) :
    (context.recordLog entry).workingJournal.logList =
      context.workingJournal.logList ++ [entry] := by
  simp

@[simp] theorem createdContractList_recordLog
    (context : Context)
    (entry : CheckedCoreWordLog) :
    (context.recordLog entry).workingJournal.createdContractList =
      context.workingJournal.createdContractList := by
  simp

@[simp] theorem recordLog_workingWorld
    (context : Context)
    (entry : CheckedCoreWordLog) :
    (context.recordLog entry).context.values.working.1 =
      context.context.values.working.1 :=
  rfl

@[simp] theorem recordLog_storageAccount
    (context : Context)
    (entry : CheckedCoreWordLog) :
    (context.recordLog entry).storageAccount = context.storageAccount :=
  rfl

@[simp] theorem recordLog_storageAddress
    (context : Context)
    (entry : CheckedCoreWordLog) :
    (context.recordLog entry).context.storageAddress =
      context.context.storageAddress :=
  rfl

@[simp] theorem recordLog_checkpoint
    (context : Context)
    (entry : CheckedCoreWordLog) :
    (context.recordLog entry).context.values.checkpoint =
      context.context.values.checkpoint :=
  rfl

end Context

@[simp] theorem wordLog_emitter
    (inputs : HostStorageDriver.ExecutionInputs)
    (topic payload : Core.Word) :
    (wordLog inputs topic payload).emitter = inputs.currentAddress :=
  rfl

@[simp] theorem wordLog_topic
    (inputs : HostStorageDriver.ExecutionInputs)
    (topic payload : Core.Word) :
    (wordLog inputs topic payload).topic = topic :=
  rfl

@[simp] theorem wordLog_payload
    (inputs : HostStorageDriver.ExecutionInputs)
    (topic payload : Core.Word) :
    (wordLog inputs topic payload).payload = payload :=
  rfl

end Solcore.ContractRuntime.TransactionHostStorageDriver

/-!
## Consolidated module: `Solcore.ContractRuntime.TransactionHostStorageHandler`
-/

/-! Observable host handling over rollback-scoped transaction journals. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.TransactionHostStorageDriver

/--
Handle one request with the generic storage policy, except that a word log is
attributed to the active address and appended to the working journal.
-/
def handleRequest
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (request : Core.HostRequest) : Context × request.Response :=
  match request with
  | .emitLogWord topic payload =>
      (context.recordLog (wordLog inputs topic payload), ())
  | request => HostStorageDriver.handleRequest inputs context request

/-- The transaction-aware handler for one immutable execution input. -/
def handler
    (inputs : HostStorageDriver.ExecutionInputs) : HostHandler Context where
  supports := fun _ => true
  handle := handleRequest inputs

/-- Handle and resume one suspension under the transaction-aware policy. -/
def handleSuspension
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (suspension : Core.HostSuspension) : Context × Core.State :=
  (handler inputs).handleSuspension context suspension

end Solcore.ContractRuntime.TransactionHostStorageDriver

/-!
## Consolidated module: `Solcore.ContractRuntime.TransactionHostStorageHandlerProperties`
-/

/-! Exact emission and compatibility laws for the transaction host handler. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.TransactionHostStorageDriver

@[simp] theorem handler_supports
    (inputs : HostStorageDriver.ExecutionInputs)
    (request : Core.HostRequest) :
    (handler inputs).supports request = true :=
  rfl

/-- Every non-log request is delegated to the canonical storage handler. -/
theorem handleRequest_eq_generic_of_not_emitLogWord
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (request : Core.HostRequest)
    (notEmission :
      ∀ topic payload, request ≠ .emitLogWord topic payload) :
    handleRequest inputs context request =
      HostStorageDriver.handleRequest inputs context request := by
  cases request <;> simp_all [handleRequest] <;> rfl

@[simp] theorem handleRequest_emitLogWord
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (topic payload : Core.Word) :
    handleRequest inputs context (.emitLogWord topic payload) =
      (context.recordLog (wordLog inputs topic payload), ()) :=
  rfl

@[simp] theorem handleSuspension_emitLogWord
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (topic payload : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension inputs context
        ⟨.emitLogWord topic payload, continuation, store⟩ =
      (context.recordLog (wordLog inputs topic payload),
        ⟨.ret .unit, continuation, store⟩) :=
  rfl

@[simp] theorem handleRequest_emitLogWord_logList
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (topic payload : Core.Word) :
    (Context.workingJournal
      (handleRequest inputs context (.emitLogWord topic payload)).1).logList =
      context.workingJournal.logList ++ [wordLog inputs topic payload] := by
  simp

@[simp] theorem handleRequest_emitLogWord_createdContractList
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (topic payload : Core.Word) :
    TransactionJournal.createdContractList
      (Context.workingJournal
        (handleRequest inputs context (.emitLogWord topic payload)).1) =
      context.workingJournal.createdContractList := by
  simp

@[simp] theorem handleRequest_emitLogWord_workingWorld
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (topic payload : Core.Word) :
    (handleRequest inputs context
      (.emitLogWord topic payload)).1.context.values.working.1 =
      context.context.values.working.1 := by
  simp

@[simp] theorem handleRequest_emitLogWord_storageAccount
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (topic payload : Core.Word) :
    (handleRequest inputs context
      (.emitLogWord topic payload)).1.storageAccount = context.storageAccount := by
  simp

@[simp] theorem handleRequest_emitLogWord_storageAddress
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (topic payload : Core.Word) :
    (handleRequest inputs context
      (.emitLogWord topic payload)).1.context.storageAddress =
        context.context.storageAddress := by
  simp

@[simp] theorem handleRequest_emitLogWord_checkpoint
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (topic payload : Core.Word) :
    (handleRequest inputs context
      (.emitLogWord topic payload)).1.context.values.checkpoint =
        context.context.values.checkpoint := by
  simp

@[simp] theorem handleSuspension_emitLogWord_control
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (topic payload : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.emitLogWord topic payload, continuation, store⟩).2.control =
        .ret .unit := by
  simp

@[simp] theorem handleSuspension_emitLogWord_continuation
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (topic payload : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.emitLogWord topic payload, continuation, store⟩).2.continuation =
        continuation := by
  simp

@[simp] theorem handleSuspension_emitLogWord_store
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (topic payload : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.emitLogWord topic payload, continuation, store⟩).2.store = store := by
  simp

theorem handleSuspension_state_hasType
    {definitions : Core.DataEnvironment} {resultType : Core.Ty}
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (suspension : Core.HostSuspension)
    (typing : Core.HostSuspensionHasType suspension resultType definitions) :
    Core.HostStateHasType
      (handleSuspension inputs context suspension).2 resultType definitions := by
  simpa only [handleSuspension] using
    HostHandler.handleSuspension_state_hasType
      (handler inputs) context suspension typing

end Solcore.ContractRuntime.TransactionHostStorageDriver

/-!
## Consolidated module: `Solcore.ContractRuntime.TransactionHostStorageDriver`
-/

/-! Canonical driver for observable transaction storage execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

namespace TransactionHostStorageDriver

/-- Run Core while preserving and extending the active transaction journal. -/
def run
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) : HostDriverResult Context :=
  HostDriver.run (handler inputs) context fuel state

end TransactionHostStorageDriver

namespace CheckedHostCoreProgram

/-- Start checked code under the observable transaction storage policy. -/
def runWithTransactionStorage
    (code : CheckedHostCoreProgram)
    (context : TransactionHostStorageDriver.Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    HostDriverResult TransactionHostStorageDriver.Context :=
  TransactionHostStorageDriver.run context inputs fuel
    (Core.State.initial code.program.body Core.hostEnvironment)

end CheckedHostCoreProgram

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.TransactionHostStorageDriverProperties`
-/

/-! Execution, preservation, and safety laws for transaction storage runs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

namespace TransactionHostStorageDriver

@[simp] theorem run_of_done
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (value : Core.Value)
    (store : Core.Store)
    (execution : Core.hostRun fuel state = .done value store) :
    run context inputs fuel state = ⟨context, .done value store⟩ := by
  simpa only [run] using
    HostDriver.run_of_done (handler inputs)
      context fuel state value store execution

@[simp] theorem run_of_outOfFuel
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state exhausted : Core.State)
    (execution : Core.hostRun fuel state = .outOfFuel exhausted) :
    run context inputs fuel state = ⟨context, .outOfFuel exhausted⟩ := by
  simpa only [run] using
    HostDriver.run_of_outOfFuel (handler inputs)
      context fuel state exhausted execution

@[simp] theorem run_of_fault
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state faultState : Core.State)
    (error : Core.MachineFault)
    (execution : Core.hostRun fuel state = .fault error faultState) :
    run context inputs fuel state =
      ⟨context, .fault error faultState⟩ := by
  simpa only [run] using
    HostDriver.run_of_fault (handler inputs)
      context fuel state faultState error execution

theorem run_of_suspended
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (suspension : Core.HostSuspension)
    (execution :
      Core.hostRun fuel state = .suspended suspension remainingFuel) :
    run context inputs fuel state =
      run (handleSuspension inputs context suspension).1 inputs remainingFuel
        (handleSuspension inputs context suspension).2 := by
  simpa only [run, handleSuspension] using
    (HostDriver.run_of_suspended (handler inputs)
      context fuel remainingFuel state suspension execution
      |>.trans (by rw [if_pos (handler_supports inputs suspension.request)]))

theorem run_of_suspended_emitLogWord
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (topic payload : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended
          ⟨.emitLogWord topic payload, continuation, store⟩ remainingFuel) :
    run context inputs fuel state =
      run (context.recordLog (wordLog inputs topic payload)) inputs
        remainingFuel ⟨.ret .unit, continuation, store⟩ := by
  calc
    run context inputs fuel state =
        run
          (handleSuspension inputs context
            ⟨.emitLogWord topic payload, continuation, store⟩).1
          inputs remainingFuel
          (handleSuspension inputs context
            ⟨.emitLogWord topic payload, continuation, store⟩).2 :=
      run_of_suspended context inputs fuel remainingFuel state _ execution
    _ = _ := by rw [handleSuspension_emitLogWord]

@[simp] theorem run_storageAddress
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    (run context inputs fuel state).context.context.storageAddress =
      context.context.storageAddress := by
  simpa only [run] using
    HostDriver.run_observe (handler inputs)
      (fun current => current.context.storageAddress)
      (by
        intro current request
        cases request <;>
          simp [handler, handleRequest, HostStorageDriver.handleRequest])
      context fuel state

@[simp] theorem run_checkpoint
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    (run context inputs fuel state).context.context.values.checkpoint =
      context.context.values.checkpoint := by
  simpa only [run] using
    HostDriver.run_observe (handler inputs)
      (fun current => current.context.values.checkpoint)
      (by
        intro current request
        cases request <;>
          simp [handler, handleRequest, HostStorageDriver.handleRequest])
      context fuel state

@[simp] theorem run_trace
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    (run context inputs fuel state).context.context.values.working.2.trace =
      context.context.values.working.2.trace := by
  exact Subsingleton.elim _ _

@[simp] theorem run_workingCode?
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (observedAddress : Address) :
    (run context inputs fuel state).context.context.values.working.1.code?
        observedAddress =
      context.context.values.working.1.code? observedAddress := by
  simpa only [run] using
    HostDriver.run_observe (handler inputs)
      (fun current =>
        current.context.values.working.1.code? observedAddress)
      (by
        intro current request
        cases request <;>
          simp [handler, handleRequest, HostStorageDriver.handleRequest])
      context fuel state

@[simp] theorem run_workingAccount?_of_ne_storageAddress
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (observedAddress : Address)
    (different : observedAddress ≠ context.context.storageAddress) :
    (run context inputs fuel state).context.context.values.working.1.account?
        observedAddress =
      context.context.values.working.1.account? observedAddress := by
  have preserved :
      (if observedAddress =
          (run context inputs fuel state).context.context.storageAddress
        then none
        else
          (run context inputs fuel state).context.context.values.working.1.account?
            observedAddress) =
      (if observedAddress = context.context.storageAddress
        then none
        else context.context.values.working.1.account? observedAddress) := by
    exact
      HostDriver.run_observe (handler inputs)
        (fun current =>
          if observedAddress = current.context.storageAddress
            then none
            else current.context.values.working.1.account? observedAddress)
        (by
          intro current request
          cases request with
          | storageWrite slot value =>
              by_cases same :
                  observedAddress = current.context.storageAddress
              · simp [handler, handleRequest,
                  HostStorageDriver.handleRequest, same]
              · simp [handler, handleRequest,
                  HostStorageDriver.handleRequest, same]
          | storageRead slot =>
              simp [handler, handleRequest, HostStorageDriver.handleRequest] <;> rfl
          | storageAddress =>
              simp [handler, handleRequest, HostStorageDriver.handleRequest] <;> rfl
          | codeAddress =>
              simp [handler, handleRequest, HostStorageDriver.handleRequest] <;> rfl
          | callValue =>
              simp [handler, handleRequest, HostStorageDriver.handleRequest] <;> rfl
          | callerAddress =>
              simp [handler, handleRequest, HostStorageDriver.handleRequest] <;> rfl
          | inputDataByte? offset =>
              simp [handler, handleRequest, HostStorageDriver.handleRequest] <;> rfl
          | inputDataSize =>
              simp [handler, handleRequest, HostStorageDriver.handleRequest] <;> rfl
          | inputDataWordBE? offset =>
              simp [handler, handleRequest, HostStorageDriver.handleRequest] <;> rfl
          | currentAddress =>
              simp [handler, handleRequest, HostStorageDriver.handleRequest] <;> rfl
          | callContractWord target input =>
              simp [handler, handleRequest, HostStorageDriver.handleRequest] <;> rfl
          | callContractWordWithValue target value input =>
              simp [handler, handleRequest, HostStorageDriver.handleRequest] <;> rfl
          | createContractWord templateId value input =>
              simp [handler, handleRequest, HostStorageDriver.handleRequest] <;> rfl
          | emitLogWord topic payload =>
              simp [handler, handleRequest] <;> rfl)
        context fuel state
  simpa only [run_storageAddress, if_neg different] using preserved

theorem run_hasType
    {definitions : Core.DataEnvironment} {resultType : Core.Ty}
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (stateTyping : Core.HostStateHasType state resultType definitions) :
    (run context inputs fuel state).outcome.HasType
      resultType definitions := by
  simpa only [run] using
    HostDriver.run_hasType (handler inputs)
      context fuel state stateTyping

theorem run_ne_fault
    {definitions : Core.DataEnvironment} {resultType : Core.Ty}
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state faultState : Core.State)
    (error : Core.MachineFault)
    (stateTyping : Core.HostStateHasType state resultType definitions) :
    (run context inputs fuel state).outcome ≠
      .fault error faultState := by
  simpa only [run] using
    HostDriver.run_ne_fault (handler inputs)
      context fuel state faultState error stateTyping

/-- The transaction policy supports every request, including logs. -/
theorem run_ne_unsupported
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (suspension : Core.HostSuspension)
    (remainingFuel : Nat) :
    (run context inputs fuel state).outcome ≠
      .unsupported suspension remainingFuel := by
  simpa only [run] using
    HostDriver.run_ne_unsupported_of_supports_all
      (handler inputs) (handler_supports inputs) context fuel state
      suspension remainingFuel

end TransactionHostStorageDriver

namespace CheckedHostCoreProgram

theorem runWithTransactionStorage_hasType
    (code : CheckedHostCoreProgram)
    (context : TransactionHostStorageDriver.Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    (code.runWithTransactionStorage context inputs fuel).outcome.HasType
      code.program.resultType code.program.dataDefinitions := by
  exact TransactionHostStorageDriver.run_hasType
    context inputs fuel _ code.initialState_hasType

theorem runWithTransactionStorage_ne_fault
    (code : CheckedHostCoreProgram)
    (context : TransactionHostStorageDriver.Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    (code.runWithTransactionStorage context inputs fuel).outcome ≠
      .fault error faultState := by
  exact TransactionHostStorageDriver.run_ne_fault
    context inputs fuel _ faultState error code.initialState_hasType

theorem runWithTransactionStorage_ne_unsupported
    (code : CheckedHostCoreProgram)
    (context : TransactionHostStorageDriver.Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (suspension : Core.HostSuspension)
    (remainingFuel : Nat) :
    (code.runWithTransactionStorage context inputs fuel).outcome ≠
      .unsupported suspension remainingFuel := by
  exact TransactionHostStorageDriver.run_ne_unsupported
    context inputs fuel _ suspension remainingFuel

end CheckedHostCoreProgram

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.TransactionHostStorageDriverFuelProperties`
-/

/-! Exact fuel continuation laws for transaction storage execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

namespace TransactionHostStorageDriver

/-- Exhaustion resumes with the exact retained transaction context. -/
theorem run_additional_of_outOfFuel
    (context nextContext : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel additional : Nat)
    (state exhausted : Core.State)
    (execution :
      run context inputs fuel state =
        ⟨nextContext, .outOfFuel exhausted⟩) :
    run context inputs (fuel + additional) state =
      run nextContext inputs additional exhausted := by
  simpa only [run] using
    HostDriver.run_additional_of_outOfFuel
      (handler inputs) execution

/-- Split execution and a single summed-budget run retain identical journals. -/
theorem resumeWithFuel_run
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel additional : Nat)
    (state : Core.State) :
    (run context inputs fuel state).resumeWithFuel
        (handler inputs) additional =
      run context inputs (fuel + additional) state := by
  simpa only [run] using
    HostDriverResult.resumeWithFuel_run
      (handler inputs) context fuel additional state

/-- A completed transaction run is stable under a larger fuel budget. -/
theorem run_done_stable
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel largerFuel : Nat}
    (state : Core.State)
    {finalContext : Context}
    {value : Core.Value} {store : Core.Store}
    (execution :
      run context inputs fuel state =
        ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    run context inputs largerFuel state =
      ⟨finalContext, .done value store⟩ := by
  simpa only [run] using
    HostDriver.run_done_stable (handler inputs) execution more

end TransactionHostStorageDriver

namespace CheckedHostCoreProgram

theorem runWithTransactionStorage_done_stable
    (code : CheckedHostCoreProgram)
    (context : TransactionHostStorageDriver.Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel largerFuel : Nat}
    {finalContext : TransactionHostStorageDriver.Context}
    {value : Core.Value} {store : Core.Store}
    (execution :
      code.runWithTransactionStorage context inputs fuel =
        ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    code.runWithTransactionStorage context inputs largerFuel =
      ⟨finalContext, .done value store⟩ := by
  simpa only [runWithTransactionStorage] using
    TransactionHostStorageDriver.run_done_stable context inputs
      (Core.State.initial code.program.body Core.hostEnvironment)
      execution more

/-- Checked transaction execution has the exact additive resumption law. -/
theorem runWithTransactionStorage_resumeWithFuel
    (code : CheckedHostCoreProgram)
    (context : TransactionHostStorageDriver.Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel additional : Nat) :
    (code.runWithTransactionStorage context inputs fuel).resumeWithFuel
        (TransactionHostStorageDriver.handler inputs) additional =
      code.runWithTransactionStorage context inputs (fuel + additional) := by
  simpa only [runWithTransactionStorage] using
    TransactionHostStorageDriver.resumeWithFuel_run context inputs
      fuel additional
      (Core.State.initial code.program.body Core.hostEnvironment)

end CheckedHostCoreProgram

end Solcore.ContractRuntime
