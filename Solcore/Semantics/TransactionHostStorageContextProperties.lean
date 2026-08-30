import Solcore.Semantics.TransactionHostStorageContext
import Solcore.Semantics.TransactionJournalProperties

/-! Exact preservation and append laws for transaction storage contexts. -/

set_option autoImplicit false

namespace Solcore.Semantics.TransactionHostStorageDriver

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

end Solcore.Semantics.TransactionHostStorageDriver
