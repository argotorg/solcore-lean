import Solcore.ContractRuntime.HostStorageContextRebase
import Solcore.ContractRuntime.HostStorageExecutionInputs
import Solcore.ContractRuntime.TransactionJournal

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
