import Solcore.ContractRuntime.RuntimeScalars
import Solcore.ContractRuntime.Frames
import Solcore.ContractRuntime.Contracts
import Solcore.ContractRuntime.StorageDriver
import Solcore.ContractRuntime.WorldState
import Solcore.Core.Syntax
import Solcore.Core.HostMachine
import Solcore.ContractRuntime.Driver
import Solcore.Core.Machine
import Solcore.Core.Host

/-!
# Transaction-scoped execution

`TransactionJournal` collects logs and created contracts, scoped to rollback.
`TransactionHostStorageDriver.handleRequest` and `TransactionHostStorageDriver.run` add it to the
storage driver, and `CheckedHostCoreProgram.runWithTransactionStorage` runs checked code with it.
-/

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsTransactionJournal
/-! Rollback-scoped observations accumulated by one checked transaction. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/--
Ordered transaction observations selected together at frame boundaries.

Both traces are chronological and preserve duplicates. The journal itself is
the rollback payload; diagnostic or revert-surviving traces remain separate.
-/
structure TransactionJournal where
  logs : FrameTrace CheckedCoreWordLog
  createdContracts : FrameTrace Address

namespace TransactionJournal

/-- A transaction journal with no recorded observations. -/
def empty : TransactionJournal := {
  logs := FrameTrace.empty
  createdContracts := FrameTrace.empty
}

/-- Record one log after every log already in the journal. -/
def recordLog
    (journal : TransactionJournal)
    (entry : CheckedCoreWordLog) : TransactionJournal :=
  { journal with logs := journal.logs.record entry }

/-- Record one successfully created contract after earlier creations. -/
def recordCreatedContract
    (journal : TransactionJournal)
    (address : Address) : TransactionJournal :=
  { journal with createdContracts := journal.createdContracts.record address }

/-- Observe logs from earliest to latest. -/
def logList (journal : TransactionJournal) : List CheckedCoreWordLog :=
  journal.logs.toList

/-- Observe successful contract creations from earliest to latest. -/
def createdContractList (journal : TransactionJournal) : List Address :=
  journal.createdContracts.toList

end TransactionJournal

end Solcore.ContractRuntime
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsTransactionHostStorage
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
end
