import Solcore.ContractRuntime.CheckedCoreWordLog
import Solcore.ContractRuntime.FrameTrace

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

/-!
## Consolidated module: `Solcore.ContractRuntime.TransactionJournalProperties`
-/

/-! Exact executable observation laws for transaction journals. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.TransactionJournal

@[simp] theorem logList_empty : empty.logList = [] := by
  rfl

@[simp] theorem createdContractList_empty : empty.createdContractList = [] := by
  rfl

@[simp] theorem logList_recordLog
    (journal : TransactionJournal)
    (entry : CheckedCoreWordLog) :
    (journal.recordLog entry).logList = journal.logList ++ [entry] := by
  rfl

@[simp] theorem createdContractList_recordLog
    (journal : TransactionJournal)
    (entry : CheckedCoreWordLog) :
    (journal.recordLog entry).createdContractList =
      journal.createdContractList := by
  rfl

@[simp] theorem createdContractList_recordCreatedContract
    (journal : TransactionJournal)
    (address : Address) :
    (journal.recordCreatedContract address).createdContractList =
      journal.createdContractList ++ [address] := by
  rfl

@[simp] theorem logList_recordCreatedContract
    (journal : TransactionJournal)
    (address : Address) :
    (journal.recordCreatedContract address).logList = journal.logList := by
  rfl

/-- Sequential log recording retains duplicates in chronological order. -/
theorem logList_record_two
    (journal : TransactionJournal)
    (first second : CheckedCoreWordLog) :
    ((journal.recordLog first).recordLog second).logList =
      journal.logList ++ [first, second] := by
  simp

/-- Successful creations are observed in completion order. -/
theorem createdContractList_record_two
    (journal : TransactionJournal)
    (first second : Address) :
    createdContractList
        ((journal.recordCreatedContract first).recordCreatedContract second) =
      journal.createdContractList ++ [first, second] := by
  simp

end Solcore.ContractRuntime.TransactionJournal
