import Solcore.Semantics.FrameTraceProperties
import Solcore.Semantics.TransactionJournal

/-! Exact executable observation laws for transaction journals. -/

set_option autoImplicit false

namespace Solcore.Semantics.TransactionJournal

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

set_option doc.verso true in
/-- Sequential recording appends the two logs in chronological order and retains
duplicates. The log observation is a sequence, not a set that may be sorted
or deduplicated without changing the result.
-/
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

end Solcore.Semantics.TransactionJournal
