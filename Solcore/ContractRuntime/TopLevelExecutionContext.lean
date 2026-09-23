import Solcore.ContractRuntime.CheckedCoreContract
import Solcore.ContractRuntime.FrameCheckpointSnapshot
import Solcore.ContractRuntime.HostStorageContext
import Solcore.ContractRuntime.TransactionHostStorageContext

/-! Root storage context derived from explicit top-level execution inputs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

namespace TopLevelExecution

/-- Root execution currently has no separate rollback payload or event trace. -/
def initialEffects : FrameEffectJournal Unit Unit :=
  ⟨(), ()⟩

/-- Empty rollback-scoped observations for a direct transaction root. -/
def initialTransactionEffects :
    FrameEffectJournal TransactionJournal Unit :=
  ⟨TransactionJournal.empty, ()⟩

/-- Use the same explicit world and empty effects as checkpoint and working data. -/
def initialValues
    (initialWorld : WorldState) :
    FrameCheckpointedWorkingPair Unit Unit :=
  let working := (initialWorld, initialEffects)
  ⟨FrameCheckpointSnapshot.fromWorkingPair working, working⟩

/--
Pair an original transaction checkpoint with a separately prepared working
world. This is the root context shape used after a successful call-value
transfer: execution sees the transferred world, while rollback retains the
exact caller-supplied world.
-/
def preparedValues
    (checkpointWorld workingWorld : WorldState) :
    FrameCheckpointedWorkingPair Unit Unit :=
  let checkpoint :=
    FrameCheckpointSnapshot.fromWorkingPair
      (checkpointWorld, initialEffects)
  ⟨checkpoint, (workingWorld, initialEffects)⟩

/--
Pair explicit checkpoint and working worlds with their exact transaction
journals. This general constructor lets nested frames inherit observations
without weakening the empty-journal direct-root boundary.
-/
def preparedTransactionValuesWithJournals
    (checkpointWorld : WorldState)
    (checkpointJournal : TransactionJournal)
    (workingWorld : WorldState)
    (workingJournal : TransactionJournal) :
    FrameCheckpointedWorkingPair TransactionJournal Unit :=
  let checkpointEffects : FrameEffectJournal TransactionJournal Unit :=
    ⟨checkpointJournal, ()⟩
  let workingEffects : FrameEffectJournal TransactionJournal Unit :=
    ⟨workingJournal, ()⟩
  ⟨⟨checkpointWorld, checkpointEffects⟩, (workingWorld, workingEffects)⟩

/-- Direct transaction roots start with one empty checkpoint/working journal. -/
def initialTransactionValues
    (initialWorld : WorldState) :
    FrameCheckpointedWorkingPair TransactionJournal Unit :=
  preparedTransactionValuesWithJournals initialWorld TransactionJournal.empty
    initialWorld TransactionJournal.empty

/--
Prepare a direct transaction root after preflight while retaining the original
world and empty transaction observations as its rollback checkpoint.
-/
def preparedTransactionValues
    (checkpointWorld workingWorld : WorldState) :
    FrameCheckpointedWorkingPair TransactionJournal Unit :=
  preparedTransactionValuesWithJournals checkpointWorld
    TransactionJournal.empty workingWorld TransactionJournal.empty

/-- Build the exact root storage context certified by contract installation. -/
def initialContext
    {initialWorld : WorldState}
    {target : Address}
    {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract initialWorld target contract) :
    HostStorageDriver.Context Unit Unit := {
  context := {
    storageAddress := target
    values := initialValues initialWorld
  }
  storageAccount := installed.account
  storageAccount_present := installed.account_present
}

/-- Build a root context with distinct checkpoint and working worlds. -/
def preparedContext
    {checkpointWorld workingWorld : WorldState}
    {target : Address}
    {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    HostStorageDriver.Context Unit Unit := {
  context := {
    storageAddress := target
    values := preparedValues checkpointWorld workingWorld
  }
  storageAccount := installed.account
  storageAccount_present := installed.account_present
}

/-- Build the observable direct-root context certified by installation. -/
def initialTransactionContext
    {initialWorld : WorldState}
    {target : Address}
    {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract initialWorld target contract) :
    TransactionHostStorageDriver.Context := {
  context := {
    storageAddress := target
    values := initialTransactionValues initialWorld
  }
  storageAccount := installed.account
  storageAccount_present := installed.account_present
}

/-- Build an observable prepared root with empty transaction observations. -/
def preparedTransactionContext
    {checkpointWorld workingWorld : WorldState}
    {target : Address}
    {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    TransactionHostStorageDriver.Context := {
  context := {
    storageAddress := target
    values := preparedTransactionValues checkpointWorld workingWorld
  }
  storageAccount := installed.account
  storageAccount_present := installed.account_present
}

/--
Build an observable prepared context carrying caller-selected checkpoint and
working journals. Nested schedulers use this boundary to preserve log order.
-/
def preparedTransactionContextWithJournals
    {checkpointWorld workingWorld : WorldState}
    {target : Address}
    {contract : CheckedCoreContract}
    (checkpointJournal workingJournal : TransactionJournal)
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    TransactionHostStorageDriver.Context := {
  context := {
    storageAddress := target
    values := preparedTransactionValuesWithJournals checkpointWorld
      checkpointJournal workingWorld workingJournal
  }
  storageAccount := installed.account
  storageAccount_present := installed.account_present
}

end TopLevelExecution

end Solcore.ContractRuntime
