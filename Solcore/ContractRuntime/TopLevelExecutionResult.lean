import Solcore.ContractRuntime.CheckedCoreContract
import Solcore.ContractRuntime.HostDriverProperties
import Solcore.ContractRuntime.TransactionHostStorageContext
import Solcore.ContractRuntime.TopLevelStorageDelta

/-! Total results for one bounded checked-Core top-level execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- A terminal result after contract-owned decoding and root state selection. -/
structure TopLevelTerminalResult
    (initialWorld : WorldState)
    (target : Address) where
  terminalContext : TransactionHostStorageDriver.Context
  checkpointJournal_eq :
    terminalContext.context.values.checkpoint.effects.rollback =
      TransactionJournal.empty
  coreValue : Core.Value
  coreStore : Core.Store
  outcome : FrameOutcome Core.Word
  finalWorld : WorldState
  /-- All rollback-scoped observations produced by speculative execution. -/
  workingJournal : TransactionJournal
  workingJournal_eq : workingJournal = terminalContext.workingJournal
  /-- Root-selected observations: committed on return, checkpoint on failure. -/
  committedJournal : TransactionJournal
  committedJournal_eq :
    committedJournal =
      match outcome with
      | .returned _ => terminalContext.workingJournal
      | .reverted _ =>
          terminalContext.context.values.checkpoint.effects.rollback
      | .trapped _ =>
          terminalContext.context.values.checkpoint.effects.rollback
  workingDelta :
    TopLevelStorageDelta initialWorld
      terminalContext.context.values.working.1 target
  committedDelta :
    TopLevelStorageDelta initialWorld finalWorld target

/--
One bounded run either completes or retains the exact typed machine state needed
to continue. Checked execution has no raw-fault constructor here.
-/
inductive TopLevelRunResult
    (initialWorld : WorldState)
    (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation) where
  | completed
      (result :
        TopLevelTerminalResult initialWorld invocation.target)
  | outOfFuel
      (context : TransactionHostStorageDriver.Context)
      (state : Core.State)
      (storageAddress_eq :
        context.context.storageAddress = invocation.target)
      (stateTyping :
        Core.HostStateHasType state contract.code.program.resultType
          contract.code.program.dataDefinitions)
      (workingDelta :
        TopLevelStorageDelta initialWorld
          context.context.values.working.1 invocation.target)
      (checkpointJournal_eq :
        context.context.values.checkpoint.effects.rollback =
          TransactionJournal.empty)

namespace TopLevelRunResult

/-- The root rollback journal retained by either terminal or resumable output. -/
def rootCheckpointJournal
    {initialWorld : WorldState}
    {contract : CheckedCoreContract}
    {invocation : TopLevelInvocation} :
    TopLevelRunResult initialWorld contract invocation → TransactionJournal
  | .completed result =>
      result.terminalContext.context.values.checkpoint.effects.rollback
  | .outOfFuel context _ _ _ _ _ =>
      context.context.values.checkpoint.effects.rollback

/-- Every public top-level result retains the empty root rollback checkpoint. -/
@[simp] theorem rootCheckpointJournal_eq_empty
    {initialWorld : WorldState}
    {contract : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (execution : TopLevelRunResult initialWorld contract invocation) :
    execution.rootCheckpointJournal = TransactionJournal.empty := by
  cases execution with
  | completed result =>
      exact result.checkpointJournal_eq
  | outOfFuel context state address typing delta checkpointJournal_eq =>
      exact checkpointJournal_eq

end TopLevelRunResult

end Solcore.ContractRuntime
