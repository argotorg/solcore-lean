import Solcore.Semantics.CheckedCoreContract
import Solcore.Semantics.HostDriverProperties
import Solcore.Semantics.TransactionHostStorageContext
import Solcore.Semantics.TopLevelStorageDelta

/-! Total results for one bounded checked-Core top-level execution. -/

set_option autoImplicit false

namespace Solcore.Semantics

/-- A terminal result after contract-owned decoding and root state selection. -/
structure TopLevelTerminalResult
    (initialWorld : WorldState)
    (target : Address) where
  terminalContext : TransactionHostStorageDriver.Context
  coreValue : Core.Value
  coreStore : Core.Store
  outcome : FrameOutcome Core.Word
  finalWorld : WorldState
  /-- All rollback-scoped observations produced by speculative execution. -/
  workingJournal : TransactionJournal
  /-- Root-selected observations: committed on return, checkpoint on failure. -/
  committedJournal : TransactionJournal
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

end Solcore.Semantics
