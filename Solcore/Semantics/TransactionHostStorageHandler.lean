import Solcore.Semantics.HostStorageHandler
import Solcore.Semantics.TransactionHostStorageContext

/-! Observable host handling over rollback-scoped transaction journals. -/

set_option autoImplicit false

namespace Solcore.Semantics.TransactionHostStorageDriver

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
  handle := handleRequest inputs

/-- Handle and resume one suspension under the transaction-aware policy. -/
def handleSuspension
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (suspension : Core.HostSuspension) : Context × Core.State :=
  (handler inputs).handleSuspension context suspension

end Solcore.Semantics.TransactionHostStorageDriver
