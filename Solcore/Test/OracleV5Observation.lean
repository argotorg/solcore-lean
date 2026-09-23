import Solcore.Oracle.V5.Observation
import Solcore.Test.Adr0147BalancedTopLevelExecutionFixture

/-! Executable regressions for total Oracle v5 terminal projection. -/

set_option autoImplicit false

namespace Tests.OracleV5Observation

open Solcore.Core
open Solcore.Oracle.V5
open Solcore.ContractRuntime
open Tests.Adr0147BalancedTopLevelExecutionFixture
open Tests.TopLevelExecutionFixture

private def rootId : ContractId :=
  ⟨"root", by native_decide⟩

private def resolveAll (_program : Program) : Option ContractId :=
  some rootId

private def emptyJournal : JournalObservation := {
  logs := []
  createdAddresses := []
}

private def returnedProbes : List Probe :=
  [.accountPresence callerAddress, .balance callerAddress,
    .balance targetAddress, .code targetAddress]

private def returnedProjection : ExecutionProjection :=
  ExecutionProjection.ofBalancedResult resolveAll returnedProbes <|
    runWithBalances returningContract ten three one completionFuel

private def returnedProjectionExpected : ExecutionProjection :=
  .executed {
    outcome := .returned (encodeWordBytesBE returnPayload)
    journal := emptyJournal
    state := {
      probes :=
        [.accountPresence callerAddress true true,
          .balance callerAddress (some ten) (some nine),
          .balance targetAddress (some three) (some four),
          .code targetAddress (some rootId) (some rootId)]
    }
  }

private def returnCommitsTransfer : Bool :=
  returnedProjection == returnedProjectionExpected

private def rollbackProbes : List Probe :=
  [.storage targetAddress targetSlot, .balance callerAddress,
    .balance targetAddress]

private def revertedProjection : ExecutionProjection :=
  ExecutionProjection.ofBalancedResult resolveAll rollbackProbes <|
    runWithBalances contract ten three one completionFuel

private def revertedProjectionExpected : ExecutionProjection :=
  .executed {
    outcome := .reverted (encodeWordBytesBE revertPayload)
    journal := emptyJournal
    state := {
      probes :=
        [.storage targetAddress targetSlot (some oldValue) (some oldValue),
          .balance callerAddress (some ten) (some ten),
          .balance targetAddress (some three) (some three)]
    }
  }

private def revertRollsBackTransferAndStorage : Bool :=
  revertedProjection == revertedProjectionExpected

private def rejectionProbes : List Probe :=
  [.accountPresence callerAddress, .balance targetAddress]

private def rejectedProjection : ExecutionProjection :=
  ExecutionProjection.ofBalancedResult resolveAll rejectionProbes <|
    runWithoutCaller returningContract three callerAddress one completionFuel

private def rejectedProjectionExpected : ExecutionProjection :=
  .executed {
    outcome := .preflightRejected .senderAbsent
    journal := emptyJournal
    state := {
      probes :=
        [.accountPresence callerAddress false false,
          .balance targetAddress (some three) (some three)]
    }
  }

private def rejectionIsIdentity : Bool :=
  rejectedProjection == rejectedProjectionExpected

private def exhaustionHasNoObservation : Bool :=
  ExecutionProjection.ofBalancedResult resolveAll returnedProbes
      (runWithBalances returningContract ten three one 0) ==
    .outOfFuel

private def unresolvedCodeIsInternalError : Bool :=
  ExecutionProjection.ofBalancedResult (fun _ => none)
      [.code targetAddress]
      (runWithBalances returningContract ten three one completionFuel) ==
    .internalError .worldCodeReferenceInvariant

private def allChecks : Bool :=
  returnCommitsTransfer && revertRollsBackTransferAndStorage &&
    rejectionIsIdentity && exhaustionHasNoObservation &&
    unresolvedCodeIsInternalError

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5Observation : IO Unit := do
  unless allChecks do
    throw (IO.userError
      "Oracle v5 terminal projection changed commit, rollback, or exhaustion")

end Tests.OracleV5Observation
