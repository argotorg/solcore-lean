import Solcore.Oracle.V5.Observation

/-! Focused regressions for sealed Oracle v5 rollback observations. -/

set_option autoImplicit false

namespace Tests.OracleV5ObservationValidity

open Solcore.Oracle.V5
open Solcore.ContractRuntime

private def address : Address := ⟨1, by decide⟩
private def zero : Solcore.Core.Word := ⟨0, by decide⟩
private def one : Solcore.Core.Word := ⟨1, by decide⟩
private def contractId : ContractId := ⟨"runtime", by decide⟩

private def probeChecksExact : Bool :=
  (ProbeObservation.accountPresence address true true).endpointsEqual &&
    !(ProbeObservation.accountPresence address true false).endpointsEqual &&
    (ProbeObservation.storage address zero none none).endpointsEqual &&
    !(ProbeObservation.storage address zero none (some zero)).endpointsEqual &&
    (ProbeObservation.balance address (some zero) (some zero)).endpointsEqual &&
    !(ProbeObservation.balance address (some zero) (some one)).endpointsEqual &&
    (ProbeObservation.nonce address none none).endpointsEqual &&
    !(ProbeObservation.nonce address none (some zero)).endpointsEqual &&
    (ProbeObservation.code address (some contractId)
      (some contractId)).endpointsEqual &&
    !(ProbeObservation.code address none (some contractId)).endpointsEqual

private def emptyJournal : JournalObservation := {
  logs := []
  createdAddresses := []
}

private def nonemptyJournal : JournalObservation := {
  logs := []
  createdAddresses := [address]
}

private def rollbackState : StateObservation := {
  probes := [
    .accountPresence address true true,
    .storage address zero none none,
    .code address (some contractId) (some contractId)
  ]
}

private def changedState : StateObservation := {
  probes := [
    .accountPresence address true true,
    .balance address (some zero) (some one)
  ]
}

private def observation
    (outcome : TerminalOutcome)
    (journal : JournalObservation := emptyJournal)
    (state : StateObservation := rollbackState) : ExecutionObservation := {
  outcome
  journal
  state
}

private def returnedAlwaysValid : Bool :=
  (observation (.returned ByteArray.empty)
    nonemptyJournal changedState).isValid

private def rollbackOutcomesExact : Bool :=
  (observation (.preflightRejected .senderAbsent)).isValid &&
    (observation (.reverted ByteArray.empty)).isValid &&
    (observation (.trapped zero)).isValid &&
    !(observation (.preflightRejected .senderAbsent)
      nonemptyJournal rollbackState).isValid &&
    !(observation (.reverted ByteArray.empty)
      emptyJournal changedState).isValid &&
    !(observation (.trapped zero) nonemptyJournal changedState).isValid

private def sealingExact : Bool :=
  let valid := observation (.reverted ByteArray.empty)
  let invalid := observation (.reverted ByteArray.empty)
    nonemptyJournal changedState
  match ValidExecutionObservation.of? valid,
      ValidExecutionObservation.of? invalid with
  | some sealed, none => sealed.value == valid && sealed.value.isValid
  | _, _ => false

private theorem acceptedWrapperCarriesContract
    (sealed : ValidExecutionObservation) : sealed.value.Valid :=
  sealed.valid

private def allChecks : Bool :=
  probeChecksExact && emptyJournal.isEmpty && !nonemptyJournal.isEmpty &&
    rollbackState.isRollbackExact && !changedState.isRollbackExact &&
    returnedAlwaysValid && rollbackOutcomesExact && sealingExact

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5ObservationValidity : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 observation validity changed")

end Tests.OracleV5ObservationValidity
