import Solcore.Oracle.V5.ObservationCodec

/-! Exact-wire regressions for canonical Oracle v5 execution observations. -/

set_option autoImplicit false

namespace Tests.OracleV5ObservationCodec

open Solcore.Oracle.V5
open Solcore.Semantics

private def addressOne : Address := ⟨1, by decide⟩
private def addressTwo : Address := ⟨2, by decide⟩
private def zero : Solcore.Core.Word := ⟨0, by decide⟩
private def one : Solcore.Core.Word := ⟨1, by decide⟩
private def two : Solcore.Core.Word := ⟨2, by decide⟩
private def three : Solcore.Core.Word := ⟨3, by decide⟩
private def runtimeId : ContractId := ⟨"runtime", by decide⟩

private def addressOneText : String :=
  "0x0000000000000000000000000000000000000001"

private def addressTwoText : String :=
  "0x0000000000000000000000000000000000000002"

private def wordText (last : String) : String :=
  "0x000000000000000000000000000000000000000000000000000000000000000" ++
    last

private def scalarEncodingsExact : Bool :=
  (encodeAddress addressOne).compress == s!"\"{addressOneText}\"" &&
    (encodeWord three).compress == s!"\"{wordText "3"}\"" &&
    (encodeBytes (ByteArray.mk #[0, 15, 255])).compress == "\"0x000fff\""

private def terminalOutcomesExact : Bool :=
  (encodeTerminalOutcome (.preflightRejected .senderAbsent)).compress ==
      "{\"kind\":\"preflightRejected\",\"reason\":\"senderAbsent\"}" &&
    (encodeTerminalOutcome (.preflightRejected .recipientAbsent)).compress ==
      "{\"kind\":\"preflightRejected\",\"reason\":\"recipientAbsent\"}" &&
    (encodeTerminalOutcome
      (.preflightRejected .insufficientBalance)).compress ==
      "{\"kind\":\"preflightRejected\",\"reason\":\"insufficientBalance\"}" &&
    (encodeTerminalOutcome (.preflightRejected .recipientOverflow)).compress ==
      "{\"kind\":\"preflightRejected\",\"reason\":\"recipientOverflow\"}" &&
    (encodeTerminalOutcome (.returned ByteArray.empty)).compress ==
      "{\"kind\":\"returned\",\"returndata\":\"0x\"}" &&
    (encodeTerminalOutcome
      (.reverted (ByteArray.mk #[10, 188]))).compress ==
      "{\"kind\":\"reverted\",\"revertdata\":\"0x0abc\"}" &&
    (encodeTerminalOutcome (.trapped zero)).compress ==
      "{\"kind\":\"trapped\",\"reason\":\"" ++ wordText "0" ++ "\"}"

private def journal : JournalObservation := {
  logs := [{ emitter := addressOne, topic := two, payload := three }]
  createdAddresses := [addressTwo, addressOne, addressOne]
}

private def journalEncodingExact : Bool :=
  (encodeJournalObservation journal).compress ==
    "{\"createdAddresses\":[\"" ++ addressTwoText ++ "\",\"" ++
    addressOneText ++ "\",\"" ++ addressOneText ++ "\"],\"logs\":[{" ++
    "\"emitter\":\"" ++ addressOneText ++ "\",\"payload\":\"" ++
    wordText "3" ++ "\",\"topic\":\"" ++ wordText "2" ++ "\"}]}"

private def probes : List ProbeObservation := [
  .accountPresence addressOne false true,
  .storage addressOne two none (some zero),
  .balance addressOne (some zero) none,
  .nonce addressOne none (some one),
  .code addressOne none (some runtimeId)
]

private def probeEncodingsExact : Bool :=
  (Lean.Json.arr (probes.toArray.map encodeProbeObservation)).compress ==
    "[{\"address\":\"" ++ addressOneText ++
    "\",\"committed\":true,\"initial\":false,\"kind\":\"accountPresence\"}," ++
    "{\"address\":\"" ++ addressOneText ++ "\",\"committed\":\"" ++
    wordText "0" ++ "\",\"initial\":null,\"kind\":\"storage\",\"slot\":\"" ++
    wordText "2" ++ "\"},{\"address\":\"" ++ addressOneText ++
    "\",\"committed\":null,\"initial\":\"" ++ wordText "0" ++
    "\",\"kind\":\"balance\"},{\"address\":\"" ++ addressOneText ++
    "\",\"committed\":\"" ++ wordText "1" ++
    "\",\"initial\":null,\"kind\":\"nonce\"},{\"address\":\"" ++
    addressOneText ++
    "\",\"committed\":\"runtime\",\"initial\":null,\"kind\":\"code\"}]"

private def observation : ExecutionObservation := {
  outcome := .returned (ByteArray.mk #[0, 15, 255])
  journal
  state := { probes }
}

private def stateSchemaAndOrderExact : Bool :=
  let encoded := encodeStateObservation observation.state
  match encoded.getObjValAs? String "schema",
      encoded.getObjVal? "probes" with
  | .ok schema, .ok (.arr values) =>
      schema == stateObservationSchema && values.size == 5
  | _, _ => false

private def executionSchemaAndFieldsExact : Bool :=
  let encoded := encodeExecutionObservation observation
  match encoded.getObjValAs? String "schema",
      encoded.getObjVal? "value" with
  | .ok schema, .ok value =>
      match value.getObjVal? "outcome", value.getObjVal? "journal",
          value.getObjVal? "state" with
      | .ok outcome, .ok journal, .ok state =>
          schema == executionSchema &&
            outcome == encodeTerminalOutcome observation.outcome &&
            journal == encodeJournalObservation observation.journal &&
            state == encodeStateObservation observation.state
      | _, _, _ => false
  | _, _ => false

private def allChecks : Bool :=
  scalarEncodingsExact && terminalOutcomesExact && journalEncodingExact &&
    probeEncodingsExact && stateSchemaAndOrderExact &&
    executionSchemaAndFieldsExact

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5ObservationCodec : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 observation JSON codec changed")

end Tests.OracleV5ObservationCodec
