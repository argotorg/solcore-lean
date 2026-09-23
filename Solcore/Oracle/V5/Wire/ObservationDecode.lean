import Solcore.Oracle.V5.ObservationCodec
import Solcore.Oracle.V5.ObservationValidity
import Solcore.Oracle.V5.Wire.Scalar

/-! Strict JSON decoding for total Oracle v5 execution observations. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.Wire

open Solcore.ContractRuntime

private def decodeNullableAt {α : Type}
    (decode : Path → Lean.Json → DecodeResult α)
    (path : Path)
    (json : Lean.Json) : DecodeResult (Option α) :=
  match json with
  | .null => pure none
  | _ => some <$> decode path json

def decodeContractIdAt
    (path : Path)
    (json : Lean.Json) : DecodeResult ContractId := do
  let value ← decodeStringAt path json
  match ContractId.ofString? value with
  | some id => pure id
  | none => invalidTagAt path value "[A-Za-z_][A-Za-z0-9_.-]*"

def decodeBalanceTransferFailureAt
    (path : Path)
    (json : Lean.Json) : DecodeResult BalanceTransferFailure := do
  let value ← decodeStringAt path json
  match value with
  | "senderAbsent" => pure .senderAbsent
  | "recipientAbsent" => pure .recipientAbsent
  | "insufficientBalance" => pure .insufficientBalance
  | "recipientOverflow" => pure .recipientOverflow
  | _ => invalidTagAt path value <| .arr #[
      "senderAbsent", "recipientAbsent", "insufficientBalance",
      "recipientOverflow"
    ]

def decodeTerminalOutcomeAt
    (path : Path)
    (json : Lean.Json) : DecodeResult TerminalOutcome := do
  ensureExactObject path json
    ["kind", "reason", "returndata", "revertdata"] ["kind"]
  let kindPath := path.field "kind"
  let kind ← decodeStringAt kindPath (← requireField path json "kind")
  match kind with
  | "preflightRejected" => do
      ensureExactObject path json ["kind", "reason"] ["kind", "reason"]
      let reason ← decodeBalanceTransferFailureAt (path.field "reason")
        (← requireField path json "reason")
      pure (.preflightRejected reason)
  | "returned" => do
      ensureExactObject path json
        ["kind", "returndata"] ["kind", "returndata"]
      let returndata ← decodeBytesAt (path.field "returndata")
        (← requireField path json "returndata")
      pure (.returned returndata)
  | "reverted" => do
      ensureExactObject path json
        ["kind", "revertdata"] ["kind", "revertdata"]
      let revertdata ← decodeBytesAt (path.field "revertdata")
        (← requireField path json "revertdata")
      pure (.reverted revertdata)
  | "trapped" => do
      ensureExactObject path json ["kind", "reason"] ["kind", "reason"]
      let reason ← decodeWordAt (path.field "reason")
        (← requireField path json "reason")
      pure (.trapped reason)
  | _ => invalidTagAt kindPath kind <| .arr #[
      "preflightRejected", "returned", "reverted", "trapped"
    ]

def decodeLogObservationAt
    (path : Path)
    (json : Lean.Json) : DecodeResult LogObservation := do
  ensureExactObject path json
    ["emitter", "payload", "topic"] ["emitter", "payload", "topic"]
  let emitter ← decodeAddressAt (path.field "emitter")
    (← requireField path json "emitter")
  let payload ← decodeWordAt (path.field "payload")
    (← requireField path json "payload")
  let topic ← decodeWordAt (path.field "topic")
    (← requireField path json "topic")
  pure { emitter, topic, payload }

def decodeJournalObservationAt
    (path : Path)
    (json : Lean.Json) : DecodeResult JournalObservation := do
  ensureExactObject path json
    ["createdAddresses", "logs"] ["createdAddresses", "logs"]
  let createdAddresses ← decodeArrayAt decodeAddressAt
    (path.field "createdAddresses")
    (← requireField path json "createdAddresses")
  let logs ← decodeArrayAt decodeLogObservationAt (path.field "logs")
    (← requireField path json "logs")
  pure { logs, createdAddresses }

def decodeProbeObservationAt
    (path : Path)
    (json : Lean.Json) : DecodeResult ProbeObservation := do
  ensureExactObject path json
    ["address", "committed", "initial", "kind", "slot"]
    ["address", "committed", "initial", "kind"]
  let kindPath := path.field "kind"
  let kind ← decodeStringAt kindPath (← requireField path json "kind")
  match kind with
  | "accountPresence" => do
      ensureExactObject path json
        ["address", "committed", "initial", "kind"]
        ["address", "committed", "initial", "kind"]
      let address ← decodeAddressAt (path.field "address")
        (← requireField path json "address")
      let committed ← decodeBoolAt (path.field "committed")
        (← requireField path json "committed")
      let initial ← decodeBoolAt (path.field "initial")
        (← requireField path json "initial")
      pure (.accountPresence address initial committed)
  | "storage" => do
      ensureExactObject path json
        ["address", "committed", "initial", "kind", "slot"]
        ["address", "committed", "initial", "kind", "slot"]
      let address ← decodeAddressAt (path.field "address")
        (← requireField path json "address")
      let committed ← decodeNullableAt decodeWordAt (path.field "committed")
        (← requireField path json "committed")
      let initial ← decodeNullableAt decodeWordAt (path.field "initial")
        (← requireField path json "initial")
      let slot ← decodeWordAt (path.field "slot")
        (← requireField path json "slot")
      pure (.storage address slot initial committed)
  | "balance" | "nonce" => do
      ensureExactObject path json
        ["address", "committed", "initial", "kind"]
        ["address", "committed", "initial", "kind"]
      let address ← decodeAddressAt (path.field "address")
        (← requireField path json "address")
      let committed ← decodeNullableAt decodeWordAt (path.field "committed")
        (← requireField path json "committed")
      let initial ← decodeNullableAt decodeWordAt (path.field "initial")
        (← requireField path json "initial")
      if kind == "balance" then
        pure (.balance address initial committed)
      else
        pure (.nonce address initial committed)
  | "code" => do
      ensureExactObject path json
        ["address", "committed", "initial", "kind"]
        ["address", "committed", "initial", "kind"]
      let address ← decodeAddressAt (path.field "address")
        (← requireField path json "address")
      let committed ← decodeNullableAt decodeContractIdAt
        (path.field "committed") (← requireField path json "committed")
      let initial ← decodeNullableAt decodeContractIdAt
        (path.field "initial") (← requireField path json "initial")
      pure (.code address initial committed)
  | _ => invalidTagAt kindPath kind <| .arr #[
      "accountPresence", "storage", "balance", "nonce", "code"
    ]

def decodeStateObservationAt
    (path : Path)
    (json : Lean.Json) : DecodeResult StateObservation := do
  ensureExactObject path json ["probes", "schema"] ["probes", "schema"]
  let probes ← decodeArrayAt decodeProbeObservationAt (path.field "probes")
    (← requireField path json "probes")
  let schemaPath := path.field "schema"
  let schema ← decodeStringAt schemaPath (← requireField path json "schema")
  unless schema == stateObservationSchema do
    failAt schemaPath .invalidSchema (.mkObj [
      ("expected", stateObservationSchema), ("actual", schema)
    ])
  pure { probes }

private def decodeExecutionObservationValueAt
    (path : Path)
    (json : Lean.Json) : DecodeResult ExecutionObservation := do
  ensureExactObject path json
    ["journal", "outcome", "state"] ["journal", "outcome", "state"]
  let journal ← decodeJournalObservationAt (path.field "journal")
    (← requireField path json "journal")
  let outcome ← decodeTerminalOutcomeAt (path.field "outcome")
    (← requireField path json "outcome")
  let state ← decodeStateObservationAt (path.field "state")
    (← requireField path json "state")
  pure { outcome, journal, state }

private def encodeOptionalEndpoint {α : Type}
    (encode : α → Lean.Json) : Option α → Lean.Json
  | none => .null
  | some value => encode value

private def probeEndpointJson
    (probe : ProbeObservation) : Lean.Json × Lean.Json :=
  match probe with
  | .accountPresence _ initial committed =>
      (.bool initial, .bool committed)
  | .storage _ _ initial committed
  | .balance _ initial committed
  | .nonce _ initial committed =>
      (encodeOptionalEndpoint Solcore.Oracle.V5.encodeWord initial,
        encodeOptionalEndpoint Solcore.Oracle.V5.encodeWord committed)
  | .code _ initial committed =>
      (encodeOptionalEndpoint Solcore.Oracle.V5.encodeContractId initial,
        encodeOptionalEndpoint Solcore.Oracle.V5.encodeContractId committed)

private def validateRollbackProbesAt
    (path : Path) : Nat → List ProbeObservation → DecodeResult Unit
  | _, [] => pure ()
  | index, probe :: rest =>
      if probe.endpointsEqual then
        validateRollbackProbesAt path (index + 1) rest
      else
        let endpoints := probeEndpointJson probe
        invalidTagAt (((path.field "state").field "probes").index index |>.field
          "committed") endpoints.2 endpoints.1

/-- Select the first rollback invariant violation in the published order. -/
private def validateExecutionObservationAt
    (path : Path)
    (observation : ExecutionObservation) : DecodeResult Unit :=
  match observation.outcome with
  | .returned _ => pure ()
  | .preflightRejected _
  | .reverted _
  | .trapped _ =>
      if observation.journal.createdAddresses.isEmpty then
        if observation.journal.logs.isEmpty then
          validateRollbackProbesAt path 0 observation.state.probes
        else
          invalidTagAt ((path.field "journal").field "logs")
            (.arr <| observation.journal.logs.toArray.map
              Solcore.Oracle.V5.encodeLogObservation)
            (.arr #[])
      else
        invalidTagAt ((path.field "journal").field "createdAddresses")
          (.arr <| observation.journal.createdAddresses.toArray.map
            Solcore.Oracle.V5.encodeAddress)
          (.arr #[])

def decodeExecutionObservationAt
    (path : Path)
    (json : Lean.Json) : DecodeResult ValidExecutionObservation := do
  ensureExactObject path json ["schema", "value"] ["schema", "value"]
  let schemaPath := path.field "schema"
  let schema ← decodeStringAt schemaPath (← requireField path json "schema")
  unless schema == executionSchema do
    failAt schemaPath .invalidSchema (.mkObj [
      ("expected", executionSchema), ("actual", schema)
    ])
  let valuePath := path.field "value"
  let observation ← decodeExecutionObservationValueAt valuePath
    (← requireField path json "value")
  match validateExecutionObservationAt valuePath observation with
  | .error error => throw error
  | .ok _ =>
      match ValidExecutionObservation.of? observation with
      | some valid => pure valid
      | none => invalidTagAt valuePath Lean.Json.null (Lean.Json.mkObj
          [("constraint", "valid-execution-observation")])

def decodeExecutionObservation
    (json : Lean.Json) : DecodeResult ValidExecutionObservation :=
  decodeExecutionObservationAt .root json

end Solcore.Oracle.V5.Wire
