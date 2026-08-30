import Solcore.Oracle.V5.ObservationCodec
import Solcore.Oracle.V5.Wire.Scalar

/-! Strict JSON decoding for total Oracle v5 execution observations. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.Wire

open Solcore.Semantics

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

def decodeExecutionObservationValueAt
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

def decodeExecutionObservationAt
    (path : Path)
    (json : Lean.Json) : DecodeResult ExecutionObservation := do
  ensureExactObject path json ["schema", "value"] ["schema", "value"]
  let schemaPath := path.field "schema"
  let schema ← decodeStringAt schemaPath (← requireField path json "schema")
  unless schema == executionSchema do
    failAt schemaPath .invalidSchema (.mkObj [
      ("expected", executionSchema), ("actual", schema)
    ])
  decodeExecutionObservationValueAt (path.field "value")
    (← requireField path json "value")

def decodeExecutionObservation
    (json : Lean.Json) : DecodeResult ExecutionObservation :=
  decodeExecutionObservationAt .root json

end Solcore.Oracle.V5.Wire
