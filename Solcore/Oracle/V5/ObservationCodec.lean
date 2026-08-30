import Solcore.Oracle.V5.Observation
import Solcore.Oracle.V5.Wire.Scalar

/-! Canonical JSON encoding for total Oracle v5 execution observations. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5

open Solcore.Semantics

/-- Encode one runtime address with its exact 160-bit lowercase spelling. -/
def encodeAddress (address : Address) : Lean.Json :=
  Wire.encodeAddress address

/-- Encode one Core word with its exact 256-bit lowercase spelling. -/
def encodeWord (word : Solcore.Core.Word) : Lean.Json :=
  Wire.encodeWord word

/-- Encode an arbitrary byte sequence with two lowercase digits per byte. -/
def encodeBytes (bytes : Bytes) : Lean.Json :=
  Wire.encodeBytes bytes

/-- Contract identifiers have already passed the closed v5 grammar. -/
def encodeContractId (id : ContractId) : Lean.Json :=
  id.value

private def encodeOptional {α : Type}
    (encode : α → Lean.Json) : Option α → Lean.Json
  | none => .null
  | some value => encode value

def encodeBalanceTransferFailure : BalanceTransferFailure → Lean.Json
  | .senderAbsent => "senderAbsent"
  | .recipientAbsent => "recipientAbsent"
  | .insufficientBalance => "insufficientBalance"
  | .recipientOverflow => "recipientOverflow"

/-- Encode all four terminal outcomes without an ABI-length assumption. -/
def encodeTerminalOutcome : TerminalOutcome → Lean.Json
  | .preflightRejected reason => .mkObj [
      ("kind", "preflightRejected"),
      ("reason", encodeBalanceTransferFailure reason)
    ]
  | .returned returndata => .mkObj [
      ("kind", "returned"),
      ("returndata", encodeBytes returndata)
    ]
  | .reverted revertdata => .mkObj [
      ("kind", "reverted"),
      ("revertdata", encodeBytes revertdata)
    ]
  | .trapped reason => .mkObj [
      ("kind", "trapped"),
      ("reason", encodeWord reason)
    ]

def encodeLogObservation (log : LogObservation) : Lean.Json :=
  .mkObj [
    ("emitter", encodeAddress log.emitter),
    ("topic", encodeWord log.topic),
    ("payload", encodeWord log.payload)
  ]

def encodeJournalObservation (journal : JournalObservation) : Lean.Json :=
  .mkObj [
    ("logs", .arr <| journal.logs.toArray.map encodeLogObservation),
    ("createdAddresses",
      .arr <| journal.createdAddresses.toArray.map encodeAddress)
  ]

/-- Encode every probe while preserving the requested order and null endpoints. -/
def encodeProbeObservation : ProbeObservation → Lean.Json
  | .accountPresence address initial committed => .mkObj [
      ("kind", "accountPresence"),
      ("address", encodeAddress address),
      ("initial", initial),
      ("committed", committed)
    ]
  | .storage address slot initial committed => .mkObj [
      ("kind", "storage"),
      ("address", encodeAddress address),
      ("slot", encodeWord slot),
      ("initial", encodeOptional encodeWord initial),
      ("committed", encodeOptional encodeWord committed)
    ]
  | .balance address initial committed => .mkObj [
      ("kind", "balance"),
      ("address", encodeAddress address),
      ("initial", encodeOptional encodeWord initial),
      ("committed", encodeOptional encodeWord committed)
    ]
  | .nonce address initial committed => .mkObj [
      ("kind", "nonce"),
      ("address", encodeAddress address),
      ("initial", encodeOptional encodeWord initial),
      ("committed", encodeOptional encodeWord committed)
    ]
  | .code address initial committed => .mkObj [
      ("kind", "code"),
      ("address", encodeAddress address),
      ("initial", encodeOptional encodeContractId initial),
      ("committed", encodeOptional encodeContractId committed)
    ]

/-- State observations always carry the fixed v1 schema marker. -/
def encodeStateObservation (state : StateObservation) : Lean.Json :=
  .mkObj [
    ("schema", stateObservationSchema),
    ("probes", .arr <| state.probes.toArray.map encodeProbeObservation)
  ]

def encodeExecutionObservationValue
    (observation : ExecutionObservation) : Lean.Json :=
  .mkObj [
    ("outcome", encodeTerminalOutcome observation.outcome),
    ("journal", encodeJournalObservation observation.journal),
    ("state", encodeStateObservation observation.state)
  ]

/-- Encode the complete value beneath an `executed` verdict. -/
def encodeExecutionObservation
    (observation : ExecutionObservation) : Lean.Json :=
  .mkObj [
    ("schema", executionSchema),
    ("value", encodeExecutionObservationValue observation)
  ]

end Solcore.Oracle.V5
