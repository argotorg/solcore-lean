import Solcore.Oracle.V5.Wire.ObservationDecode

/-! Round-trip and exact-path regressions for Oracle v5 observations. -/

set_option autoImplicit false

namespace Tests.OracleV5ObservationDecode

open Solcore.Oracle.V5
open Solcore.Oracle.V5.Wire
open Solcore.Semantics

private def addressOne : Address := ⟨1, by decide⟩
private def addressTwo : Address := ⟨2, by decide⟩
private def zero : Solcore.Core.Word := ⟨0, by decide⟩
private def one : Solcore.Core.Word := ⟨1, by decide⟩
private def two : Solcore.Core.Word := ⟨2, by decide⟩
private def runtimeId : ContractId := ⟨"runtime", by decide⟩

private def probes : List ProbeObservation := [
  .accountPresence addressOne false true,
  .storage addressOne two none (some zero),
  .balance addressOne (some zero) none,
  .nonce addressOne none (some one),
  .code addressOne none (some runtimeId)
]

private def journal : JournalObservation := {
  logs := [
    { emitter := addressOne, topic := one, payload := two },
    { emitter := addressOne, topic := one, payload := two }
  ]
  createdAddresses := [addressTwo, addressOne, addressOne]
}

private def observation (outcome : TerminalOutcome) : ExecutionObservation := {
  outcome
  journal
  state := { probes }
}

private def observations : List ExecutionObservation := [
  observation (.preflightRejected .senderAbsent),
  observation (.preflightRejected .recipientAbsent),
  observation (.preflightRejected .insufficientBalance),
  observation (.preflightRejected .recipientOverflow),
  observation (.returned (ByteArray.mk #[0, 15, 255])),
  observation (.reverted ByteArray.empty),
  observation (.trapped two)
]

private def roundTripsExact : Bool :=
  observations.all fun expected =>
    match decodeExecutionObservation
        (Solcore.Oracle.V5.encodeExecutionObservation expected) with
    | .ok actual => actual == expected
    | .error _ => false

private def errorIs {α : Type}
    (result : DecodeResult α)
    (code path : String)
    (arguments : Lean.Json) : Bool :=
  match result with
  | .ok _ => false
  | .error error =>
      error.code == code && error.path.toPointer == path &&
        error.arguments == arguments

private def emptyJournalJson : Lean.Json :=
  .mkObj [("logs", .arr #[]), ("createdAddresses", .arr #[])]

private def stateJson
    (probes : Array Lean.Json)
    (schema : String := stateObservationSchema) : Lean.Json :=
  .mkObj [("schema", schema), ("probes", .arr probes)]

private def executionJson
    (outcome : Lean.Json)
    (journal : Lean.Json := emptyJournalJson)
    (state : Lean.Json := stateJson #[]) : Lean.Json :=
  .mkObj [
    ("schema", executionSchema),
    ("value", .mkObj [
      ("outcome", outcome), ("journal", journal), ("state", state)
    ])
  ]

private def unknownOutcomeFieldExact : Bool :=
  errorIs (decodeExecutionObservation <| executionJson <| .mkObj [
      ("kind", "returned"), ("returndata", "0x"), ("future", true)
    ])
    "oracle.wire.unknown-field" "/value/outcome/future"
    (.mkObj [("field", "future")])

private def invalidBytesPathExact : Bool :=
  errorIs (decodeExecutionObservation <| executionJson <| .mkObj [
      ("kind", "returned"), ("returndata", "0x0")
    ])
    "oracle.wire.invalid-bytes" "/value/outcome/returndata"
    (.mkObj [("reason", "odd-length")])

private def invalidStateSchemaExact : Bool :=
  errorIs (decodeExecutionObservation <| executionJson
      (.mkObj [("kind", "returned"), ("returndata", "0x")])
      (state := stateJson #[] "future-state"))
    "oracle.wire.invalid-schema" "/value/state/schema"
    (.mkObj [
      ("expected", stateObservationSchema), ("actual", "future-state")
    ])

private def invalidExecutionSchemaExact : Bool :=
  let json := .mkObj [
    ("schema", "future-execution"),
    ("value", .mkObj [
      ("outcome", .mkObj [("kind", "returned"), ("returndata", "0x")]),
      ("journal", emptyJournalJson), ("state", stateJson #[])
    ])
  ]
  errorIs (decodeExecutionObservation json)
    "oracle.wire.invalid-schema" "/schema"
    (.mkObj [
      ("expected", executionSchema), ("actual", "future-execution")
    ])

private def invalidContractIdExact : Bool :=
  let codeProbe := .mkObj [
    ("kind", "code"),
    ("address", Solcore.Oracle.V5.Wire.encodeAddress addressOne),
    ("initial", .null),
    ("committed", "1bad")
  ]
  errorIs (decodeExecutionObservation <| executionJson
      (.mkObj [("kind", "returned"), ("returndata", "0x")])
      (state := stateJson #[codeProbe]))
    "oracle.wire.invalid-tag" "/value/state/probes/0/committed"
    (.mkObj [
      ("actual", "1bad"),
      ("expected", "[A-Za-z_][A-Za-z0-9_.-]*")
    ])

private def missingLogFieldExact : Bool :=
  let incompleteLog := .mkObj [
    ("emitter", Solcore.Oracle.V5.Wire.encodeAddress addressOne),
    ("topic", Solcore.Oracle.V5.Wire.encodeWord one)
  ]
  let badJournal := .mkObj [
    ("logs", .arr #[incompleteLog]), ("createdAddresses", .arr #[])
  ]
  errorIs (decodeExecutionObservation <| executionJson
      (.mkObj [("kind", "returned"), ("returndata", "0x")])
      (journal := badJournal))
    "oracle.wire.missing-field" "/value/journal/logs/0/payload"
    (.mkObj [("field", "payload")])

private def committedEndpointPrecedesInitial : Bool :=
  let storageProbe := .mkObj [
    ("kind", "storage"),
    ("address", Solcore.Oracle.V5.Wire.encodeAddress addressOne),
    ("slot", Solcore.Oracle.V5.Wire.encodeWord zero),
    ("initial", "bad-initial"),
    ("committed", "bad-committed")
  ]
  match decodeExecutionObservation <| executionJson
      (.mkObj [("kind", "returned"), ("returndata", "0x")])
      (state := stateJson #[storageProbe]) with
  | .ok _ => false
  | .error error =>
      error.code == "oracle.wire.invalid-word" &&
        error.path.toPointer == "/value/state/probes/0/committed"

private def invalidOutcomeTagExact : Bool :=
  errorIs (decodeExecutionObservation <| executionJson <| .mkObj [
      ("kind", "future")
    ])
    "oracle.wire.invalid-tag" "/value/outcome/kind"
    (.mkObj [
      ("actual", "future"),
      ("expected", .arr #[
        "preflightRejected", "returned", "reverted", "trapped"
      ])
    ])

private def allChecks : Bool :=
  roundTripsExact && unknownOutcomeFieldExact && invalidBytesPathExact &&
    invalidStateSchemaExact && invalidExecutionSchemaExact && invalidContractIdExact &&
    missingLogFieldExact && committedEndpointPrecedesInitial &&
    invalidOutcomeTagExact

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5ObservationDecode : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 observation decoder changed")

end Tests.OracleV5ObservationDecode
