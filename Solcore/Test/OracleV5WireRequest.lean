import Solcore.Oracle.V5.Wire.Decode

/-! Roundtrip, namespace, path, and resource regressions for Oracle v5 requests. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Core.Wire
open Solcore.Oracle.V5
open Solcore.Oracle.V5.Wire
open Solcore.Semantics

private def requestId : RequestId := ⟨"wire-test", by decide⟩
private def addressA : Address := ⟨1, by decide⟩
private def addressB : Address := ⟨2, by decide⟩
private def slot : Word := ⟨3, by decide⟩
private def value : Word := ⟨4, by decide⟩
private def templateId : Word := ⟨5, by decide⟩

private def rawProgram : V3.Program := {
  resultType := .word
  dataDefinitions := []
  body := .word value
}

private def methodProgram : V3.Program := {
  resultType := .function .word .word
  dataDefinitions := []
  body := .lambda .word .word (.var 0)
}

private def scenario : Scenario := {
  contracts := [
    { id := "abi", spec := .staticWordAbi [{
      name := "identity"
      implementation := methodProgram
    }] },
    { id := "raw", spec := .checkedCore rawProgram }
  ]
  world := { accounts := [{
    address := addressA
    balance := value
    nonce := Word.zero
    storage := [{ slot, value }]
    code := some "raw"
  }] }
  environment := {
    callRegistry := [{ address := addressB, contract := "raw" }]
    creationTemplates := [{
      templateId
      initializer := "raw"
      runtime := "raw"
    }]
    creationAddressPolicy := {
      routes := [{ creator := addressA, nonce := Word.zero, address := addressB }]
      defaultAddress := addressA
    }
  }
  invocation := {
    target := addressA
    caller := addressB
    callValue := Word.zero
    calldata := [0x01, 0x02].toByteArray
    probes := [
      .accountPresence addressA,
      .storage addressA slot,
      .balance addressA,
      .nonce addressA,
      .code addressA
    ]
  }
}

private def requestWith
    (limits : Limits := Limits.default)
    (query : Query := .execute scenario) : Request := {
  id := requestId
  limits
  query
}

private def roundtrip : Bool :=
  let request := requestWith
  match decodeJson (encodeRequest request), decodeText (encodeRequestText request) with
  | .ok (.request decodedJson), .ok (.request decodedText) =>
      decodedJson.value == request && decodedText.value == request
  | _, _ => false

private def setField
    (json : Lean.Json)
    (name : String)
    (value : Lean.Json) : Lean.Json :=
  match json with
  | .obj fields => .obj (fields.insert name value)
  | other => other

private def nestedSet
    (json : Lean.Json)
    (name childName : String)
    (value : Lean.Json) : Lean.Json :=
  match json.getObjVal? name with
  | .ok child => setField json name (setField child childName value)
  | .error _ => json

private def errorCodePath
    (result : Except Solcore.Oracle.V5.ProtocolError DecodeOutcome) :
    Option (String × String) :=
  match result with
  | .error error => some (error.code, error.path)
  | .ok _ => none

private def rawErrorCodePath {alpha : Type}
    (result : DecodeResult alpha) : Option (String × String) :=
  match result with
  | .error error => some (error.code, error.path.toPointer)
  | .ok _ => none

private def rootIdentityFailures : Bool :=
  let base := encodeRequest (requestWith (query := .capabilities))
  errorCodePath (decodeJson (setField base "schema" "future")) ==
      some ("oracle.wire.invalid-schema", "/schema") &&
    errorCodePath (decodeJson (setField base "spec" "future")) ==
      some ("oracle.wire.invalid-spec", "/spec") &&
    errorCodePath (decodeJson (setField base "id" "")) ==
      some ("oracle.wire.invalid-request-id", "/id") &&
    errorCodePath (decodeJson (setField base "future" true)) ==
      some ("oracle.wire.unknown-field", "/future")

private def invalidProfileFailure : Bool :=
  let base := encodeRequest (requestWith (query := .capabilities))
  let profile := Lean.Json.mkObj [
    ("id", "future"),
    ("digest", "sha256:future")
  ]
  errorCodePath (decodeJson (setField base "profile" profile)) ==
    some ("oracle.wire.invalid-profile", "/profile")

private def invalidLimitFailure : Bool :=
  let base := encodeRequest (requestWith (query := .capabilities))
  let invalid := nestedSet base "limits" "calldataBytes"
    (Lean.toJson Solcore.Core.wordModulus)
  errorCodePath (decodeJson invalid) ==
    some ("oracle.wire.invalid-limit", "/limits/calldataBytes")

private def coreOwnershipFailure : Bool :=
  let base := encodeRequest (requestWith (query := .coreCheck rawProgram))
  let invalid := nestedSet base "query" "program" .null
  errorCodePath (decodeJson invalid) ==
    some ("core.wire.expected-object", "/query/program")

private def malformedDuplicateKey : Bool :=
  let text :=
    "{\"schema\":\"solcore-oracle/v5\",\"schema\":\"solcore-oracle/v5\"}"
  errorCodePath (decodeText text) == some ("malformed-json", "")

private def scalarReasons : Bool :=
  let wordError := decodeWordAt (Path.root.field "word") "0X00"
  let addressError := decodeAddressAt (Path.root.field "address") "0x00"
  let bytesError := decodeBytesAt (Path.root.field "bytes") "0x0"
  match wordError, addressError, bytesError with
  | .error (.oracle wordPath .invalidWord wordArgs),
      .error (.oracle addressPath .invalidAddress addressArgs),
      .error (.oracle bytesPath .invalidBytes bytesArgs) =>
      wordPath.toPointer == "/word" &&
        addressPath.toPointer == "/address" &&
        bytesPath.toPointer == "/bytes" &&
        wordArgs == Lean.Json.mkObj [("reason", "prefix")] &&
        addressArgs == Lean.Json.mkObj [("reason", "length")] &&
        bytesArgs == Lean.Json.mkObj [("reason", "odd-length")]
  | _, _, _ => false

private def taggedBroadPrepassExact : Bool :=
  let contractPath := Path.root.field "contract"
  let queryPath := Path.root.field "query"
  let probePath := Path.root.field "probe"
  let invalidContract := .mkObj [
    ("id", "raw"), ("kind", "future"), ("zzz", .null)
  ]
  let missingContractId := .mkObj [("kind", "future")]
  let invalidQuery := .mkObj [
    ("kind", "future"), ("zzz", .null)
  ]
  let invalidProbe := .mkObj [
    ("address", encodeAddress addressA), ("kind", "future"),
    ("zzz", .null)
  ]
  let missingProbeAddress := .mkObj [("kind", "future")]
  rawErrorCodePath (decodeRawContractAt contractPath invalidContract) ==
      some ("oracle.wire.unknown-field", "/contract/zzz") &&
    rawErrorCodePath (decodeRawContractAt contractPath missingContractId) ==
      some ("oracle.wire.missing-field", "/contract/id") &&
    rawErrorCodePath (decodeRawQueryAt queryPath invalidQuery) ==
      some ("oracle.wire.unknown-field", "/query/zzz") &&
    rawErrorCodePath (decodeProbeAt probePath invalidProbe) ==
      some ("oracle.wire.unknown-field", "/probe/zzz") &&
    rawErrorCodePath (decodeProbeAt probePath missingProbeAddress) ==
      some ("oracle.wire.missing-field", "/probe/address")

private def coreBudgetInconclusive : Bool :=
  let limits := { Limits.default with coreNodes := 0 }
  match decodeJson (encodeRequest (requestWith limits (.coreCheck rawProgram))) with
  | .ok (.inconclusive id .coreCheck exhaustion) =>
      id == requestId && exhaustion.resource == .coreNodes &&
        exhaustion.limit == 0 && exhaustion.consumed == 1
  | _ => false

private def jsonBudgetInconclusive : Bool :=
  let limits := { Limits.default with jsonDepth := 0 }
  match decodeJson (encodeRequest (requestWith limits (.coreCheck rawProgram))) with
  | .ok (.inconclusive id .coreCheck exhaustion) =>
      id == requestId && exhaustion.resource == .jsonDepth &&
        exhaustion.limit == 0 && exhaustion.consumed > 0
  | _ => false

private def typedBudgetInconclusive : Bool :=
  let limits := { Limits.default with scenarioEntries := 12 }
  match decodeJson (encodeRequest (requestWith limits)) with
  | .ok (.inconclusive id .execute exhaustion) =>
      id == requestId && exhaustion.resource == .scenarioEntries &&
        exhaustion.limit == 12 && exhaustion.consumed == 13
  | _ => false

private theorem compileTimeWireRequestRegressions :
    roundtrip = true ∧
      rootIdentityFailures = true ∧
      invalidProfileFailure = true ∧
      invalidLimitFailure = true ∧
      coreOwnershipFailure = true ∧
      malformedDuplicateKey = true ∧
      scalarReasons = true ∧
      taggedBroadPrepassExact = true ∧
      jsonBudgetInconclusive = true ∧
      coreBudgetInconclusive = true ∧
      typedBudgetInconclusive = true := by
  native_decide

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def testOracleV5WireRequest : IO Unit := do
  assertTrue roundtrip "Oracle v5 request JSON/text roundtrip changed"
  assertTrue (rootIdentityFailures && invalidProfileFailure && invalidLimitFailure)
    "Oracle v5 shallow identity or Limits errors changed"
  assertTrue (coreOwnershipFailure && malformedDuplicateKey && scalarReasons)
    "Oracle/Core wire ownership, strict parsing, or scalar reasons changed"
  assertTrue taggedBroadPrepassExact
    "Oracle v5 tagged-object broad structural precedence changed"
  assertTrue (jsonBudgetInconclusive && coreBudgetInconclusive &&
    typedBudgetInconclusive)
    "Oracle v5 preflight resource ordering changed"

end Tests
