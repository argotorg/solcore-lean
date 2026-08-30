import Solcore.Oracle.V5.Wire.Protocol
import Solcore.Oracle.V5.Wire.ResponseEncode

/-! Focused regressions for the public Oracle v5 protocol-error boundary. -/

set_option autoImplicit false

namespace Tests.OracleV5WireProtocol

open Solcore.Oracle.V5
open Solcore.Oracle.V5.Wire

private def requestId : RequestId := ⟨"request-id", by decide⟩

private def requestIdRecoveryExact : Bool :=
  recoverRequestId? (.mkObj [("id", "request-id")]) == some requestId &&
    recoverRequestId? (.mkObj [("id", "")]) == none &&
    recoverRequestId? (.mkObj [("id", .null)]) == none &&
    recoverRequestId? (.mkObj [("future", "request-id")]) == none &&
    recoverRequestId? (.arr #["request-id"]) == none

private def oracleWireError : Solcore.Oracle.V5.Wire.ProtocolError :=
  .oracle ((Path.root.field "query").field "future/field~")
    .unknownField (.mkObj [("field", "future/field~")])

private def oracleOwnershipExact : Bool :=
  let exposed := oracleWireError.toPublic (some requestId)
  exposed.id == some requestId &&
    exposed.code == "oracle.wire.unknown-field" &&
    exposed.path == "/query/future~1field~0" &&
    exposed.arguments == .mkObj [("field", "future/field~")] &&
    exposed.display == "invalid Oracle v5 value"

private def coreWireError : Solcore.Oracle.V5.Wire.ProtocolError :=
  .core {
    path := ((Path.root.field "query").field "program").field "resultType"
    code := .invalidType
    arguments := .mkObj [
      ("actual", "future"),
      ("allowed", .arr #["string", "object"])
    ]
  }

private def coreOwnershipExact : Bool :=
  let exposed := coreWireError.toPublic
  exposed.id == none &&
    exposed.code == "core.wire.invalid-type" &&
    exposed.path == "/query/program/resultType" &&
    exposed.arguments == .mkObj [
      ("actual", "future"),
      ("allowed", .arr #["string", "object"])
    ] &&
    exposed.display == "invalid Semantic Core v3 program"

private def malformedTextExact : Bool :=
  match parseDirectText "{" with
  | .ok _ => false
  | .error error =>
      error.id == none &&
        error.code == "malformed-json" &&
        error.path == "" &&
        error.arguments == .null &&
        error.display == "offset 1: unexpected end of input" &&
        encodeProtocolErrorText error ==
          "{\"arguments\":null,\"code\":\"malformed-json\"," ++
          "\"display\":\"offset 1: unexpected end of input\",\"id\":null," ++
          "\"kind\":\"protocolError\",\"path\":\"\"," ++
          "\"schema\":\"solcore-oracle/v5\"}"

private def duplicateKeyPreservesParserMessage : Bool :=
  let text := "{\"id\":\"first\",\"id\":\"second\"}"
  match Solcore.Oracle.StrictJson.parse text, parseDirectText text with
  | .error message, .error error =>
      error.code == "malformed-json" && error.arguments == .null &&
        error.display == message
  | _, _ => false

private def rejectAtFuture
    (_json : Lean.Json) : DecodeResult Unit :=
  failAt ((Path.root.field "query").field "future")
    .unknownField (.mkObj [("field", "future")])

private def directDecoderRecoversValidId : Bool :=
  match decodeDirectTextWith rejectAtFuture
      "{\"id\":\"request-id\"}" with
  | .ok _ => false
  | .error error =>
      error.id == some requestId &&
        encodeProtocolErrorText error ==
          "{\"arguments\":{\"field\":\"future\"}," ++
          "\"code\":\"oracle.wire.unknown-field\"," ++
          "\"display\":\"invalid Oracle v5 value\",\"id\":\"request-id\"," ++
          "\"kind\":\"protocolError\",\"path\":\"/query/future\"," ++
          "\"schema\":\"solcore-oracle/v5\"}"

private def malformedTextNeverRecoversId : Bool :=
  match decodeDirectTextWith rejectAtFuture
      "{\"id\":\"request-id\"" with
  | .ok _ => false
  | .error error =>
      error.id == none && error.code == "malformed-json"

private def directDecoderPreservesSuccess : Bool :=
  match decodeDirectTextWith (fun json => .ok json.compress)
      " { \"id\" : \"request-id\" } " with
  | .ok value => value == "{\"id\":\"request-id\"}"
  | .error _ => false

private def allChecks : Bool :=
  requestIdRecoveryExact && oracleOwnershipExact && coreOwnershipExact &&
    malformedTextExact && duplicateKeyPreservesParserMessage &&
    directDecoderRecoversValidId && malformedTextNeverRecoversId &&
    directDecoderPreservesSuccess

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5WireProtocol : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 protocol-error boundary changed")

end Tests.OracleV5WireProtocol
