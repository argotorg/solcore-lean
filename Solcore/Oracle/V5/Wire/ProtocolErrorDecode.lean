import Solcore.Oracle.V5.Wire.Protocol
import Solcore.Oracle.V5.Wire.ProtocolErrorArguments
import Solcore.Oracle.V5.Wire.ResponseEncode
import Solcore.Oracle.V5.Wire.Scalar

/-! Strict decoding for the public Oracle v5 protocol-error partition. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.Wire

open ProtocolErrorDecoding

private def decodeDisplayAt
    (owner : CodeOwner)
    (path : Path)
    (json : Lean.Json) : DecodeResult String := do
  let display ← decodeStringAt path json
  let expected? := match owner with
    | .malformed => none
    | .oracle => some "invalid Oracle v5 value"
    | .core => some "invalid Semantic Core v3 program"
  match expected? with
  | none => pure display
  | some expected =>
      unless display == expected do invalidTagAt path display expected
      pure display

private def decodeProtocolIdAt
    (owner : CodeOwner)
    (path : Path)
    (json : Lean.Json) : DecodeResult (Option RequestId) :=
  match owner, json with
  | .malformed, .null => pure none
  | .malformed, _ => invalidTagAt path json .null
  | _, .null => pure none
  | _, _ => some <$> decodeRequestIdAt path json

private def decodeProtocolPathAt
    (owner : CodeOwner)
    (path : Path)
    (json : Lean.Json) : DecodeResult String := do
  let value ← decodeStringAt path json
  match owner with
  | .malformed =>
      unless value == "" do invalidTagAt path value ""
  | .oracle | .core =>
      unless Solcore.Oracle.V5.ProtocolError.canonicalPointer value do
        invalidTagAt path value <| .mkObj [
          ("constraint", "rfc6901-json-pointer")]
  pure value

private def decodeProtocolSchemaAt
    (path : Path)
    (json : Lean.Json) : DecodeResult Unit := do
  let schema ← decodeStringAt path json
  unless schema == schemaVersion do
    failAt path .invalidSchema <| .mkObj [
      ("actual", schema), ("expected", schemaVersion)]

/--
Decode one parsed protocol-error value. Its exact envelope is checked first;
field values then follow lexicographic order, with arguments directed by a
non-failing read of the raw code discriminator.
-/
def decodeProtocolErrorValue
    (json : Lean.Json) : DecodeResult ValidProtocolError := do
  let path := Path.root
  let fields := ["arguments", "code", "display", "id", "kind", "path", "schema"]
  ensureExactObject path json fields fields
  let rawCode ← requireField path json "code"
  let arguments ← ProtocolErrorDecoding.decodeArgumentsAt
    (path.field "arguments") rawCode (← requireField path json "arguments")
  let (code, owner) ← ProtocolErrorDecoding.decodeCodeAt
    (path.field "code") rawCode
  let display ← decodeDisplayAt owner (path.field "display")
    (← requireField path json "display")
  let id ← decodeProtocolIdAt owner (path.field "id")
    (← requireField path json "id")
  requireLiteralAt (path.field "kind")
    (← requireField path json "kind") "protocolError"
  let decodedPath ← decodeProtocolPathAt owner (path.field "path")
    (← requireField path json "path")
  ProtocolErrorDecoding.validatePathAt
    (path.field "path") code decodedPath arguments
  decodeProtocolSchemaAt (path.field "schema")
    (← requireField path json "schema")
  let raw : Solcore.Oracle.V5.ProtocolError := {
    id, code, path := decodedPath, arguments, display
  }
  match ValidProtocolError.of? raw with
  | some error => pure error
  | none => invalidTagAt (path.field "code") code <| .mkObj [
      ("constraint", "closed-protocol-error")]

/-- Decode an already parsed public protocol-error value. -/
def decodeProtocolErrorJson
    (json : Lean.Json) : Except ValidProtocolError ValidProtocolError :=
  (decodeProtocolErrorValue json).mapError
    (fun error => error.toPublic (recoverRequestId? json))

/-- Duplicate-rejecting direct-text decoder for public protocol errors. -/
def decodeProtocolErrorText
    (text : String) : Except ValidProtocolError ValidProtocolError :=
  decodeDirectTextWith decodeProtocolErrorValue text

/-- Strictly decode and re-emit the unique canonical protocol-error spelling. -/
def canonicalizeProtocolErrorText
    (text : String) : Except ValidProtocolError String := do
  pure (encodeProtocolErrorText (← decodeProtocolErrorText text))

end Solcore.Oracle.V5.Wire
