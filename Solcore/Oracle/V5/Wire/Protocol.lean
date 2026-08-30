import Solcore.Oracle.StrictJson
import Solcore.Oracle.V5.Response
import Solcore.Oracle.V5.Wire.Foundation

/-! Public Oracle v5 protocol-error adaptation for direct wire decoding. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.Wire

/-- Recover only a present, string-valued, valid v5 request identifier. -/
def recoverRequestId? (json : Lean.Json) : Option RequestId :=
  match json.getObjVal? "id" >>= Lean.Json.getStr? with
  | .ok value => RequestId.ofString? value
  | .error _ => none

namespace ProtocolError

/-- Preserve ownership, pointer, arguments, and display at the public boundary. -/
def toPublic
    (error : ProtocolError)
    (id : Option RequestId := none) :
    Solcore.Oracle.V5.ProtocolError := {
  id
  code := error.code
  path := error.path.toPointer
  arguments := error.arguments
  display := error.display
}

end ProtocolError

/-- Malformed text has no recoverable ID or typed-decoder ownership prefix. -/
def malformedJsonProtocolError
    (message : String) : Solcore.Oracle.V5.ProtocolError := {
  code := "malformed-json"
  display := message
}

/-- Parse the direct v5 codec with duplicate-key rejection. -/
def parseDirectText
    (text : String) :
    Except Solcore.Oracle.V5.ProtocolError Lean.Json :=
  match Solcore.Oracle.StrictJson.parse text with
  | .ok json => .ok json
  | .error message => .error (malformedJsonProtocolError message)

/--
Run a typed decoder after strict parsing, recovering the request ID only from
the successfully parsed root value.
-/
def decodeDirectTextWith {α : Type}
    (decode : Lean.Json → DecodeResult α)
    (text : String) : Except Solcore.Oracle.V5.ProtocolError α :=
  match parseDirectText text with
  | .error error => .error error
  | .ok json =>
      match decode json with
      | .ok value => .ok value
      | .error error =>
          .error (error.toPublic (recoverRequestId? json))

end Solcore.Oracle.V5.Wire
