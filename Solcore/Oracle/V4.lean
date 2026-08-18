import Solcore.Oracle.V4.Schema
import Solcore.Oracle.V4.Capabilities
import Solcore.Oracle.V4.Codec
import Solcore.Oracle.V4.Validation
import Solcore.Oracle.V4.Handler

set_option autoImplicit false

namespace Solcore.Oracle.V4

/-!
Public umbrella module for the Surface parser Oracle v4 protocol.

The conversion helpers below are the protocol boundary for strict decoder
failures. They preserve the structured decoder path and arguments while
keeping malformed JSON distinct from well-formed JSON that violates the
closed v4 request grammar.
-/

def recoverRequestId? (json : Lean.Json) : Option RequestId :=
  match json.getObjVal? "id" >>= Lean.Json.getStr? with
  | .ok value => RequestId.ofString? value
  | .error _ => none

namespace DecodeError

def toProtocolError
    (error : Solcore.Surface.Wire.V1.DecodeError)
    (id : Option RequestId := none) :
    ProtocolError := {
  id
  code := "oracle.wire." ++ error.code.wireName
  path := error.path.toPointer
  arguments := error.arguments
  display := "invalid Oracle v4 request"
}

end DecodeError

namespace TextDecodeError

def toProtocolError
    (error : TextDecodeError)
    (id : Option RequestId := none) :
    ProtocolError :=
  match error with
  | .malformedJson message => {
      id
      code := "malformed-json"
      display := message
    }
  | .invalidValue error =>
      Solcore.Oracle.V4.DecodeError.toProtocolError error id

end TextDecodeError

end Solcore.Oracle.V4
