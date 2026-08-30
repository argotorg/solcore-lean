import Solcore.Oracle.V5.TypedHandler
import Solcore.Oracle.V5.Wire.Decode
import Solcore.Oracle.V5.Wire.ResponseEncode

/-! Public Oracle v5 boundary from strict wire input to total JSON output. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5

private def preflightBody
    (queryKind : QueryKind)
    (exhaustion : PreflightExhaustion) : ResponseBody :=
  match queryKind with
  | .capabilities => .capabilities (.inconclusive exhaustion)
  | .coreCheck => .coreCheck (.inconclusive exhaustion)
  | .execute => .execute (.inconclusive (.preflight exhaustion))

/--
Handle either a proof-carrying request or a pre-execution resource result.  The
shallow decoder retains exactly the ID and query kind needed by the latter.
-/
def handleDecoded : Wire.DecodeOutcome → Response
  | .request decoded =>
      TypedHandler.handle decoded.value decoded.limitsValid
  | .inconclusive id queryKind exhaustion => {
      id
      body := preflightBody queryKind exhaustion
    }

/-- Strict handling for an already parsed JSON value. -/
def handleJson
    (json : Lean.Json) : Except ProtocolError Response :=
  handleDecoded <$> Wire.decodeJson json

/-- Direct strict-text handling, including duplicate-key rejection. -/
def handleText
    (text : String) : Except ProtocolError Response :=
  handleDecoded <$> Wire.decodeText text

/-- Encode the complete v5 result partition for an already parsed value. -/
def processJson (json : Lean.Json) : Lean.Json :=
  match handleJson json with
  | .ok response => Wire.encodeResponse response
  | .error error => Wire.encodeProtocolError error

/-- Encode the complete direct-text result partition. -/
def processText (text : String) : Lean.Json :=
  match handleText text with
  | .ok response => Wire.encodeResponse response
  | .error error => Wire.encodeProtocolError error

end Solcore.Oracle.V5
