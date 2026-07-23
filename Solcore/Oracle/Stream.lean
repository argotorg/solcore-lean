import Solcore.Oracle.Capabilities
import Solcore.Oracle.StrictJson
import Solcore.Oracle.V2.Handler

set_option autoImplicit false

namespace Solcore.Oracle

private def requestId? (json : Lean.Json) : Option String :=
  match json.getObjVal? "id" >>= Lean.Json.getStr? with
  | .ok id => if id.isEmpty then none else some id
  | .error _ => none

private def processV1Json (json : Lean.Json) : Lean.Json :=
  match decodeRequest json with
  | .error message =>
      Lean.toJson (show ProtocolError from {
        id := requestId? json
        code := "invalid-request-shape"
        display := message
      })
  | .ok request =>
      match handle request with
      | .ok response => Lean.toJson response
      | .error error => Lean.toJson error

private def processV2Json (json : Lean.Json) : Lean.Json :=
  match V2.decodeRequest json with
  | .error error =>
      Lean.toJson (error.toProtocolError (requestId? json))
  | .ok request =>
      match V2.handle request with
      | .ok response => Lean.toJson response
      | .error error => Lean.toJson error

def processJsonLine (line : String) : Lean.Json :=
  match StrictJson.parse line.trimAscii.copy with
  | .error message =>
      Lean.toJson (show ProtocolError from {
        code := "malformed-json"
        display := message
      })
  | .ok json =>
      match json.getObjVal? "schema" >>= Lean.Json.getStr? with
      | .ok schema =>
          if schema == V2.schemaVersion then
            processV2Json json
          else
            processV1Json json
      | .error _ => processV1Json json

end Solcore.Oracle
