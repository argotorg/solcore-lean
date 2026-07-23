import Solcore.Oracle.Capabilities
import Solcore.Oracle.StrictJson

set_option autoImplicit false

namespace Solcore.Oracle

def processJsonLine (line : String) : Lean.Json :=
  match StrictJson.parse line.trimAscii.copy with
  | .error message =>
      Lean.toJson (show ProtocolError from {
        code := "malformed-json"
        display := message
      })
  | .ok json =>
      match decodeRequest json with
      | .error message =>
          Lean.toJson (show ProtocolError from {
            id :=
              match json.getObjVal? "id" >>= Lean.Json.getStr? with
              | .ok id => if id.isEmpty then none else some id
              | .error _ => none
            code := "invalid-request-shape"
            display := message
          })
      | .ok request =>
          match handle request with
          | .ok response => Lean.toJson response
          | .error error => Lean.toJson error

end Solcore.Oracle
