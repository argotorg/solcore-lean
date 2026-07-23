import Solcore.Baseline
import Solcore.Feature
import Solcore.Oracle.Schema

set_option autoImplicit false

namespace Solcore.Oracle

def capabilityReport : CapabilityReport := {
  schema := capabilitiesSchema
  spec := draftLanguage.id
  profile := draftCoreProfile
  profileDigest := draftCoreProfileDigest
  baselines := implementationBaselines
  implementedQueries := #[.capabilities]
  unavailableQueries := #[.parse, .resolve, .check, .elaborate, .eval, .contract]
  features := featureMatrix
}

def unsupportedVerdict (query : QueryKind) : Verdict :=
  .unsupported query.phase #[]

def handle (request : Request) : Except ProtocolError Response := do
  match request.validationErrors with
  | error :: _ =>
      throw {
        id := if request.id.isEmpty then none else some request.id
        code := "invalid-request"
        display := error
      }
  | [] =>
      let verdict :=
        if request.query.kind == .capabilities then
          .accepted .protocol {
            schema := capabilitiesSchema
            value := Lean.toJson capabilityReport
          }
        else
          unsupportedVerdict request.query.kind
      let verdict :=
        match verdict.validationErrorsFor request.query.kind with
        | [] => verdict
        | _ => .internalError (some request.query.kind.phase) "oracle-invariant"
      return {
        schema := schemaVersion
        id := request.id
        spec := draftLanguage.id
        profile := request.profile
        query := request.query.kind
        verdict
      }

end Solcore.Oracle
