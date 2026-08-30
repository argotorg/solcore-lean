import Solcore.Oracle.V5.TypedPreflight
import Solcore.Oracle.V5.Wire.Encode
import Solcore.Oracle.V5.Wire.JsonBudget
import Solcore.Oracle.V5.Wire.ProgramDecode
import Solcore.Oracle.V5.Wire.Protocol

/-! Ordered strict decoding of complete Oracle v5 requests. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.Wire

/-- A decoded request or a declared pre-execution resource result. -/
inductive DecodeOutcome where
  | request (value : DecodedRequest)
  | inconclusive
      (id : RequestId)
      (queryKind : QueryKind)
      (exhaustion : PreflightExhaustion)

private def coreExhaustion
    (exhaustion : Solcore.Core.Wire.V3.CoreBudgetExhaustion) :
    PreflightExhaustion :=
  match exhaustion.resource with
  | .depth => {
      resource := .coreDepth
      limit := exhaustion.limit
      consumed := exhaustion.consumed
      exceeded := exhaustion.exceeded
    }
  | .nodes => {
      resource := .coreNodes
      limit := exhaustion.limit
      consumed := exhaustion.consumed
      exceeded := exhaustion.exceeded
    }

/--
Decode one parsed request in the published order: shallow identities and Limits,
whole-tree JSON budgets, Oracle shape, canonical Core Programs, then typed sizes.
-/
def decodeJson
    (json : Lean.Json) :
    Except Solcore.Oracle.V5.ValidProtocolError DecodeOutcome := do
  let recoveredId := recoverRequestId? json
  let shallow ← (decodeShallowRequest json).mapError
    (fun error => error.toPublic recoveredId)
  match checkJsonBudget shallow.limits json with
  | some exhaustion =>
      pure (.inconclusive shallow.id shallow.queryKind exhaustion)
  | none =>
      let raw ← (decodeRequestShape shallow json).mapError
        (fun error => error.toPublic recoveredId)
      match decodeRequestPrograms raw with
      | .error (.protocol error) =>
          throw (error.toPublic recoveredId)
      | .error (.exhausted exhaustion) =>
          pure (.inconclusive raw.id raw.query.kind (coreExhaustion exhaustion))
      | .ok (decoded, _) =>
          match TypedPreflight.check decoded.value with
          | some exhaustion =>
              pure (.inconclusive decoded.value.id
                decoded.value.query.kind exhaustion)
          | none => pure (.request decoded)

/-- Direct text entry point using the duplicate-rejecting strict parser. -/
def decodeText
    (text : String) :
    Except Solcore.Oracle.V5.ValidProtocolError DecodeOutcome :=
  match parseDirectText text with
  | .error error => .error error
  | .ok json => decodeJson json

/-- Re-encode only a fully decoded request; inconclusive demand has no request. -/
def canonicalizeText
    (text : String) :
    Except Solcore.Oracle.V5.ValidProtocolError (Option String) := do
  match ← decodeText text with
  | .request decoded => pure (some (encodeRequestText decoded.value))
  | .inconclusive _ _ _ => pure none

end Solcore.Oracle.V5.Wire
