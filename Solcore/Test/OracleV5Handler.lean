import Solcore.Oracle.V5.Handler

/-! Strict public-boundary regressions for Oracle v5. -/

set_option autoImplicit false

namespace Tests.OracleV5Handler

open Solcore.Core.Wire
open Solcore.Oracle.V5
open Solcore.Semantics

private def requestId : RequestId := ⟨"handler", by decide⟩
private def target : Address := ⟨1, by decide⟩
private def caller : Address := ⟨2, by decide⟩
private def seven : Solcore.Core.Word := ⟨7, by decide⟩

private def program : V3.Program := {
  resultType := .word
  dataDefinitions := []
  body := .word seven
}

private def scenario : Scenario := {
  contracts := [{ id := "root", spec := .checkedCore program }]
  world := { accounts := [{
    address := target
    balance := Solcore.Core.Word.zero
    nonce := Solcore.Core.Word.zero
    storage := []
    code := some "root"
  }] }
  environment := {
    callRegistry := []
    creationTemplates := []
    creationAddressPolicy := { routes := [], defaultAddress := target }
  }
  invocation := {
    target
    caller
    callValue := Solcore.Core.Word.zero
    calldata := ByteArray.empty
    probes := [.code target]
  }
}

private def requestWith
    (query : Query)
    (limits : Limits := Limits.default) : Request := {
  id := requestId
  limits
  query
}

private def capabilitiesAccepted : Bool :=
  match handleJson (Wire.encodeRequest (requestWith .capabilities)) with
  | .ok response =>
      response.id == requestId && response.queryKind == .capabilities &&
        response.verdictKind == .accepted && response.phase == some .protocol
  | .error _ => false

private def jsonBudgetKeepsEnvelope : Bool :=
  let limits := { Limits.default with jsonDepth := 0 }
  match handleJson (Wire.encodeRequest (requestWith .capabilities limits)) with
  | .ok { id, body := .capabilities (.inconclusive exhaustion) } =>
      id == requestId && exhaustion.resource == .jsonDepth &&
        exhaustion.limit == 0 && exhaustion.consumed > 0
  | _ => false

private def coreCheckAccepted : Bool :=
  match handleJson (Wire.encodeRequest (requestWith (.coreCheck program))) with
  | .ok { body := .coreCheck (.accepted result), .. } =>
      result.resultType == .word
  | _ => false

private def executionReturned : Bool :=
  match handleJson (Wire.encodeRequest (requestWith (.execute scenario))) with
  | .ok { body := .execute (.executed observation), .. } =>
      observation.value.outcome == .returned (encodeWordBytesBE seven) &&
        observation.value.journal.logs.isEmpty &&
        observation.value.journal.createdAddresses.isEmpty &&
        observation.value.state.probes.length == 1
  | _ => false

private def repeatedExecutionIsExact : Bool :=
  let limits := { Limits.default with evaluationSteps := 128 }
  let input := Wire.encodeRequest (requestWith (.execute scenario) limits)
  match handleJson input, handleJson input with
  | .ok first, .ok second =>
      match first.body, second.body with
      | .execute (.executed _), .execute (.executed _) =>
          first == second &&
            Wire.encodeResponse first == Wire.encodeResponse second &&
            Wire.encodeResponseText first == Wire.encodeResponseText second
      | _, _ => false
  | _, _ => false

private def setField
    (json : Lean.Json)
    (name : String)
    (value : Lean.Json) : Lean.Json :=
  match json with
  | .obj fields => .obj (fields.insert name value)
  | other => other

private def protocolFailureRetainsId : Bool :=
  let input := setField
    (Wire.encodeRequest (requestWith .capabilities)) "future" true
  match handleJson input with
  | .error error =>
      error.id == some requestId &&
        error.code == "oracle.wire.unknown-field" && error.path == "/future"
  | .ok _ => false

private def totalJsonPartition : Bool :=
  let accepted := processJson (Wire.encodeRequest (requestWith .capabilities))
  let malformed := processText "{"
  accepted.getObjValD "schema" == schemaVersion &&
    accepted.getObjValD "id" == "handler" &&
    accepted.getObjValD "query" == "capabilities" &&
    (accepted.getObjValD "verdict").getObjValD "kind" == "accepted" &&
    malformed.getObjValD "kind" == "protocolError" &&
    malformed.getObjValD "code" == "malformed-json"

private def allChecks : Bool :=
  capabilitiesAccepted && jsonBudgetKeepsEnvelope && coreCheckAccepted &&
    executionReturned && repeatedExecutionIsExact &&
    protocolFailureRetainsId && totalJsonPartition

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5Handler : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 strict public handler changed")

end Tests.OracleV5Handler
