import Solcore.Oracle.V5.TypedHandler

/-! End-to-end typed request handling regressions for Oracle v5. -/

set_option autoImplicit false

namespace Tests.OracleV5TypedHandler

open Solcore.Core.Wire
open Solcore.Oracle.V5
open Solcore.Semantics

private def requestId : RequestId := ⟨"id", by decide⟩
private def target : Address := ⟨1, by decide⟩
private def seven : Solcore.Core.Word := ⟨7, by decide⟩

private def program : V3.Program := {
  resultType := .word
  dataDefinitions := []
  body := .word seven
}

private def badProgram : V3.Program := {
  resultType := .word
  dataDefinitions := []
  body := .var 14
}

private def scenario : Scenario := {
  contracts := [{ id := "root", spec := .checkedCore program }]
  world := {
    accounts := [{
      address := target
      balance := Solcore.Core.Word.zero
      nonce := Solcore.Core.Word.zero
      storage := []
      code := some "root"
    }]
  }
  environment := {
    callRegistry := []
    creationTemplates := []
    creationAddressPolicy := { routes := [], defaultAddress := target }
  }
  invocation := {
    target
    caller := ⟨2, by decide⟩
    callValue := Solcore.Core.Word.zero
    calldata := ByteArray.empty
    probes := []
  }
}

private def requestWith
    (query : Query)
    (limits : Limits := Limits.default) : Request := {
  id := requestId
  limits
  query
}

private theorem defaultValid : Limits.default.Valid := by
  show Limits.default.calldataBytes < Solcore.Core.wordModulus
  native_decide

private def capabilitiesAccepted : Bool :=
  let response := TypedHandler.handle (requestWith .capabilities) defaultValid
  response.id == requestId && response.queryKind == .capabilities &&
    response.verdictKind == .accepted && response.phase == some .protocol

private def capabilityEnvelopeBudgeted : Bool :=
  let limits := { Limits.default with identifierBytes := 0 }
  have valid : Limits.Valid limits := by
    show Limits.default.calldataBytes < Solcore.Core.wordModulus
    native_decide
  let response := TypedHandler.handle (requestWith .capabilities limits) valid
  match response.body with
  | .capabilities (.inconclusive (.preflight exhaustion)) =>
      exhaustion.resource == .identifierBytes &&
        exhaustion.limit == 0 && exhaustion.consumed == 2
  | _ => false

private def coreCheckAccepted : Bool :=
  let response := TypedHandler.handle (requestWith (.coreCheck program))
    defaultValid
  match response.body with
  | .coreCheck (.accepted result) => result.resultType == .word
  | _ => false

private def coreCheckRejected : Bool :=
  let response := TypedHandler.handle (requestWith (.coreCheck badProgram))
    defaultValid
  match response.body with
  | .coreCheck (.rejected diagnostic) =>
      diagnostic.code == "core.check.unbound-variable" &&
        diagnostic.phase == .coreChecking && diagnostic.path == ["program"]
  | _ => false

private def executionAccepted : Bool :=
  let response := TypedHandler.handle (requestWith (.execute scenario))
    defaultValid
  match response.body with
  | .execute (.executed observation) =>
      observation.outcome == .returned (encodeWordBytesBE seven) &&
        observation.journal == { logs := [], createdAddresses := [] } &&
        observation.state.probes.isEmpty
  | _ => false

private def allChecks : Bool :=
  capabilitiesAccepted && capabilityEnvelopeBudgeted && coreCheckAccepted &&
    coreCheckRejected && executionAccepted

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5TypedHandler : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 typed handler changed")

end Tests.OracleV5TypedHandler
