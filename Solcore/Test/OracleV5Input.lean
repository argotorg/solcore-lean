import Solcore.Oracle.V5.TypedPreflight

/-! Independent consumers of Oracle v5 input identities and typed budgets. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Core.Wire
open Solcore.Oracle.V5
open Solcore.Semantics

private def requestId : RequestId := ⟨"request", by decide⟩
private def address0 : Address := ⟨0, by decide⟩
private def address1 : Address := ⟨1, by decide⟩
private def address2 : Address := ⟨2, by decide⟩
private def address3 : Address := ⟨3, by decide⟩
private def address4 : Address := ⟨4, by decide⟩

private def program : V3.Program := {
  resultType := .word
  dataDefinitions := []
  body := .word Word.zero
}

private def scenario : Scenario := {
  contracts := [{ id := "constant", spec := .checkedCore program }]
  world := {
    accounts := [{
      address := address0
      balance := Word.zero
      nonce := Word.zero
      storage := [{ slot := Word.zero, value := Word.zero }]
      code := some "constant"
    }]
  }
  environment := {
    callRegistry := [{ address := address1, contract := "constant" }]
    creationTemplates := [{
      templateId := Word.zero
      initializer := "constant"
      runtime := "constant"
    }]
    creationAddressPolicy := {
      routes := [{ creator := address0, nonce := Word.zero, address := address2 }]
      defaultAddress := address3
    }
  }
  invocation := {
    target := address0
    caller := address4
    callValue := Word.zero
    calldata := ByteArray.mk #[0]
    probes := [.code address0]
  }
}

private def exactLimits : Limits := {
  Limits.default with
  scenarioEntries := 7
  identifierBytes := 8
  calldataBytes := 1
}

private def request : Request := {
  id := requestId
  limits := exactLimits
  query := .execute scenario
}

private theorem compileTimeCounts :
    scenario.scenarioEntries = 7 ∧
      request.maxIdentifierBytes = 8 ∧
      scenario.calldataBytes = 1 := by
  native_decide

private theorem compileTimeExactLimitsAccepted :
    TypedPreflight.check request = none := by
  native_decide

private def scenarioExceededRequest : Request := {
  request with limits := { exactLimits with scenarioEntries := 6 }
}

private def identifierExceededRequest : Request := {
  request with limits := { exactLimits with identifierBytes := 7 }
}

private def calldataExceededRequest : Request := {
  request with limits := { exactLimits with calldataBytes := 0 }
}

private def failureResource? (value : Option PreflightExhaustion) :
    Option PreflightResource :=
  value.map (fun exhaustion => exhaustion.resource)

private def identitiesAreExact : Bool :=
  RequestId.ofString? "request" == some requestId &&
  (RequestId.ofString? "").isNone &&
  (ContractId.ofString? "contract_1.v1-test").isSome &&
  (ContractId.ofString? "1contract").isNone &&
  (ContractId.ofString? "contract/name").isNone &&
  ProfileRef.canonical.id == "contract-m3a-v1" &&
  ProfileRef.canonical.digest ==
    "sha256:da3d49b830d25705634cfda568691f1f12fe5a7d038bd0b7ca5839134c1073d5"

private def prioritiesAreExact : Bool :=
  failureResource? (TypedPreflight.check scenarioExceededRequest) ==
      some .scenarioEntries &&
    failureResource? (TypedPreflight.check identifierExceededRequest) ==
      some .identifierBytes &&
    failureResource? (TypedPreflight.check calldataExceededRequest) ==
      some .calldataBytes

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

def testOracleV5Input : IO Unit := do
  assertTrue identitiesAreExact
    "Oracle v5 request, contract, or profile identities changed"
  assertTrue (TypedPreflight.check request).isNone
    "an Oracle v5 request at every typed budget boundary was rejected"
  assertTrue prioritiesAreExact
    "Oracle v5 typed budget precedence or exact measurement changed"

end Tests
