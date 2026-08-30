import Solcore.Oracle.V5.Execution

/-! End-to-end executable regressions for the Oracle v5 vertical milestone. -/

set_option autoImplicit false

namespace Tests.OracleV5Execution

open Solcore.Core.Wire
open Solcore.Oracle.V5
open Solcore.Semantics

private def target : Address := ⟨1, by decide⟩
private def caller : Address := ⟨2, by decide⟩
private def ten : Solcore.Core.Word := ⟨10, by decide⟩
private def three : Solcore.Core.Word := ⟨3, by decide⟩
private def one : Solcore.Core.Word := ⟨1, by decide⟩
private def seven : Solcore.Core.Word := ⟨7, by decide⟩
private def rootId : ContractId := ⟨"root", by decide⟩

private def program : V3.Program := {
  resultType := .word
  dataDefinitions := []
  body := .word seven
}

private def callerAccount : AccountInput := {
  address := caller
  balance := ten
  nonce := Solcore.Core.Word.zero
  storage := []
  code := none
}

private def targetAccount (code : Option String := some "root") : AccountInput := {
  address := target
  balance := three
  nonce := Solcore.Core.Word.zero
  storage := []
  code
}

private def scenarioWithWorld (accounts : List AccountInput) : Scenario := {
  contracts := [{ id := "root", spec := .checkedCore program }]
  world := { accounts }
  environment := {
    callRegistry := []
    creationTemplates := []
    creationAddressPolicy := { routes := [], defaultAddress := target }
  }
  invocation := {
    target
    caller
    callValue := one
    calldata := ByteArray.empty
    probes := [.balance caller, .balance target, .code target]
  }
}

private def validScenario : Scenario :=
  scenarioWithWorld [callerAccount, targetAccount]

private theorem defaultLimitsValid : Limits.default.Valid := by
  show Limits.default.calldataBytes < Solcore.Core.wordModulus
  native_decide

private def execute
    (scenario : Scenario)
    (fuel : Nat) : ScenarioExecutionResult :=
  if within : scenario.invocation.calldata.size ≤
      Limits.default.calldataBytes then
    Execution.execute Limits.default defaultLimitsValid scenario within fuel
  else
    .internalError .oracleResponseInvariant

private def expectedObservation : ExecutionObservation := {
  outcome := .returned (encodeWordBytesBE seven)
  journal := { logs := [], createdAddresses := [] }
  state := {
    probes := [
      .balance caller (some ten) (some ⟨9, by decide⟩),
      .balance target (some three) (some ⟨4, by decide⟩),
      .code target (some rootId) (some rootId)
    ]
  }
}

private def returnCommitsAndObserves : Bool :=
  match execute validScenario 128 with
  | .executed observation => observation == expectedObservation
  | _ => false

private def zeroFuelHasNoObservation : Bool :=
  match execute validScenario 0 with
  | .outOfFuel => true
  | _ => false

private def absentTargetRejected : Bool :=
  match execute (scenarioWithWorld [callerAccount]) 128 with
  | .rootRejected .targetAbsent => true
  | _ => false

private def absentCodeRejected : Bool :=
  match execute (scenarioWithWorld [callerAccount, targetAccount none]) 128 with
  | .rootRejected .targetCodeAbsent => true
  | _ => false

private def duplicateProbeRejectedBeforeRoot : Bool :=
  let scenario := { scenarioWithWorld [callerAccount] with invocation :=
    { validScenario.invocation with probes :=
      [.balance caller, .balance caller] } }
  match execute scenario 128 with
  | .preparationRejected (.probeValidation duplicate) =>
      duplicate.firstIndex == 0 && duplicate.secondIndex == 1
  | _ => false

private def allChecks : Bool :=
  returnCommitsAndObserves && zeroFuelHasNoObservation &&
    absentTargetRejected && absentCodeRejected &&
    duplicateProbeRejectedBeforeRoot

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5Execution : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 vertical execution milestone changed")

end Tests.OracleV5Execution
