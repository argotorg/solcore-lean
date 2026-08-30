import Solcore.Oracle.V5.ScenarioPreparation

/-! End-to-end regressions for deterministic Oracle v5 scenario preparation. -/

set_option autoImplicit false

namespace Tests.OracleV5ScenarioPreparation

open Solcore.Core.Wire
open Solcore.Oracle.V5
open Solcore.Semantics

private def target : Address := ⟨1, by decide⟩
private def caller : Address := ⟨2, by decide⟩
private def ten : Solcore.Core.Word := ⟨10, by decide⟩
private def three : Solcore.Core.Word := ⟨3, by decide⟩
private def one : Solcore.Core.Word := ⟨1, by decide⟩

private def program : V3.Program := {
  resultType := .word
  dataDefinitions := []
  body := .word three
}

private def rootContract : ContractInput := {
  id := "root"
  spec := .checkedCore program
}

private def callerAccount : AccountInput := {
  address := caller
  balance := ten
  nonce := Solcore.Core.Word.zero
  storage := []
  code := none
}

private def targetAccount : AccountInput := {
  address := target
  balance := three
  nonce := Solcore.Core.Word.zero
  storage := []
  code := some "root"
}

private def validWorld : WorldInput := {
  accounts := [callerAccount, targetAccount]
}

private def validEnvironment : EnvironmentInput := {
  callRegistry := []
  creationTemplates := []
  creationAddressPolicy := { routes := [], defaultAddress := target }
}

private def validInvocation : InvocationInput := {
  target
  caller
  callValue := one
  calldata := ByteArray.empty
  probes := [.balance caller, .balance target, .code target]
}

private def validScenario : Scenario := {
  contracts := [rootContract]
  world := validWorld
  environment := validEnvironment
  invocation := validInvocation
}

private theorem defaultLimitsValid : Limits.default.Valid := by
  show Limits.default.calldataBytes < Solcore.Core.wordModulus
  native_decide

private def prepare
    (scenario : Scenario)
    (within : scenario.invocation.calldata.size ≤
      Limits.default.calldataBytes) :=
  ScenarioPreparation.prepare Limits.default defaultLimitsValid scenario within

private def preparationSucceeds : Bool :=
  match prepare validScenario (by native_decide) with
  | .error _ => false
  | .ok prepared =>
      prepared.package.entries.map (fun entry => entry.id.value) == ["root"] &&
        prepared.world.balance? caller == some ten &&
        prepared.world.balance? target == some three &&
        (prepared.world.code? target).map (fun code => code.program) ==
            some program.toCore &&
        (prepared.environment.callRegistry.lookup target).isNone &&
        prepared.invocation.invocation.target == target &&
        prepared.invocation.invocation.caller == caller &&
        prepared.invocation.probes.values == validInvocation.probes

private def contractFailurePrecedesWorld : Bool :=
  let scenario := {
    validScenario with
    contracts := [{ rootContract with id := "invalid id!" }]
    world := { accounts := [{ callerAccount with code := some "missing" }] }
  }
  match prepare scenario (by native_decide) with
  | .error (.contractAdmission (.invalidContractId actual)) =>
      actual == "invalid id!"
  | _ => false

private def worldFailurePrecedesEnvironment : Bool :=
  let scenario := {
    validScenario with
    world := { validWorld with accounts :=
      validWorld.accounts ++ [callerAccount] }
    environment := { validEnvironment with callRegistry :=
      [{ address := target, contract := "missing" }] }
  }
  match prepare scenario (by native_decide) with
  | .error (.worldValidation (.duplicateAccount address)) => address == caller
  | _ => false

private def environmentFailurePrecedesProbe : Bool :=
  let scenario := {
    validScenario with
    environment := { validEnvironment with callRegistry :=
      [{ address := target, contract := "missing" }] }
    invocation := { validInvocation with probes :=
      [.balance caller, .balance caller] }
  }
  match prepare scenario (by native_decide) with
  | .error (.environmentValidation
      (.danglingCallContract address id)) =>
      address == target && id == "missing"
  | _ => false

private def duplicateProbeRejectedLast : Bool :=
  let scenario := { validScenario with invocation :=
    { validInvocation with probes := [.balance caller, .balance caller] } }
  match prepare scenario (by native_decide) with
  | .error (.probeValidation duplicate) =>
      duplicate.firstIndex == 0 && duplicate.secondIndex == 1
  | _ => false

private def allChecks : Bool :=
  preparationSucceeds && contractFailurePrecedesWorld &&
    worldFailurePrecedesEnvironment && environmentFailurePrecedesProbe &&
    duplicateProbeRejectedLast

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5ScenarioPreparation : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 scenario preparation precedence changed")

end Tests.OracleV5ScenarioPreparation
