import Solcore.Oracle.V5.ContractAdmission
import Solcore.Oracle.V5.EnvironmentMaterialization
import Solcore.Oracle.V5.InvocationPreparation
import Solcore.Oracle.V5.WorldMaterialization

/-! One deterministic preparation pipeline for Oracle v5 execution scenarios. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5

open Solcore.ContractRuntime

/-- Preparation failures retain the phase-specific closed error value. -/
inductive ScenarioPreparationError where
  | contractAdmission (error : ContractAdmissionError)
  | worldValidation (error : WorldMaterializationError)
  | environmentValidation (error : EnvironmentMaterializationError)
  | probeValidation (error : DuplicateProbe)

/-- All checked values needed immediately before root installation. -/
structure PreparedScenario where
  package : ContractAdmission.ContractPackage
  world : WorldState
  environment : ExecutionEnvironment
  invocation : PreparedInvocation

namespace ScenarioPreparation

private def resolveContract
    (package : ContractAdmission.ContractPackage)
    (rawId : String) : Option CheckedCoreContract :=
  package.lookupRaw? rawId

private def resolveCode
    (package : ContractAdmission.ContractPackage)
    (rawId : String) : Option CheckedHostCoreProgram :=
  (resolveContract package rawId).map (fun contract => contract.code)

/--
Admit contracts, then materialize world, environment, and invocation in the
published semantic precedence order.
-/
def prepare
    (limits : Limits)
    (limitsValid : limits.Valid)
    (scenario : Scenario)
    (calldataWithin : scenario.invocation.calldata.size ≤ limits.calldataBytes) :
    Except ScenarioPreparationError PreparedScenario := do
  let package ←
    (ContractAdmission.admit scenario.contracts).mapError
      ScenarioPreparationError.contractAdmission
  let world ←
    (WorldMaterialization.materializeWith (resolveCode package) scenario.world)
      |>.mapError ScenarioPreparationError.worldValidation
  let environment ←
    (EnvironmentMaterialization.materializeWith
      (resolveContract package) scenario.environment)
      |>.mapError ScenarioPreparationError.environmentValidation
  let invocation ←
    (InvocationPreparation.prepare limits limitsValid scenario.invocation
      calldataWithin)
      |>.mapError ScenarioPreparationError.probeValidation
  .ok { package, world, environment, invocation }

end ScenarioPreparation

end Solcore.Oracle.V5
