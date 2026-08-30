import Solcore.Oracle.V5.Observation
import Solcore.Oracle.V5.RootInstallation
import Solcore.Oracle.V5.ScenarioPreparation
import Solcore.Semantics.BalancedTopLevelExecution

/-! End-to-end typed execution of one decoded Oracle v5 scenario. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5

open Solcore.Semantics

/-- A fully prepared scenario whose selected root is proved installed. -/
structure ReadyExecution where
  prepared : PreparedScenario
  root : InstalledRoot prepared.package prepared.world
    prepared.invocation.invocation.target

/-- Closed total result before response-diagnostic projection. -/
inductive ScenarioExecutionResult where
  | preparationRejected (error : ScenarioPreparationError)
  | rootRejected (reason : RootInstallationRejection)
  | outOfFuel
  | executed (observation : ExecutionObservation)
  | internalError (error : InternalError)

namespace Execution

private def runReady
    (ready : ReadyExecution)
    (fuel : Nat) : ExecutionProjection :=
  let invocation := ready.prepared.invocation.invocation
  let balanced :=
    BalancedTopLevelExecution.runWithEnvironment ready.root.contract invocation
      ready.root.installed ready.prepared.environment fuel
  ExecutionProjection.ofBalancedResult
    ready.prepared.package.codeIdResolver
    ready.prepared.invocation.probes.values balanced

/--
Execute exactly once after deterministic preparation. Return commits the
working endpoint; rejection, revert, and trap observe the checkpoint; fuel
exhaustion remains a distinct total result without fabricated observations.
-/
def execute
    (limits : Limits)
    (limitsValid : limits.Valid)
    (scenario : Scenario)
    (calldataWithin : scenario.invocation.calldata.size ≤ limits.calldataBytes)
    (fuel : Nat) : ScenarioExecutionResult :=
  match ScenarioPreparation.prepare limits limitsValid scenario calldataWithin with
  | .error error => .preparationRejected error
  | .ok prepared =>
      match RootInstallation.install prepared.package prepared.world
          prepared.invocation.invocation.target with
      | .rejected reason => .rootRejected reason
      | .internalError error => .internalError error
      | .installed root =>
          match runReady { prepared, root } fuel with
          | .outOfFuel => .outOfFuel
          | .internalError error => .internalError error
          | .executed observation => .executed observation

end Execution

end Solcore.Oracle.V5
