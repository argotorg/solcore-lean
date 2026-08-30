import Solcore.Oracle.V5.CheckDiagnostic
import Solcore.Oracle.V5.Execution
import Solcore.Oracle.V5.ScenarioDiagnostic
import Solcore.Oracle.V5.TypedPreflight

/-! Total handling after strict Oracle v5 JSON and Core budget decoding. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.TypedHandler

private def responseFor (request : Request) (body : ResponseBody) : Response := {
  id := request.id
  body
}

private def inconclusiveBody
    (query : Query)
    (exhaustion : PreflightExhaustion) : ResponseBody :=
  match query with
  | .capabilities => .capabilities (.inconclusive exhaustion)
  | .coreCheck _ => .coreCheck (.inconclusive exhaustion)
  | .execute _ => .execute (.inconclusive (.preflight exhaustion))

private def coreCheckRejection (diagnostic : Diagnostic) : CoreCheckVerdict :=
  match CoreCheckRejection.of? diagnostic with
  | some rejection => .rejected rejection
  | none => .internalError .oracleResponseInvariant

private def executeRejection (diagnostic : Diagnostic) : ExecuteVerdict :=
  match ExecuteRejection.of? diagnostic with
  | some rejection => .rejected rejection
  | none => .internalError .oracleResponseInvariant

private def handleCoreCheck (program : Solcore.Core.Wire.V3.Program) :
    CoreCheckVerdict :=
  match program.checkDetailed with
  | .ok _ => .accepted { resultType := program.resultType }
  | .error error =>
      match CheckDiagnostic.ofError .coreChecking ["program"] error with
      | .ok diagnostic => coreCheckRejection diagnostic
      | .error internal => .internalError internal

private def executeVerdict
    (target : Solcore.Semantics.Address)
    (fuel : Nat) : ScenarioExecutionResult → ExecuteVerdict
  | .preparationRejected error =>
      match ScenarioDiagnostic.ofPreparationError error with
      | .ok diagnostic => executeRejection diagnostic
      | .error internal => .internalError internal
  | .rootRejected reason =>
      executeRejection (ScenarioDiagnostic.ofRootRejection target reason)
  | .outOfFuel => .inconclusive (.evaluationSteps fuel)
  | .executed observation => .executed observation
  | .internalError error => .internalError error

private def handleExecute
    (limits : Limits)
    (limitsValid : limits.Valid)
    (scenario : Scenario)
    (calldataWithin : scenario.invocation.calldata.size ≤ limits.calldataBytes) :
    ExecuteVerdict :=
  executeVerdict scenario.invocation.target limits.evaluationSteps <|
    Execution.execute limits limitsValid scenario calldataWithin
      limits.evaluationSteps

/--
Handle a fully decoded request. Typed preflight is checked first for every
query; all later branches preserve the request's query/verdict compatibility.
-/
def handle
    (request : Request)
    (limitsValid : request.limits.Valid) : Response :=
  match accepted : TypedPreflight.check request with
  | some exhaustion =>
      responseFor request <|
        inconclusiveBody request.query exhaustion
  | none =>
      match queryEq : request.query with
      | .capabilities =>
          responseFor request (.capabilities (.accepted .canonical))
      | .coreCheck program =>
          responseFor request (.coreCheck (handleCoreCheck program))
      | .execute scenario =>
          have measured :=
            TypedPreflight.calldataBytes_within_of_check_eq_none accepted
          have calldataWithin :
              scenario.invocation.calldata.size ≤
                request.limits.calldataBytes := by
            simpa [Query.calldataBytes, Scenario.calldataBytes, queryEq] using
              measured
          responseFor request <|
            .execute (handleExecute request.limits limitsValid scenario
              calldataWithin)

end Solcore.Oracle.V5.TypedHandler
