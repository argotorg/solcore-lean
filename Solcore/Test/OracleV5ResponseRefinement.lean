import Solcore.Oracle.V5.Response

/-! Focused regressions for query-refined Oracle v5 response payloads. -/

set_option autoImplicit false

namespace Tests.OracleV5ResponseRefinement

open Solcore.Oracle.V5

private def diagnostic (phase : Phase) : Diagnostic := {
  code := "test"
  phase
  path := []
  arguments := .mkObj []
}

private def coreCheckRejectionExact : Bool :=
  match CoreCheckRejection.of? (diagnostic .coreChecking),
      CoreCheckRejection.of? (diagnostic .contractAdmission) with
  | some accepted, none =>
      accepted.diagnostic.phase == .coreChecking &&
        (CoreCheckVerdict.rejected accepted).phase == some .coreChecking
  | _, _ => false

private def executeAllowedPhases : List Phase := [
  .contractAdmission,
  .worldValidation,
  .environmentValidation,
  .probeValidation,
  .rootInstallation
]

private def executeDeniedPhases : List Phase := [
  .protocol,
  .requestPreflight,
  .coreDecoding,
  .coreChecking,
  .contractExecution,
  .observationEncoding
]

private def executeRejectionExact : Bool :=
  executeAllowedPhases.all fun phase =>
    executeRejectionPhaseAllowed phase &&
      match ExecuteRejection.of? (diagnostic phase) with
      | some accepted =>
          accepted.diagnostic.phase == phase &&
            (ExecuteVerdict.rejected accepted).phase == some phase
      | none => false

private def executeDeniedExact : Bool :=
  executeDeniedPhases.all fun phase =>
    !executeRejectionPhaseAllowed phase &&
      (ExecuteRejection.of? (diagnostic phase)).isNone

private def preflight : PreflightExhaustion :=
  ⟨.jsonDepth, 1, 2, by decide⟩

private def preflightVerdictsExact : Bool :=
  (CapabilitiesVerdict.inconclusive preflight).phase ==
      some .requestPreflight &&
    (CoreCheckVerdict.inconclusive preflight).phase ==
      some .requestPreflight &&
    (ExecuteVerdict.inconclusive (.preflight preflight)).phase ==
      some .requestPreflight &&
    (ExecuteVerdict.inconclusive (.evaluationSteps 12)).phase ==
      some .contractExecution

private theorem acceptedCorePhaseProof
    (rejection : CoreCheckRejection) :
    rejection.diagnostic.phase = .coreChecking :=
  rejection.phase_eq

private theorem acceptedExecutePhaseProof
    (rejection : ExecuteRejection) :
    ExecuteRejectionPhaseAllowed rejection.diagnostic.phase :=
  rejection.phase_allowed

private def allChecks : Bool :=
  coreCheckRejectionExact && executeRejectionExact && executeDeniedExact &&
    preflightVerdictsExact

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5ResponseRefinement : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 response refinements changed")

end Tests.OracleV5ResponseRefinement
