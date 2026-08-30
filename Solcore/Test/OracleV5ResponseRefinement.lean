import Solcore.Oracle.V5.Response

/-! Focused regressions for query-refined Oracle v5 response payloads. -/

set_option autoImplicit false

namespace Tests.OracleV5ResponseRefinement

open Solcore.Oracle.V5

private def address : String :=
  "0x0000000000000000000000000000000000000001"

private def word : String :=
  "0x0000000000000000000000000000000000000000000000000000000000000002"

private def coreDiagnostic : Diagnostic := {
  code := "core.check.unbound-variable"
  phase := .coreChecking
  path := ["program"]
  arguments := .mkObj [("index", 1), ("contextSize", 0)]
}

private def coreCheckRejectionExact : Bool :=
  match CoreCheckRejection.of? coreDiagnostic with
  | some accepted =>
      accepted.diagnostic.phase == .coreChecking &&
        (CoreCheckVerdict.rejected accepted).phase == some .coreChecking
  | none => false

private def coreCatalogClosed : Bool := [
  { coreDiagnostic with code := "core.check.future" },
  { coreDiagnostic with phase := .contractAdmission },
  { coreDiagnostic with path := [] },
  { coreDiagnostic with arguments := .mkObj [("index", 1)] }
].all fun diagnostic => (CoreCheckRejection.of? diagnostic).isNone

private def rootDiagnostic : Diagnostic := {
  code := "oracle.v5.root.target-absent"
  phase := .rootInstallation
  path := ["world", "accounts", address]
  arguments := .mkObj [("target", address)]
}

private def executeDiagnostics : List Diagnostic := [
  {
    code := "oracle.v5.contract.invalid-id"
    phase := .contractAdmission
    path := ["contracts", "*", "id"]
    arguments := .mkObj [("actual", "*")]
  },
  {
    code := "oracle.v5.world.duplicate-account"
    phase := .worldValidation
    path := ["world", "accounts", address]
    arguments := .mkObj [("address", address)]
  },
  {
    code := "oracle.v5.environment.duplicate-template-id"
    phase := .environmentValidation
    path := ["environment", "creationTemplates", word]
    arguments := .mkObj [("templateId", word)]
  },
  {
    code := "oracle.v5.probe.duplicate"
    phase := .probeValidation
    path := ["invocation", "probes", "2"]
    arguments := .mkObj [("firstIndex", 0), ("secondIndex", 2)]
  },
  rootDiagnostic
]

private def executeRejectionExact : Bool :=
  executeDiagnostics.all fun diagnostic =>
    executeRejectionPhaseAllowed diagnostic.phase &&
      match ExecuteRejection.of? diagnostic with
      | some accepted =>
          accepted.diagnostic == diagnostic &&
            (ExecuteVerdict.rejected accepted).phase == some diagnostic.phase
      | none => false

private def executeCatalogClosed : Bool :=
  executeRejectionPhaseAllowed rootDiagnostic.phase && [
    { rootDiagnostic with code := "oracle.v5.root.future" },
    { rootDiagnostic with path := ["world", "accounts", word] },
    { rootDiagnostic with arguments := .mkObj [("target", word)] },
    { rootDiagnostic with arguments := .mkObj [] },
    { rootDiagnostic with phase := .worldValidation }
  ].all fun diagnostic => (ExecuteRejection.of? diagnostic).isNone

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

private theorem acceptedCoreValidityProof
    (rejection : CoreCheckRejection) :
    rejection.diagnostic.ValidCoreCheck :=
  rejection.valid

private theorem acceptedExecuteValidityProof
    (rejection : ExecuteRejection) :
    rejection.diagnostic.ValidExecute :=
  rejection.valid

private def allChecks : Bool :=
  coreCheckRejectionExact && coreCatalogClosed && executeRejectionExact &&
    executeCatalogClosed && preflightVerdictsExact

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5ResponseRefinement : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 response refinements changed")

end Tests.OracleV5ResponseRefinement
