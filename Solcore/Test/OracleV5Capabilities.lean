import Solcore.Oracle.V5.Capabilities

/-! Executable identity tests for the singleton Oracle v5 capability report. -/

set_option autoImplicit false

namespace Tests.OracleV5Capabilities

open Solcore.Oracle.V5

private def allChecks : Bool :=
  capabilityReport.schema == capabilitiesSchema &&
    capabilityReport.spec == Solcore.m3aLanguage.id &&
    capabilityReport.profile == Solcore.m3aContractProfile &&
    capabilityReport.profileDigest == Solcore.m3aContractProfileDigest &&
    capabilityReport.coreSchema == Solcore.Core.Wire.V3.schemaVersion &&
    capabilityReport.checkResultSchema == checkResultSchema &&
    capabilityReport.executionSchema == executionSchema &&
    capabilityReport.stateObservationSchema == stateObservationSchema &&
    capabilityReport.contractProfiles == #["returnWord", "wordOutcomeV1"] &&
    capabilityReport.abiProfiles == #["staticWordAbiV1"] &&
    capabilityReport.implementedQueries ==
      #[.capabilities, .coreCheck, .execute] &&
    capabilityReport.maxNestedCallDepth == 1 &&
    capabilityReport.observationKinds ==
      #["accountPresence", "storage", "balance", "nonce", "code"] &&
    capabilityReport.defaultLimits == Limits.default &&
    capabilityReport.baselines == Solcore.implementationBaselines &&
    capabilityReport.features == Solcore.m3aContractFeatureMatrix

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5Capabilities : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 capability report changed")

end Tests.OracleV5Capabilities
