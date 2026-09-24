import Solcore.Feature

/-! External proof and executable consumers for the draft.5 contract profile. -/

set_option autoImplicit false

namespace Tests

open Solcore

private def expectedFeatures : Array Feature := #[
  .coreProductsV1,
  .coreFunctionsV1,
  .coreSumsV1,
  .coreLocalCellsV1,
  .coreNamedDataV1,
  .coreExtendedWordOperationsV1,
  .checkedContractExecutionV1,
  .staticWordAbiV1
]

private def expectedEnabledFeatures : Array Feature := #[
  .coreUnit,
  .coreBool,
  .coreWord,
  .coreImmutableLet,
  .coreConditional,
  .coreBoolNot,
  .coreWordArithmetic,
  .coreWordComparison,
  .coreWordBitwise
] ++ expectedFeatures

private theorem compileTimeObservationBoundary
    (scope : ProfileScope)
    (runtime : Option ContractRuntimeProfile) :
    ObservationPolicy.checkedCoreStateV1.matchesScope scope runtime = true ↔
      scope = .contract ∧ runtime = none :=
  ObservationPolicy.checkedCoreStateV1_matchesScope_iff scope runtime

private theorem compileTimeProfileValidity : m3aContractProfile.Valid :=
  m3aContractProfile_valid

private theorem compileTimeMatrixCompleteness :
    m3aContractFeatureMatrixIsComplete = true :=
  m3aContractFeatureMatrix_complete

private theorem compileTimeMatrixProfileAgreement :
    m3aContractFeatureMatrixRespectsProfile m3aContractProfile = true :=
  m3aContractFeatureMatrix_respectsProfile

private def featureNamesAreExact : Bool :=
  Lean.toJson Feature.coreProductsV1 == .str "coreProductsV1" &&
  Lean.toJson Feature.coreFunctionsV1 == .str "coreFunctionsV1" &&
  Lean.toJson Feature.coreSumsV1 == .str "coreSumsV1" &&
  Lean.toJson Feature.coreLocalCellsV1 == .str "coreLocalCellsV1" &&
  Lean.toJson Feature.coreNamedDataV1 == .str "coreNamedDataV1" &&
  Lean.toJson Feature.coreExtendedWordOperationsV1 ==
    .str "coreExtendedWordOperationsV1" &&
  Lean.toJson Feature.checkedContractExecutionV1 ==
    .str "checkedContractExecutionV1" &&
  Lean.toJson Feature.staticWordAbiV1 == .str "staticWordAbiV1"

private def profileShapeIsExact : Bool :=
  m3aLanguage.id == "solcore/0.1.0-draft.5" &&
  m3aLanguage.release.prerelease == some "draft.5" &&
  m3aLanguage.grammarVersion.isNone &&
  m3aLanguage.staticSemanticsVersion == some 3 &&
  m3aLanguage.dynamicSemanticsVersion == some 3 &&
  m3aLanguage.abiVersion == some 1 &&
  m3aLanguage.storageLayoutVersion.isNone &&
  m3aLanguage.knownFeatures == Feature.m1cAll ++ expectedFeatures &&
  m3aContractProfile.id == "contract-m3a-v1" &&
  m3aContractProfile.scope == .contract &&
  m3aContractProfile.enabledFeatures == expectedEnabledFeatures &&
  m3aContractProfile.observation == .checkedCoreStateV1 &&
  m3aContractProfile.contractRuntime.isNone &&
  m3aContractProfile.validationErrors.isEmpty

private def matrixShapeIsExact : Bool :=
  m3aContractFeatureMatrix.map (·.feature) == expectedFeatures &&
  m3aContractFeatureMatrix.all fun row =>
    row.specStatus == .normative &&
      row.leanStatus == .implemented &&
      row.adr == some "0151"

private def incompatibleObservationProfilesAreRejected : Bool :=
  let coreScope := { m3aContractProfile with scope := .core }
  let frontendScope := { m3aContractProfile with scope := .frontend }
  let runtime := { evmRevision := EvmRevision.prague }
  let withRuntime := { m3aContractProfile with contractRuntime := some runtime }
  !coreScope.validationErrors.isEmpty &&
    !frontendScope.validationErrors.isEmpty &&
    !withRuntime.validationErrors.isEmpty

private def profileDigestsAreCurrent : Bool :=
  draftCoreProfileDigest ==
      "sha256:b5b8415eba19451d147e4fe9ae35ae2e110891f59cf80ecb70af73a162da3c92" &&
    m1aCoreProfileDigest ==
      "sha256:284ddda1ea6e979648c5ac796f7992058f448c5ce889a9e82a2602d4f012f5d1" &&
    m1cCoreProfileDigest ==
      "sha256:d86d3e11460cc07aec6ea2ed89a48b20c972829eebb5ef61de4580bf5cc88acd"

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

def testProfileM3a : IO Unit := do
  assertTrue featureNamesAreExact
    "the published draft.5 Feature names changed"
  assertTrue profileShapeIsExact
    "the draft.5 language or contract profile changed"
  assertTrue matrixShapeIsExact
    "the v5-only feature matrix changed"
  assertTrue incompatibleObservationProfilesAreRejected
    "checkedCoreStateV1 escaped contract scope without a runtime"
  assertTrue profileDigestsAreCurrent
    "a published profile digest constant is stale"
  let profileText ← IO.FS.readFile
    "profiles/solcore-0.1.0-draft.5-contract-m3a.json"
  let profileJson ←
    match Lean.Json.parse profileText with
    | .ok json => pure json
    | .error error => throw (IO.userError s!"invalid draft.5 profile JSON: {error}")
  assertTrue (profileJson == Lean.toJson m3aContractProfile)
    "the checked-in draft.5 profile differs from the Lean profile"

end Tests
