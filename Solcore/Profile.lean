import Lean.Data.Json
import Solcore.Foundation.Hash

set_option autoImplicit false

namespace Solcore

inductive EvmRevision where
  | prague
  | osaka
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

inductive Feature where
  | corePrimitives
  | functions
  | lambdas
  | localBindings
  | localMutation
  | conditionals
  | products
  | sumTypes
  | userAdts
  | patternMatching
  | modules
  | polymorphism
  | typeClasses
  | comptime
  | contracts
  | externalAbi
  | storage
  | storageArrays
  | inlineYul
  | coreUnit
  | coreBool
  | coreWord
  | coreImmutableLet
  | coreConditional
  | coreBoolNot
  | coreWordArithmetic
  | coreWordComparison
  | coreWordBitwise
  | surfaceGrammar
  | coreProductsV1
  | coreFunctionsV1
  | coreSumsV1
  | coreLocalCellsV1
  | coreNamedDataV1
  | coreExtendedWordOperationsV1
  | checkedContractExecutionV1
  | staticWordAbiV1
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

inductive SpecMaturity where
  | directionAccepted
  | normative
  | proposed
  | deferred
  | unsupported
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

namespace Feature

def legacyAll : Array Feature := #[
  .corePrimitives,
  .functions,
  .lambdas,
  .localBindings,
  .localMutation,
  .conditionals,
  .products,
  .sumTypes,
  .userAdts,
  .patternMatching,
  .modules,
  .polymorphism,
  .typeClasses,
  .comptime,
  .contracts,
  .externalAbi,
  .storage,
  .storageArrays,
  .inlineYul
]

def m1aAll : Array Feature :=
  legacyAll ++ #[
    .coreUnit,
    .coreBool,
    .coreWord,
    .coreImmutableLet,
    .coreConditional
  ]

def m1cAll : Array Feature :=
  m1aAll ++ #[
    .coreBoolNot,
    .coreWordArithmetic,
    .coreWordComparison,
    .coreWordBitwise
  ]

def m2bAll : Array Feature :=
  m1cAll ++ #[
    .surfaceGrammar
  ]

def m3aAll : Array Feature :=
  m2bAll ++ #[
    .coreProductsV1,
    .coreFunctionsV1,
    .coreSumsV1,
    .coreLocalCellsV1,
    .coreNamedDataV1,
    .coreExtendedWordOperationsV1,
    .checkedContractExecutionV1,
    .staticWordAbiV1
  ]

def all : Array Feature := m3aAll

def specMaturity : Feature → SpecMaturity
  | .coreUnit
  | .coreBool
  | .coreWord
  | .coreImmutableLet
  | .coreConditional
  | .coreBoolNot
  | .coreWordArithmetic
  | .coreWordComparison
  | .coreWordBitwise
  | .surfaceGrammar
  | .coreProductsV1
  | .coreFunctionsV1
  | .coreSumsV1
  | .coreLocalCellsV1
  | .coreNamedDataV1
  | .coreExtendedWordOperationsV1
  | .checkedContractExecutionV1
  | .staticWordAbiV1 => .normative
  | .corePrimitives
  | .functions
  | .lambdas
  | .localBindings
  | .localMutation
  | .conditionals
  | .products
  | .sumTypes
  | .userAdts
  | .patternMatching
  | .polymorphism
  | .typeClasses
  | .contracts
  | .externalAbi => .directionAccepted
  | .modules
  | .comptime
  | .storageArrays => .proposed
  | .storage
  | .inlineYul => .deferred

end Feature

inductive ProfileScope where
  | frontend
  | core
  | contract
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

inductive SolverPolicy where
  | tabled
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

inductive ObservationPolicy where
  | staticVerdictV1
  | valueV1
  | evmStateV1
  | evmStateWithGasV1
  | checkedCoreStateV1
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

inductive SpanUnit where
  | utf8Byte
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

structure SemVer where
  major : Nat
  minor : Nat
  patch : Nat
  prerelease : Option String := none
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

structure StdFileDigest where
  path : String
  byteSize : Nat
  sha256 : String
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

structure StdBundle where
  sourceRevision : String
  manifestAlgorithm : String
  manifestSha256 : String
  files : Array StdFileDigest
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

structure LanguageVersion where
  id : String
  release : SemVer
  grammarVersion : Option Nat
  staticSemanticsVersion : Option Nat
  dynamicSemanticsVersion : Option Nat
  abiVersion : Option Nat
  storageLayoutVersion : Option Nat
  standardLibrary : StdBundle
  knownFeatures : Array Feature
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

structure ContractRuntimeProfile where
  evmRevision : EvmRevision
  gasSchedule : Option String := none
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

structure SpecProfile where
  id : String
  language : LanguageVersion
  scope : ProfileScope
  enabledFeatures : Array Feature
  solver : SolverPolicy
  observation : ObservationPolicy
  contractRuntime : Option ContractRuntimeProfile
  spanUnit : SpanUnit
  sourceEncoding : String
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

private def hasDuplicates {α : Type} [BEq α] : List α → Bool
  | [] => false
  | item :: rest => rest.contains item || hasDuplicates rest

def ObservationPolicy.matchesScope
    (observation : ObservationPolicy)
    (scope : ProfileScope)
    (runtime : Option ContractRuntimeProfile) : Bool :=
  match scope, observation, runtime with
  | .frontend, .staticVerdictV1, none => true
  | .core, .staticVerdictV1, none => true
  | .core, .valueV1, none => true
  | .contract, .checkedCoreStateV1, none => true
  | .contract, .evmStateV1, some _ => true
  | .contract, .evmStateWithGasV1, some runtime => runtime.gasSchedule.isSome
  | _, _, _ => false

theorem ObservationPolicy.checkedCoreStateV1_matchesScope_iff
    (scope : ProfileScope)
    (runtime : Option ContractRuntimeProfile) :
    ObservationPolicy.checkedCoreStateV1.matchesScope scope runtime = true ↔
      scope = .contract ∧ runtime = none := by
  cases scope <;> cases runtime <;> simp [ObservationPolicy.matchesScope]

def StdFileDigest.validationErrors (file : StdFileDigest) : List String :=
  let pathErrors :=
    if file.path.isEmpty || !file.path.endsWith ".solc" then
      ["standard-library path must be a relative .solc path"]
    else
      []
  let digestErrors :=
    if Foundation.isSha256 file.sha256 then
      []
    else
      ["standard-library file SHA-256 must be 64 lowercase hexadecimal digits"]
  pathErrors ++ digestErrors

def StdBundle.validationErrors (bundle : StdBundle) : List String :=
  let revisionErrors :=
    if Foundation.isGitCommit bundle.sourceRevision then
      []
    else
      ["standard-library source revision must be a 40-digit Git commit"]
  let manifestErrors :=
    if bundle.manifestAlgorithm == "solcore-fileset-sha256-v1" &&
        Foundation.isSha256 bundle.manifestSha256 then
      []
    else
      ["standard-library manifest algorithm or digest is invalid"]
  let duplicateErrors :=
    if hasDuplicates (bundle.files.toList.map (·.path)) then
      ["standard-library paths must be unique"]
    else
      []
  revisionErrors ++ manifestErrors ++ duplicateErrors ++
    bundle.files.toList.flatMap StdFileDigest.validationErrors

def SpecProfile.validationErrors (profile : SpecProfile) : List String :=
  let identityErrors :=
    (if profile.id.isEmpty then ["profile id must not be empty"] else []) ++
    (if profile.language.id.isEmpty then ["language version id must not be empty"] else [])
  let featureErrors :=
    (if hasDuplicates profile.language.knownFeatures.toList then
      ["known features must be unique"]
    else
      []) ++
    (if hasDuplicates profile.enabledFeatures.toList then
      ["enabled features must be unique"]
    else
      []) ++
    (if profile.enabledFeatures.all profile.language.knownFeatures.contains then
      []
    else
      ["enabled features must be a subset of known features"]) ++
    (if profile.enabledFeatures.all fun feature =>
        feature.specMaturity == .normative then
      []
    else
      ["enabled features must have complete normative specifications"])
  let scopeErrors :=
    if profile.observation.matchesScope profile.scope profile.contractRuntime then
      []
    else
      ["observation policy is incompatible with profile scope"]
  let encodingErrors :=
    if profile.sourceEncoding == "UTF-8" then
      []
    else
      ["source encoding must be UTF-8"]
  identityErrors ++ featureErrors ++ scopeErrors ++ encodingErrors ++
    profile.language.standardLibrary.validationErrors

def SpecProfile.Valid (profile : SpecProfile) : Prop :=
  profile.validationErrors = []

def canonicalStd : StdBundle := {
  sourceRevision := "1d490d8bb5f374356f06e0720655496482eb1fb4"
  manifestAlgorithm := "solcore-fileset-sha256-v1"
  manifestSha256 := "3f81bebfd1fc161ee08972be9e7a52150d02bdf55dd7449dfa058cd81cfafc22"
  files := #[
    {
      path := "ABIGeneric.solc"
      byteSize := 5540
      sha256 := "b14f31abd374d65e194c7706183086082558ab2a60d230ec5b9e6f1b9c9b9ae2"
    },
    {
      path := "Generic.solc"
      byteSize := 445
      sha256 := "913a02e32829e0230e31db6512151c36e019f5630e3dbd0be9d033a9019194d7"
    },
    {
      path := "StorageGeneric.solc"
      byteSize := 10546
      sha256 := "8d68601447f40a6e662de8b6cff06031998628339ca23ec917a970157c301a6a"
    },
    {
      path := "dispatch.solc"
      byteSize := 11249
      sha256 := "b723ec9a0a76a6abf091d49a12467c6a4628b634c48d8c34e82e2c45d6e939f5"
    },
    {
      path := "opcodes.solc"
      byteSize := 10377
      sha256 := "a6a08beed16ccdf722f65c60af835dcfd0eaec61f34f041082bbc0fca1e69bab"
    },
    {
      path := "std.solc"
      byteSize := 72958
      sha256 := "e8ec755232347bbf4a130dcc05c7c5a3230c4d0cb0223445a2d82260d4474fec"
    }
  ]
}

def draftLanguage : LanguageVersion := {
  id := "solcore/0.1.0-draft.1"
  release := {
    major := 0
    minor := 1
    patch := 0
    prerelease := some "draft.1"
  }
  grammarVersion := none
  staticSemanticsVersion := none
  dynamicSemanticsVersion := none
  abiVersion := none
  storageLayoutVersion := none
  standardLibrary := canonicalStd
  knownFeatures := Feature.legacyAll
}

def draftCoreProfile : SpecProfile := {
  id := "core-v1"
  language := draftLanguage
  scope := .core
  enabledFeatures := #[]
  solver := .tabled
  observation := .valueV1
  contractRuntime := none
  spanUnit := .utf8Byte
  sourceEncoding := "UTF-8"
}

def draftCoreProfileDigest : String :=
  "sha256:2ccae018d736fa61910a6c2475fe3088bad2e924b60d43a9748852b7cc817ec8"

theorem draftCoreProfile_valid : draftCoreProfile.Valid := by
  change draftCoreProfile.validationErrors = []
  native_decide

def m1aLanguage : LanguageVersion := {
  id := "solcore/0.1.0-draft.2"
  release := {
    major := 0
    minor := 1
    patch := 0
    prerelease := some "draft.2"
  }
  grammarVersion := none
  staticSemanticsVersion := some 1
  dynamicSemanticsVersion := some 1
  abiVersion := none
  storageLayoutVersion := none
  standardLibrary := canonicalStd
  knownFeatures := Feature.m1aAll
}

def m1aCoreProfile : SpecProfile := {
  id := "core-m1a-v1"
  language := m1aLanguage
  scope := .core
  enabledFeatures := #[
    .coreUnit,
    .coreBool,
    .coreWord,
    .coreImmutableLet,
    .coreConditional
  ]
  solver := .tabled
  observation := .valueV1
  contractRuntime := none
  spanUnit := .utf8Byte
  sourceEncoding := "UTF-8"
}

def m1aCoreProfileDigest : String :=
  "sha256:3645c44ee266496e6ae13e33971d34c6836dee105a543e6805e5dd8b674ff867"

theorem m1aCoreProfile_valid : m1aCoreProfile.Valid := by
  change m1aCoreProfile.validationErrors = []
  native_decide

def m1cLanguage : LanguageVersion := {
  id := "solcore/0.1.0-draft.3"
  release := {
    major := 0
    minor := 1
    patch := 0
    prerelease := some "draft.3"
  }
  grammarVersion := none
  staticSemanticsVersion := some 2
  dynamicSemanticsVersion := some 2
  abiVersion := none
  storageLayoutVersion := none
  standardLibrary := canonicalStd
  knownFeatures := Feature.m1cAll
}

def m1cCoreProfile : SpecProfile := {
  id := "core-m1c-v1"
  language := m1cLanguage
  scope := .core
  enabledFeatures := #[
    .coreUnit,
    .coreBool,
    .coreWord,
    .coreImmutableLet,
    .coreConditional,
    .coreBoolNot,
    .coreWordArithmetic,
    .coreWordComparison,
    .coreWordBitwise
  ]
  solver := .tabled
  observation := .valueV1
  contractRuntime := none
  spanUnit := .utf8Byte
  sourceEncoding := "UTF-8"
}

def m1cCoreProfileDigest : String :=
  "sha256:111ad60f90a5dca6eaafa582475b6582d081bc081ee59766d6040173061f2693"

theorem m1cCoreProfile_valid : m1cCoreProfile.Valid := by
  change m1cCoreProfile.validationErrors = []
  native_decide

def m2bLanguage : LanguageVersion := {
  id := "solcore/0.1.0-draft.4"
  release := {
    major := 0
    minor := 1
    patch := 0
    prerelease := some "draft.4"
  }
  grammarVersion := some 1
  staticSemanticsVersion := some 2
  dynamicSemanticsVersion := some 2
  abiVersion := none
  storageLayoutVersion := none
  standardLibrary := canonicalStd
  knownFeatures := Feature.m2bAll
}

def m2bFrontendProfile : SpecProfile := {
  id := "frontend-m2b-v1"
  language := m2bLanguage
  scope := .frontend
  enabledFeatures := #[.surfaceGrammar]
  solver := .tabled
  observation := .staticVerdictV1
  contractRuntime := none
  spanUnit := .utf8Byte
  sourceEncoding := "UTF-8"
}

def m2bFrontendProfileDigest : String :=
  "sha256:292e8c423bfc2d7e77f7a9756e743af473f6a952073e590c62a05c676e3bf33a"

theorem m2bFrontendProfile_valid : m2bFrontendProfile.Valid := by
  change m2bFrontendProfile.validationErrors = []
  native_decide

def m3aLanguage : LanguageVersion := {
  id := "solcore/0.1.0-draft.5"
  release := {
    major := 0
    minor := 1
    patch := 0
    prerelease := some "draft.5"
  }
  grammarVersion := none
  staticSemanticsVersion := some 3
  dynamicSemanticsVersion := some 3
  abiVersion := some 1
  storageLayoutVersion := none
  standardLibrary := canonicalStd
  knownFeatures := Feature.m3aAll
}

def m3aContractProfile : SpecProfile := {
  id := "contract-m3a-v1"
  language := m3aLanguage
  scope := .contract
  enabledFeatures := #[
    .coreProductsV1,
    .coreFunctionsV1,
    .coreSumsV1,
    .coreLocalCellsV1,
    .coreNamedDataV1,
    .coreExtendedWordOperationsV1,
    .checkedContractExecutionV1,
    .staticWordAbiV1
  ]
  solver := .tabled
  observation := .checkedCoreStateV1
  contractRuntime := none
  spanUnit := .utf8Byte
  sourceEncoding := "UTF-8"
}

def m3aContractProfileDigest : String :=
  "sha256:615de959ac8cb6c7e9b91fe6b45ec578a7143d5f74ec092316901cf76431cf46"

theorem m3aContractProfile_valid : m3aContractProfile.Valid := by
  change m3aContractProfile.validationErrors = []
  native_decide

end Solcore
