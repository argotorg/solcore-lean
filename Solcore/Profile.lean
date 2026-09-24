import Lean.Data.Json

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

def m3aAll : Array Feature :=
  m1cAll ++ #[
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

structure LanguageVersion where
  id : String
  release : SemVer
  grammarVersion : Option Nat
  staticSemanticsVersion : Option Nat
  dynamicSemanticsVersion : Option Nat
  abiVersion : Option Nat
  storageLayoutVersion : Option Nat
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
  identityErrors ++ featureErrors ++ scopeErrors ++ encodingErrors

def SpecProfile.Valid (profile : SpecProfile) : Prop :=
  profile.validationErrors = []

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
  "sha256:b5b8415eba19451d147e4fe9ae35ae2e110891f59cf80ecb70af73a162da3c92"

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
  "sha256:284ddda1ea6e979648c5ac796f7992058f448c5ce889a9e82a2602d4f012f5d1"

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
  "sha256:d86d3e11460cc07aec6ea2ed89a48b20c972829eebb5ef61de4580bf5cc88acd"

theorem m1cCoreProfile_valid : m1cCoreProfile.Valid := by
  change m1cCoreProfile.validationErrors = []
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
  knownFeatures := Feature.m3aAll
}

def m3aContractProfile : SpecProfile := {
  id := "contract-m3a-v1"
  language := m3aLanguage
  scope := .contract
  enabledFeatures := #[
    .coreUnit,
    .coreBool,
    .coreWord,
    .coreImmutableLet,
    .coreConditional,
    .coreBoolNot,
    .coreWordArithmetic,
    .coreWordComparison,
    .coreWordBitwise,
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
  "sha256:b01693cbb3f0598a1aabc516c48c54d78f37fe0e75359504a48dde30858492a9"

theorem m3aContractProfile_valid : m3aContractProfile.Valid := by
  change m3aContractProfile.validationErrors = []
  native_decide

end Solcore
