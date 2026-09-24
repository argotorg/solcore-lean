import Solcore.Profile

set_option autoImplicit false

namespace Solcore

inductive ImplementationStatus where
  | implemented
  | partialSupport
  | planned
  | blocked
  | unsupported
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

structure FeatureRow where
  feature : Feature
  specStatus : SpecMaturity
  leanTarget : String
  leanStatus : ImplementationStatus
  adr : Option String
  note : String
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

def featureMatrix : Array FeatureRow := #[
  ⟨.corePrimitives, .directionAccepted, "M1", .partialSupport, some "0009",
    "M1a implements unit/bool/word literals; primitive operations remain."⟩,
  ⟨.functions, .directionAccepted, "M1", .planned, some "0002", "First-class invokable functions."⟩,
  ⟨.lambdas, .directionAccepted, "M1", .planned, some "0002", "Lexical closures."⟩,
  ⟨.localBindings, .directionAccepted, "M1", .partialSupport, some "0009",
    "M1a implements initialized immutable de Bruijn bindings."⟩,
  ⟨.localMutation, .directionAccepted, "M1", .planned, some "0002", "Mutable local cells."⟩,
  ⟨.conditionals, .directionAccepted, "M1", .partialSupport, some "0009",
    "M1a evaluates the condition and only the selected branch."⟩,
  ⟨.products, .directionAccepted, "M1", .planned, some "0002", "Tuple/product values."⟩,
  ⟨.sumTypes, .directionAccepted, "M1", .planned, some "0002", "Sum-type values."⟩,
  ⟨.userAdts, .directionAccepted, "M1", .planned, some "0002", "User-defined algebraic data types."⟩,
  ⟨.patternMatching, .directionAccepted, "M1", .planned, some "0002", "Pattern matching over values."⟩,
  ⟨.modules, .proposed, "M2", .blocked, none, "Blocked on import and shadowing rules."⟩,
  ⟨.polymorphism, .directionAccepted, "M2", .planned, some "0002", "Explicit and inferred polymorphism."⟩,
  ⟨.typeClasses, .directionAccepted, "M2", .planned, some "0004", "Canonical tabled resolution."⟩,
  ⟨.comptime, .proposed, "M2", .blocked, none, "Blocked on the comptime/runtime boundary."⟩,
  ⟨.contracts, .directionAccepted, "M3", .planned, some "0005", "Contract entry and transactions."⟩,
  ⟨.externalAbi, .directionAccepted, "M3", .blocked, some "0006", "Structured unsupported cases remain."⟩,
  ⟨.storage, .deferred, "M3", .blocked, some "0008", "Storage rules require a layout ADR."⟩,
  ⟨.storageArrays, .proposed, "M3", .blocked, some "0008", "Storage-array semantics remain to be specified."⟩,
  ⟨.inlineYul, .deferred, "M4", .unsupported, some "0002", "Specified as a lowering boundary."⟩
]

def m1aFeatureMatrix : Array FeatureRow :=
  featureMatrix ++ #[
    ⟨.coreUnit, .normative, "M1b", .implemented, some "0010",
      "Unit type, literal, value, typing, and evaluation are normative."⟩,
    ⟨.coreBool, .normative, "M1b", .implemented, some "0010",
      "Boolean type, literals, values, typing, and evaluation are normative."⟩,
    ⟨.coreWord, .normative, "M1b", .implemented, some "0010",
      "Range-checked 256-bit word type, literals, values, typing, and evaluation are normative."⟩,
    ⟨.coreImmutableLet, .normative, "M1b", .implemented, some "0010",
      "Initialized immutable de Bruijn bindings are normative."⟩,
    ⟨.coreConditional, .normative, "M1b", .implemented, some "0010",
      "Condition-first, selected-branch-only Core conditionals are normative."⟩
  ]

def m1cFeatureMatrix : Array FeatureRow :=
  (m1aFeatureMatrix.map fun row =>
    if row.feature == .corePrimitives then
      { row with
        note :=
          "M1c implements the normative bool-not and word-operation subset; " ++
          "the aggregate remains partial."
      }
    else
      row) ++ #[
    ⟨.coreBoolNot, .normative, "M1c", .implemented, some "0011",
      "Boolean negation is normative."⟩,
    ⟨.coreWordArithmetic, .normative, "M1c", .implemented, some "0011",
      "Modular add/subtract/multiply and total unsigned divide/modulo are normative."⟩,
    ⟨.coreWordComparison, .normative, "M1c", .implemented, some "0011",
      "Unsigned word equality and greater-than are normative."⟩,
    ⟨.coreWordBitwise, .normative, "M1c", .implemented, some "0011",
      "Fixed-width word bitwise operations and bounded logical shifts are normative."⟩
  ]

def m3aContractFeatureMatrix : Array FeatureRow := #[
  ⟨.coreProductsV1, .normative, "M3a", .implemented, some "0151",
    "Checked Core products and projections are published by Core Wire v3."⟩,
  ⟨.coreFunctionsV1, .normative, "M3a", .implemented, some "0151",
    "Checked Core lambdas, application, and lexical closures are published."⟩,
  ⟨.coreSumsV1, .normative, "M3a", .implemented, some "0151",
    "Checked Core sums, injections, and case analysis are published."⟩,
  ⟨.coreLocalCellsV1, .normative, "M3a", .implemented, some "0151",
    "Checked Core local cell allocation, reads, and writes are published."⟩,
  ⟨.coreNamedDataV1, .normative, "M3a", .implemented, some "0151",
    "Checked named data construction and matching are published."⟩,
  ⟨.coreExtendedWordOperationsV1, .normative, "M3a", .implemented, some "0151",
    "The complete current checked Word operator algebra is published."⟩,
  ⟨.checkedContractExecutionV1, .normative, "M3a", .implemented, some "0151",
    "Checked contracts execute through the balanced state lifecycle."⟩,
  ⟨.staticWordAbiV1, .normative, "M3a", .implemented, some "0151",
    "Static uint256-to-uint256 ABI dispatch is published."⟩
]

private def hasDuplicates {α : Type} [BEq α] : List α → Bool
  | [] => false
  | item :: rest => rest.contains item || hasDuplicates rest

def featureMatrixIsComplete : Bool :=
  let features := featureMatrix.toList.map (·.feature)
  !hasDuplicates features &&
    Feature.legacyAll.all features.contains &&
    features.all Feature.legacyAll.contains &&
    featureMatrix.all fun row => row.specStatus == row.feature.specMaturity

def m1aFeatureMatrixIsComplete : Bool :=
  let features := m1aFeatureMatrix.toList.map (·.feature)
  !hasDuplicates features &&
    Feature.m1aAll.all features.contains &&
    features.all Feature.m1aAll.contains &&
    m1aFeatureMatrix.all fun row => row.specStatus == row.feature.specMaturity

def m1cFeatureMatrixIsComplete : Bool :=
  let features := m1cFeatureMatrix.toList.map (·.feature)
  !hasDuplicates features &&
    Feature.m1cAll.all features.contains &&
    features.all Feature.m1cAll.contains &&
    m1cFeatureMatrix.all fun row => row.specStatus == row.feature.specMaturity

def m3aContractFeatureMatrixIsComplete : Bool :=
  let expected := #[
    .coreProductsV1,
    .coreFunctionsV1,
    .coreSumsV1,
    .coreLocalCellsV1,
    .coreNamedDataV1,
    .coreExtendedWordOperationsV1,
    .checkedContractExecutionV1,
    .staticWordAbiV1
  ]
  let features := m3aContractFeatureMatrix.toList.map (·.feature)
  !hasDuplicates features &&
    expected.all features.contains &&
    features.all expected.contains &&
    m3aContractFeatureMatrix.all fun row =>
      row.specStatus == row.feature.specMaturity

def rowsRespectProfile (rows : Array FeatureRow) (profile : SpecProfile) : Bool :=
  rows.all fun row =>
    if row.leanStatus == .implemented then
      row.specStatus == .normative && profile.enabledFeatures.contains row.feature
    else
      true

def featureMatrixRespectsProfile (profile : SpecProfile) : Bool :=
  rowsRespectProfile featureMatrix profile

def m1aFeatureMatrixRespectsProfile (profile : SpecProfile) : Bool :=
  rowsRespectProfile m1aFeatureMatrix profile

def m1cFeatureMatrixRespectsProfile (profile : SpecProfile) : Bool :=
  rowsRespectProfile m1cFeatureMatrix profile

def m3aContractFeatureMatrixRespectsProfile (profile : SpecProfile) : Bool :=
  rowsRespectProfile m3aContractFeatureMatrix profile

theorem featureMatrix_complete : featureMatrixIsComplete = true := by
  native_decide

theorem draftFeatureMatrix_respectsProfile :
    featureMatrixRespectsProfile draftCoreProfile = true := by
  native_decide

theorem m1aFeatureMatrix_complete : m1aFeatureMatrixIsComplete = true := by
  native_decide

theorem m1aFeatureMatrix_respectsProfile :
    m1aFeatureMatrixRespectsProfile m1aCoreProfile = true := by
  native_decide

theorem m1cFeatureMatrix_complete : m1cFeatureMatrixIsComplete = true := by
  native_decide

theorem m1cFeatureMatrix_respectsProfile :
    m1cFeatureMatrixRespectsProfile m1cCoreProfile = true := by
  native_decide

theorem m3aContractFeatureMatrix_complete :
    m3aContractFeatureMatrixIsComplete = true := by
  native_decide

theorem m3aContractFeatureMatrix_respectsProfile :
    m3aContractFeatureMatrixRespectsProfile m3aContractProfile = true := by
  native_decide

end Solcore
