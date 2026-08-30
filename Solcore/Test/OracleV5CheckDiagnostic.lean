import Solcore.Oracle.V5.CheckDiagnostic

/-! Executable coverage for the closed Oracle v5 checker diagnostic map. -/

set_option autoImplicit false

namespace Tests.OracleV5CheckDiagnostic

open Solcore.Core
open Solcore.Oracle.V5

private def dataType : DataTypeId := ⟨2⟩
private def constructor : ConstructorId := { owner := dataType, index := 3 }

private def allData : List CheckErrorData :=
  [.unboundVariable 1 2,
    .expectedBool .word,
    .expectedProduct .unit,
    .expectedFunction .bool,
    .functionArgumentTypeMismatch .word .bool,
    .lambdaResultTypeMismatch .word .unit,
    .expectedSum .word,
    .caseBranchTypeMismatch .word .bool,
    .invalidCellPayload (.function .word .word),
    .cellInitializerTypeMismatch .word .unit,
    .expectedCell .word,
    .cellValueTypeMismatch .word .bool,
    .invalidDefinitionPayload 1 2 (.cell .word),
    .unknownNamedDataType dataType,
    .unknownDataType dataType,
    .unknownConstructor constructor,
    .constructorPayloadTypeMismatch .word .unit,
    .expectedNamedData .word,
    .matchDataTypeMismatch dataType ⟨3⟩,
    .matchBranchCountMismatch 1 2,
    .matchBranchResultTypeMismatch 3 .word .bool,
    .invalidResultType .word,
    .primitiveOperandTypeMismatch .word .bool,
    .branchTypeMismatch .word .unit,
    .declaredResultTypeMismatch .word .bool,
    .inferenceFailure]

private def everyConstructorProjects : Bool :=
  allData.all fun data =>
    match CheckDiagnostic.arguments data with
    | .ok _ => true
    | .error _ => false

private def representative : CheckError := {
  path := [.matchBranch 3, .binaryLeft]
  data := .functionArgumentTypeMismatch .word .bool
}

private def representativeExact : Bool :=
  match CheckDiagnostic.ofError .contractAdmission
      ["contracts", "root", "program"] representative with
  | .error _ => false
  | .ok diagnostic =>
      diagnostic.code == "core.check.function-argument-type-mismatch" &&
        diagnostic.phase == .contractAdmission &&
        diagnostic.path ==
          ["contracts", "root", "program", "matchBranch[3]", "binaryLeft"] &&
        diagnostic.arguments == .mkObj [
          ("expected", .str "word"),
          ("actual", .str "bool")
        ] &&
        diagnostic.severity == "error" && diagnostic.display.isNone

private def namedIdentitiesExact : Bool :=
  match CheckDiagnostic.arguments (.unknownConstructor constructor) with
  | .error _ => false
  | .ok arguments => arguments == .mkObj [
      ("constructor", .mkObj [
        ("owner", Lean.toJson 2),
        ("index", Lean.toJson 3)
      ])
    ]

private def allChecks : Bool :=
  everyConstructorProjects && representativeExact && namedIdentitiesExact

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5CheckDiagnostic : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 Core checker diagnostic projection changed")

end Tests.OracleV5CheckDiagnostic
