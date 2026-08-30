import Solcore.Core.Wire.V3.Codec
import Solcore.Oracle.V5.Response

/-! Total Oracle v5 projection of frozen Core checker diagnostics. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.CheckDiagnostic

open Solcore.Core
open Solcore.Core.Wire

def pathStepName : CheckPathStep → String
  | .pairLeft => "pairLeft"
  | .pairRight => "pairRight"
  | .firstOperand => "firstOperand"
  | .secondOperand => "secondOperand"
  | .lambdaBody => "lambdaBody"
  | .applyFunction => "applyFunction"
  | .applyArgument => "applyArgument"
  | .inLeftPayload => "inLeftPayload"
  | .inRightPayload => "inRightPayload"
  | .caseScrutinee => "caseScrutinee"
  | .caseLeftBranch => "caseLeftBranch"
  | .caseRightBranch => "caseRightBranch"
  | .newCellInitializer => "newCellInitializer"
  | .loadCellReference => "loadCellReference"
  | .storeCellReference => "storeCellReference"
  | .storeCellValue => "storeCellValue"
  | .constructPayload => "constructPayload"
  | .matchScrutinee => "matchScrutinee"
  | .matchBranch index => "matchBranch[" ++ toString index ++ "]"
  | .unaryOperand => "unaryOperand"
  | .binaryLeft => "binaryLeft"
  | .binaryRight => "binaryRight"
  | .ternaryFirst => "ternaryFirst"
  | .ternarySecond => "ternarySecond"
  | .ternaryThird => "ternaryThird"
  | .letValue => "letValue"
  | .letBody => "letBody"
  | .ifCondition => "ifCondition"
  | .ifThen => "ifThen"
  | .ifElse => "ifElse"

private def encodeCoreType
    (type : Solcore.Core.Ty) : Except InternalError Lean.Json :=
  match V3.Ty.ofCore? type with
  | some wire => .ok (V3.encodeType wire)
  | none => .error .coreWireProjectionFailed

private def oneType (name : String) (type : Solcore.Core.Ty) :
    Except InternalError Lean.Json := do
  .ok (.mkObj [(name, ← encodeCoreType type)])

private def twoTypes
    (firstName : String) (first : Solcore.Core.Ty)
    (secondName : String) (second : Solcore.Core.Ty) :
    Except InternalError Lean.Json := do
  .ok (.mkObj [
    (firstName, ← encodeCoreType first),
    (secondName, ← encodeCoreType second)
  ])

/-- Encode every current `CheckErrorData` constructor without a fallback. -/
def arguments : CheckErrorData → Except InternalError Lean.Json
  | .unboundVariable index contextSize => .ok (.mkObj [
      ("index", Lean.toJson index),
      ("contextSize", Lean.toJson contextSize)
    ])
  | .expectedBool actual => oneType "actual" actual
  | .expectedProduct actual => oneType "actual" actual
  | .expectedFunction actual => oneType "actual" actual
  | .functionArgumentTypeMismatch expected actual =>
      twoTypes "expected" expected "actual" actual
  | .lambdaResultTypeMismatch declared actual =>
      twoTypes "declared" declared "actual" actual
  | .expectedSum actual => oneType "actual" actual
  | .caseBranchTypeMismatch leftType rightType =>
      twoTypes "leftType" leftType "rightType" rightType
  | .invalidCellPayload actual => oneType "actual" actual
  | .cellInitializerTypeMismatch expected actual =>
      twoTypes "expected" expected "actual" actual
  | .expectedCell actual => oneType "actual" actual
  | .cellValueTypeMismatch expected actual =>
      twoTypes "expected" expected "actual" actual
  | .invalidDefinitionPayload dataTypeIndex constructorIndex actual => do
      .ok (.mkObj [
        ("dataTypeIndex", Lean.toJson dataTypeIndex),
        ("constructorIndex", Lean.toJson constructorIndex),
        ("actual", ← encodeCoreType actual)
      ])
  | .unknownNamedDataType dataType => .ok (.mkObj [
      ("dataType", V3.encodeDataTypeId (.ofCore dataType))
    ])
  | .unknownDataType dataType => .ok (.mkObj [
      ("dataType", V3.encodeDataTypeId (.ofCore dataType))
    ])
  | .unknownConstructor constructor => .ok (.mkObj [
      ("constructor", V3.encodeConstructorId (.ofCore constructor))
    ])
  | .constructorPayloadTypeMismatch expected actual =>
      twoTypes "expected" expected "actual" actual
  | .expectedNamedData actual => oneType "actual" actual
  | .matchDataTypeMismatch expected actual => .ok (.mkObj [
      ("expected", V3.encodeDataTypeId (.ofCore expected)),
      ("actual", V3.encodeDataTypeId (.ofCore actual))
    ])
  | .matchBranchCountMismatch expected actual => .ok (.mkObj [
      ("expected", Lean.toJson expected),
      ("actual", Lean.toJson actual)
    ])
  | .matchBranchResultTypeMismatch branchIndex expected actual => do
      .ok (.mkObj [
        ("branchIndex", Lean.toJson branchIndex),
        ("expected", ← encodeCoreType expected),
        ("actual", ← encodeCoreType actual)
      ])
  | .invalidResultType actual => oneType "actual" actual
  | .primitiveOperandTypeMismatch expected actual =>
      twoTypes "expected" expected "actual" actual
  | .branchTypeMismatch thenType elseType =>
      twoTypes "thenType" thenType "elseType" elseType
  | .declaredResultTypeMismatch declaredType inferredType =>
      twoTypes "declaredType" declaredType "inferredType" inferredType
  | .inferenceFailure => .ok (.mkObj [])

/-- Prefix the checker-local path with its exact request or package site. -/
def ofError
    (phase : Phase)
    (pathPrefix : List String)
    (error : CheckError) : Except InternalError Diagnostic := do
  .ok {
    code := error.codeName
    phase
    path := pathPrefix ++ error.path.map pathStepName
    arguments := ← arguments error.data
  }

end Solcore.Oracle.V5.CheckDiagnostic
