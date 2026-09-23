import Solcore.Abi.StaticWord
import Solcore.Core.Wire.V3.Codec
import Solcore.Foundation.Json
import Solcore.Oracle.V5.Schema
import Solcore.Oracle.V5.Wire.JsonBudget
import Solcore.ContractRuntime.RuntimeScalars.TextProperties

/-! Closed diagnostic values and the Core-check diagnostic catalog. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5

/-- One canonical semantic rejection before query-specific sealing. -/
structure Diagnostic where
  code : String
  phase : Phase
  path : List String
  arguments : Lean.Json
  deriving BEq

namespace Diagnostic

def severity (_diagnostic : Diagnostic) : String := "error"

def display (_diagnostic : Diagnostic) : Option String := none

namespace Catalog

def field? (json : Lean.Json) (name : String) : Option Lean.Json :=
  match json.getObjVal? name with
  | .ok value => some value
  | .error _ => none

def stringValue? : Lean.Json → Option String
  | .str value => some value
  | _ => none

def naturalValue? (json : Lean.Json) : Option Nat :=
  Solcore.Foundation.jsonNatural? json

def stringField? (json : Lean.Json) (name : String) : Option String := do
  stringValue? (← field? json name)

def naturalField? (json : Lean.Json) (name : String) : Option Nat := do
  naturalValue? (← field? json name)

def exactEmpty (json : Lean.Json) : Bool :=
  json == .mkObj []

def exactOne
    (name : String)
    (valid : Lean.Json → Bool)
    (json : Lean.Json) : Bool :=
  match field? json name with
  | some value => valid value && json == .mkObj [(name, value)]
  | none => false

def exactTwo
    (firstName : String)
    (firstValid : Lean.Json → Bool)
    (secondName : String)
    (secondValid : Lean.Json → Bool)
    (json : Lean.Json) : Bool :=
  match field? json firstName, field? json secondName with
  | some first, some second =>
      firstValid first && secondValid second &&
        json == .mkObj [(firstName, first), (secondName, second)]
  | _, _ => false

def exactThree
    (firstName : String)
    (firstValid : Lean.Json → Bool)
    (secondName : String)
    (secondValid : Lean.Json → Bool)
    (thirdName : String)
    (thirdValid : Lean.Json → Bool)
    (json : Lean.Json) : Bool :=
  match field? json firstName, field? json secondName, field? json thirdName with
  | some first, some second, some third =>
      firstValid first && secondValid second && thirdValid third &&
        json == .mkObj [
          (firstName, first), (secondName, second), (thirdName, third)]
  | _, _, _ => false

def isString (json : Lean.Json) : Bool :=
  (stringValue? json).isSome

def isNatural (json : Lean.Json) : Bool :=
  (naturalValue? json).isSome

def isCanonicalCoreType (json : Lean.Json) : Bool :=
  let demand := Wire.measureJson json
  let limits : Solcore.Core.Wire.V3.CoreBudgetLimits := {
    maxDepth := demand.depth + 1
    maxNodes := demand.nodes + 1
  }
  match Solcore.Core.Wire.V3.canonicalizeTypeWithBudget limits json with
  | .ok canonical => canonical == json
  | .error _ => false

def isCanonicalConstructorId (json : Lean.Json) : Bool :=
  match Solcore.Core.Wire.V3.canonicalizeConstructorId json with
  | .ok canonical => canonical == json
  | .error _ => false

def validCoreArguments (code : String) (arguments : Lean.Json) : Bool :=
  match code with
  | "core.check.unbound-variable" =>
      exactTwo "index" isNatural "contextSize" isNatural arguments
  | "core.check.expected-bool"
  | "core.check.expected-product"
  | "core.check.expected-function"
  | "core.check.expected-sum"
  | "core.check.invalid-cell-payload"
  | "core.check.expected-cell"
  | "core.check.expected-named-data"
  | "core.check.invalid-result-type" =>
      exactOne "actual" isCanonicalCoreType arguments
  | "core.check.function-argument-type-mismatch"
  | "core.check.cell-initializer-type-mismatch"
  | "core.check.cell-value-type-mismatch"
  | "core.check.constructor-payload-type-mismatch"
  | "core.check.primitive-operand-type-mismatch" =>
      exactTwo "expected" isCanonicalCoreType
        "actual" isCanonicalCoreType arguments
  | "core.check.lambda-result-type-mismatch" =>
      exactTwo "declared" isCanonicalCoreType
        "actual" isCanonicalCoreType arguments
  | "core.check.case-branch-type-mismatch" =>
      exactTwo "leftType" isCanonicalCoreType
        "rightType" isCanonicalCoreType arguments
  | "core.check.invalid-definition-payload" =>
      exactThree "dataTypeIndex" isNatural "constructorIndex" isNatural
        "actual" isCanonicalCoreType arguments
  | "core.check.unknown-named-data-type"
  | "core.check.unknown-data-type" =>
      exactOne "dataType" isNatural arguments
  | "core.check.unknown-constructor" =>
      exactOne "constructor" isCanonicalConstructorId arguments
  | "core.check.match-data-type-mismatch" =>
      exactTwo "expected" isNatural "actual" isNatural arguments
  | "core.check.match-branch-count-mismatch" =>
      exactTwo "expected" isNatural "actual" isNatural arguments
  | "core.check.match-branch-result-type-mismatch" =>
      exactThree "branchIndex" isNatural "expected" isCanonicalCoreType
        "actual" isCanonicalCoreType arguments
  | "core.check.branch-type-mismatch" =>
      exactTwo "thenType" isCanonicalCoreType
        "elseType" isCanonicalCoreType arguments
  | "core.check.declared-result-type-mismatch" =>
      exactTwo "declaredType" isCanonicalCoreType
        "inferredType" isCanonicalCoreType arguments
  | "core.check.inference-failure" => exactEmpty arguments
  | _ => false

private def asciiDigit (character : Char) : Bool :=
  48 ≤ character.toNat && character.toNat ≤ 57

private def nonzeroAsciiDigit (character : Char) : Bool :=
  49 ≤ character.toNat && character.toNat ≤ 57

private def canonicalNaturalCharacters : List Char → Bool
  | ['0'] => true
  | first :: rest => nonzeroAsciiDigit first && rest.all asciiDigit
  | [] => false

private def validMatchBranchStep (step : String) : Bool :=
  let expectedPrefix := "matchBranch[".toList
  let characters := step.toList
  if characters.take expectedPrefix.length != expectedPrefix then
    false
  else
    match (characters.drop expectedPrefix.length).reverse with
    | ']' :: reversedDigits =>
        canonicalNaturalCharacters reversedDigits.reverse
    | _ => false

private def fixedCheckPathSteps : List String := [
  "pairLeft", "pairRight", "firstOperand", "secondOperand", "lambdaBody",
  "applyFunction", "applyArgument", "inLeftPayload", "inRightPayload",
  "caseScrutinee", "caseLeftBranch", "caseRightBranch",
  "newCellInitializer", "loadCellReference", "storeCellReference",
  "storeCellValue", "constructPayload", "matchScrutinee", "unaryOperand",
  "binaryLeft", "binaryRight", "ternaryFirst", "ternarySecond",
  "ternaryThird", "letValue", "letBody", "ifCondition", "ifThen", "ifElse"
]

def validCheckPathStep (step : String) : Bool :=
  fixedCheckPathSteps.contains step || validMatchBranchStep step

def validCoreCheckPath : List String → Bool
  | "program" :: rest => rest.all validCheckPathStep
  | _ => false

def validContractCheckPath : List String → Bool
  | "contracts" :: contract :: "program" :: rest =>
      contractIdValid contract && rest.all validCheckPathStep
  | "contracts" :: contract :: "methods" :: method ::
      "implementation" :: rest =>
      contractIdValid contract && Solcore.Abi.V1.isValidMethodName method &&
        rest.all validCheckPathStep
  | _ => false

end Catalog

def isValidCoreCheck (diagnostic : Diagnostic) : Bool :=
  diagnostic.phase == .coreChecking &&
    Catalog.validCoreArguments diagnostic.code diagnostic.arguments &&
    Catalog.validCoreCheckPath diagnostic.path

def ValidCoreCheck (diagnostic : Diagnostic) : Prop :=
  diagnostic.isValidCoreCheck = true

end Diagnostic

end Solcore.Oracle.V5

/-!
## Consolidated module: `Solcore.Oracle.V5.DiagnosticExecutionValidity`
-/

/-! Closed execution-rejection diagnostic catalog. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.Diagnostic

open Catalog

private def validAddressText (value : String) : Bool :=
  (Solcore.ContractRuntime.decodeAddressText? value).isSome

private def validWordText (value : String) : Bool :=
  (Solcore.ContractRuntime.decodeWordText? value).isSome

private def validContractId (value : String) : Bool :=
  contractIdValid value

private def validMethodName (value : String) : Bool :=
  Solcore.Abi.V1.isValidMethodName value

private def lowerHexDigit (character : Char) : Bool :=
  let code := character.toNat
  (48 ≤ code && code ≤ 57) || (97 ≤ code && code ≤ 102)

private def validSelectorText (value : String) : Bool :=
  value.toList.length == 8 && value.toList.all lowerHexDigit

private def methodNameFromSignature?
    (signature : String) : Option Solcore.Abi.V1.MethodName := do
  let suffix := "(uint256)".toList
  let characters := signature.toList
  if characters.length ≤ suffix.length then
    none
  else if characters.drop (characters.length - suffix.length) != suffix then
    none
  else
    Solcore.Abi.V1.validateMethodName? <|
      String.ofList (characters.take (characters.length - suffix.length))

def selectorTextForSignature (signature : String) : String :=
  let selector := Solcore.Abi.V1.selectorFromSignatureBytes signature.toUTF8
  ((Solcore.ContractRuntime.encodeBytesText selector.encode).drop 2).toString

/-- The two checked-Core entry result types published by Oracle v5. -/
def entryResultTypeSupported : Solcore.Core.Wire.V3.Ty → Bool
  | .word
  | .sum .word (.sum .word .word) => true
  | _ => false

/-- The only Static Word method result type published by Oracle v5. -/
def staticWordMethodResultTypeSupported : Solcore.Core.Wire.V3.Ty → Bool
  | .function .word .word => true
  | _ => false

private def exactStringField?
    (arguments : Lean.Json)
    (name : String) : Option String := do
  let value ← stringField? arguments name
  if arguments == .mkObj [(name, value)] then some value else none

private def exactNaturalField?
    (arguments : Lean.Json)
    (name : String) : Option Nat := do
  let value ← naturalField? arguments name
  if arguments == .mkObj [(name, Lean.toJson value)] then some value else none

private def exactTwoStrings?
    (arguments : Lean.Json)
    (firstName secondName : String) : Option (String × String) := do
  let first ← stringField? arguments firstName
  let second ← stringField? arguments secondName
  if arguments == .mkObj [(firstName, first), (secondName, second)] then
    some (first, second)
  else
    none

private def exactThreeStrings?
    (arguments : Lean.Json)
    (firstName secondName thirdName : String) :
    Option (String × String × String) := do
  let first ← stringField? arguments firstName
  let second ← stringField? arguments secondName
  let third ← stringField? arguments thirdName
  if arguments == .mkObj [
      (firstName, first), (secondName, second), (thirdName, third)] then
    some (first, second, third)
  else
    none

private def exactCanonicalCoreTypeField?
    (arguments : Lean.Json)
    (name : String) : Option Solcore.Core.Wire.V3.Ty := do
  let value ← field? arguments name
  if arguments != .mkObj [(name, value)] then
    none
  else
    let demand := Wire.measureJson value
    let limits : Solcore.Core.Wire.V3.CoreBudgetLimits := {
      maxDepth := demand.depth + 1
      maxNodes := demand.nodes + 1
    }
    match Solcore.Core.Wire.V3.decodeTypeWithBudget limits value with
    | .ok type =>
        if Solcore.Core.Wire.V3.encodeType type == value then some type else none
    | .error _ => none

private def validContractPath
    (path : List String)
    (suffix : List String) : Bool :=
  match path with
  | "contracts" :: contract :: rest =>
      validContractId contract && rest == suffix
  | _ => false

private def validMethodPath
    (path : List String)
    (methodName : String)
    (suffix : List String) : Bool :=
  match path with
  | "contracts" :: contract :: "methods" :: method :: rest =>
      validContractId contract && method == methodName && rest == suffix
  | _ => false

private def validInvalidContractId
    (path : List String)
    (arguments : Lean.Json) : Bool :=
  match exactStringField? arguments "actual" with
  | some actual =>
      !validContractId actual && path == ["contracts", actual, "id"]
  | none => false

private def validDuplicateContractId
    (path : List String)
    (arguments : Lean.Json) : Bool :=
  match exactStringField? arguments "id" with
  | some id => validContractId id && path == ["contracts", id, "id"]
  | none => false

private def validEntryType
    (path : List String)
    (arguments : Lean.Json) : Bool :=
  match exactCanonicalCoreTypeField? arguments "actual" with
  | some actual =>
      !entryResultTypeSupported actual &&
        validContractPath path ["program", "resultType"]
  | none => false

private def validInvalidMethodName
    (path : List String)
    (arguments : Lean.Json) : Bool :=
  match exactStringField? arguments "actual" with
  | some actual =>
      !validMethodName actual && validMethodPath path actual ["name"]
  | none => false

private def validMethodDefinitions
    (path : List String)
    (arguments : Lean.Json) : Bool :=
  match exactNaturalField? arguments "count", path with
  | some count, "contracts" :: contract :: "methods" :: method :: rest =>
      0 < count && validContractId contract && validMethodName method &&
        rest == ["implementation", "dataDefinitions"]
  | _, _ => false

private def validMethodResultType
    (path : List String)
    (arguments : Lean.Json) : Bool :=
  match exactCanonicalCoreTypeField? arguments "actual", path with
  | some actual, "contracts" :: contract :: "methods" :: method :: rest =>
      !staticWordMethodResultTypeSupported actual &&
        validContractId contract && validMethodName method &&
        rest == ["implementation", "resultType"]
  | _, _ => false

private def validEmptyMethodTable
    (path : List String)
    (arguments : Lean.Json) : Bool :=
  exactEmpty arguments && validContractPath path ["methods"]

private def validDuplicateSignature
    (path : List String)
    (arguments : Lean.Json) : Bool :=
  match exactThreeStrings? arguments
      "signature" "firstMethod" "secondMethod" with
  | some (signature, first, second) =>
      validMethodName first && first == second &&
        signature == first ++ "(uint256)" && validContractPath path ["methods"]
  | none => false

private def validSelectorCollision
    (path : List String)
    (arguments : Lean.Json) : Bool :=
  match exactThreeStrings? arguments
      "selector" "firstSignature" "secondSignature" with
  | some (selector, first, second) =>
      validSelectorText selector && (compare first second).isLT &&
        (methodNameFromSignature? first).isSome &&
        (methodNameFromSignature? second).isSome &&
        selectorTextForSignature first == selector &&
        selectorTextForSignature second == selector &&
        validContractPath path ["methods"]
  | none => false

private def validDuplicateCode
    (path : List String)
    (arguments : Lean.Json) : Bool :=
  match exactTwoStrings? arguments "firstId" "secondId" with
  | some (first, second) =>
      validContractId first && validContractId second &&
        (compare first second).isLT &&
        path == ["contracts", second]
  | none => false

private def validDanglingReference
    (phase : Phase)
    (path : List String)
    (arguments : Lean.Json) : Bool :=
  match exactStringField? arguments "id" with
  | none => false
  | some _id =>
      match phase, path with
      | .worldValidation, ["world", "accounts", address, "code"] =>
          validAddressText address
      | .environmentValidation,
          ["environment", "callRegistry", address, "contract"] =>
          validAddressText address
      | .environmentValidation,
          ["environment", "creationTemplates", templateId, endpoint] =>
          validWordText templateId &&
            (endpoint == "initializer" || endpoint == "runtime")
      | _, _ => false

private def validAddressArgumentPath
    (path : List String)
    (arguments : Lean.Json)
    (start finish : List String) : Bool :=
  match exactStringField? arguments "address" with
  | some address =>
      validAddressText address && path == start ++ address :: finish
  | none => false

private def validWorldStorage
    (zeroValue : Bool)
    (path : List String)
    (arguments : Lean.Json) : Bool :=
  match exactTwoStrings? arguments "address" "slot" with
  | some (address, slot) =>
      validAddressText address && validWordText slot &&
        path == ["world", "accounts", address, "storage", slot] ++
          (if zeroValue then ["value"] else [])
  | none => false

private def validTemplateId
    (path : List String)
    (arguments : Lean.Json) : Bool :=
  match exactStringField? arguments "templateId" with
  | some templateId =>
      validWordText templateId &&
        path == ["environment", "creationTemplates", templateId]
  | none => false

private def validCreationRoute
    (path : List String)
    (arguments : Lean.Json) : Bool :=
  match exactTwoStrings? arguments "creator" "nonce" with
  | some (creator, nonce) =>
      validAddressText creator && validWordText nonce && path == [
        "environment", "creationAddressPolicy", "routes", creator, nonce]
  | none => false

private def validDuplicateProbe
    (path : List String)
    (arguments : Lean.Json) : Bool :=
  match naturalField? arguments "firstIndex",
      naturalField? arguments "secondIndex" with
  | some first, some second =>
      arguments == .mkObj [
        ("firstIndex", Lean.toJson first), ("secondIndex", Lean.toJson second)] &&
        first < second && path == ["invocation", "probes", toString second]
  | _, _ => false

private def validRootTarget
    (path : List String)
    (arguments : Lean.Json)
    (codeAbsent : Bool) : Bool :=
  match exactStringField? arguments "target" with
  | some target =>
      validAddressText target && path == ["world", "accounts", target] ++
        (if codeAbsent then ["code"] else [])
  | none => false

private def validScenarioDiagnostic (diagnostic : Diagnostic) : Bool :=
  match diagnostic.code, diagnostic.phase with
  | "oracle.v5.contract.invalid-id", .contractAdmission =>
      validInvalidContractId diagnostic.path diagnostic.arguments
  | "oracle.v5.contract.duplicate-id", .contractAdmission =>
      validDuplicateContractId diagnostic.path diagnostic.arguments
  | "oracle.v5.contract.unsupported-entry-result-type", .contractAdmission =>
      validEntryType diagnostic.path diagnostic.arguments
  | "oracle.v5.method.invalid-name", .contractAdmission =>
      validInvalidMethodName diagnostic.path diagnostic.arguments
  | "oracle.v5.method.nonempty-data-definitions", .contractAdmission =>
      validMethodDefinitions diagnostic.path diagnostic.arguments
  | "oracle.v5.method.result-type-mismatch", .contractAdmission =>
      validMethodResultType diagnostic.path diagnostic.arguments
  | "oracle.v5.abi.empty-method-table", .contractAdmission =>
      validEmptyMethodTable diagnostic.path diagnostic.arguments
  | "oracle.v5.abi.duplicate-signature", .contractAdmission =>
      validDuplicateSignature diagnostic.path diagnostic.arguments
  | "oracle.v5.abi.selector-collision", .contractAdmission =>
      validSelectorCollision diagnostic.path diagnostic.arguments
  | "oracle.v5.contract.duplicate-code", .contractAdmission =>
      validDuplicateCode diagnostic.path diagnostic.arguments
  | "oracle.v5.reference.dangling-contract", phase =>
      validDanglingReference phase diagnostic.path diagnostic.arguments
  | "oracle.v5.world.duplicate-account", .worldValidation =>
      validAddressArgumentPath diagnostic.path diagnostic.arguments
        ["world", "accounts"] []
  | "oracle.v5.world.duplicate-storage-slot", .worldValidation =>
      validWorldStorage false diagnostic.path diagnostic.arguments
  | "oracle.v5.world.zero-storage-value", .worldValidation =>
      validWorldStorage true diagnostic.path diagnostic.arguments
  | "oracle.v5.environment.duplicate-call-address", .environmentValidation =>
      validAddressArgumentPath diagnostic.path diagnostic.arguments
        ["environment", "callRegistry"] []
  | "oracle.v5.environment.duplicate-template-id", .environmentValidation =>
      validTemplateId diagnostic.path diagnostic.arguments
  | "oracle.v5.environment.duplicate-creation-route", .environmentValidation =>
      validCreationRoute diagnostic.path diagnostic.arguments
  | "oracle.v5.probe.duplicate", .probeValidation =>
      validDuplicateProbe diagnostic.path diagnostic.arguments
  | "oracle.v5.root.target-absent", .rootInstallation =>
      validRootTarget diagnostic.path diagnostic.arguments false
  | "oracle.v5.root.target-code-absent", .rootInstallation =>
      validRootTarget diagnostic.path diagnostic.arguments true
  | _, _ => false

def isValidExecute (diagnostic : Diagnostic) : Bool :=
  (diagnostic.phase == .contractAdmission &&
      Catalog.validCoreArguments diagnostic.code diagnostic.arguments &&
      Catalog.validContractCheckPath diagnostic.path) ||
    validScenarioDiagnostic diagnostic

def ValidExecute (diagnostic : Diagnostic) : Prop :=
  diagnostic.isValidExecute = true

end Solcore.Oracle.V5.Diagnostic
