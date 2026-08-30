import Solcore.Abi.StaticWordMetadata
import Solcore.Core.Wire.V3.Codec
import Solcore.Foundation.Json
import Solcore.Oracle.V5.Schema
import Solcore.Oracle.V5.Wire.JsonBudget

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
