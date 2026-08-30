import Solcore.Abi.StaticWordMetadata
import Solcore.Oracle.V5.Diagnostic
import Solcore.Semantics.RuntimeScalars.TextProperties

/-! Closed execution-rejection diagnostic catalog. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.Diagnostic

open Catalog

private def validAddressText (value : String) : Bool :=
  (Solcore.Semantics.decodeAddressText? value).isSome

private def validWordText (value : String) : Bool :=
  (Solcore.Semantics.decodeWordText? value).isSome

private def validContractId (value : String) : Bool :=
  contractIdValid value

private def validMethodName (value : String) : Bool :=
  Solcore.Abi.V1.isValidMethodName value

private def lowerHexDigit (character : Char) : Bool :=
  let code := character.toNat
  (48 ≤ code && code ≤ 57) || (97 ≤ code && code ≤ 102)

private def validSelectorText (value : String) : Bool :=
  value.toList.length == 8 && value.toList.all lowerHexDigit

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
  exactOne "actual" isCanonicalCoreType arguments &&
    validContractPath path ["program", "resultType"]

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
  match path with
  | "contracts" :: contract :: "methods" :: method :: rest =>
      exactOne "actual" isCanonicalCoreType arguments &&
        validContractId contract && validMethodName method &&
        rest == ["implementation", "resultType"]
  | _ => false

private def validEmptyMethodTable
    (path : List String)
    (arguments : Lean.Json) : Bool :=
  exactEmpty arguments && validContractPath path ["methods"]

private def validDuplicateSignature
    (path : List String)
    (arguments : Lean.Json) : Bool :=
  match exactThreeStrings? arguments
      "signature" "firstMethod" "secondMethod" with
  | some (_signature, first, second) =>
      validMethodName first && validMethodName second && first != second &&
        validContractPath path ["methods"]
  | none => false

private def validSelectorCollision
    (path : List String)
    (arguments : Lean.Json) : Bool :=
  match exactThreeStrings? arguments
      "selector" "firstSignature" "secondSignature" with
  | some (selector, first, second) =>
      validSelectorText selector && first != second &&
        validContractPath path ["methods"]
  | none => false

private def validDuplicateCode
    (path : List String)
    (arguments : Lean.Json) : Bool :=
  match exactTwoStrings? arguments "firstId" "secondId" with
  | some (first, second) =>
      validContractId first && validContractId second && first != second &&
        path == ["contracts", second]
  | none => false

private def validDanglingReference
    (phase : Phase)
    (path : List String)
    (arguments : Lean.Json) : Bool :=
  match exactStringField? arguments "id" with
  | none => false
  | some id =>
      validContractId id && match phase, path with
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
