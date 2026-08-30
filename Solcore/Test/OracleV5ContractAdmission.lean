import Solcore.Oracle.V5.ContractAdmission

/-! Focused executable regressions for Oracle v5 contract admission. -/

set_option autoImplicit false

namespace Tests.OracleV5ContractAdmission

open Solcore
open Solcore.Core.Wire
open Solcore.Oracle.V5
open Solcore.Oracle.V5.ContractAdmission

private def word (value : Nat) (bound : value < Solcore.Core.wordModulus) :
    Solcore.Core.Word :=
  ⟨value, bound⟩

private def zero : Solcore.Core.Word := word 0 (by decide)
private def one : Solcore.Core.Word := word 1 (by decide)

private def returnProgram (value : Solcore.Core.Word := zero) : V3.Program := {
  resultType := .word
  dataDefinitions := []
  body := .word value
}

private def outcomeProgram : V3.Program := {
  resultType := .sum .word (.sum .word .word)
  dataDefinitions := []
  body := .inLeft (.sum .word .word) (.word zero)
}

private def boolProgram : V3.Program := {
  resultType := .bool
  dataDefinitions := []
  body := .bool true
}

private def unboundProgram : V3.Program := {
  resultType := .word
  dataDefinitions := []
  body := .var 14
}

private def identityProgram : V3.Program := {
  resultType := .function .word .word
  dataDefinitions := []
  body := .lambda .word .word (.var 0)
}

private def incrementProgram : V3.Program := {
  resultType := .function .word .word
  dataDefinitions := []
  body := .lambda .word .word
    (.binary .wordAdd (.var 0) (.word one))
}

private def methodWithDefinitions : V3.Program := {
  resultType := .function .word .word
  dataDefinitions := [{ constructorPayloadTypes := [] }]
  body := .lambda .word .word (.var 0)
}

private def raw
    (id : String)
    (program : V3.Program := returnProgram) : ContractInput := {
  id
  spec := .checkedCore program
}

private def method
    (name : String)
    (implementation : V3.Program := identityProgram) : StaticMethodInput := {
  name
  implementation
}

private def abi
    (id : String)
    (methods : List StaticMethodInput) : ContractInput := {
  id
  spec := .staticWordAbi methods
}

private def isAccepted
    (result : Except ContractAdmissionError ContractPackage) : Bool :=
  match result with
  | .ok _ => true
  | .error _ => false

private theorem frozenProfilesAccepted :
    isAccepted (admit [raw "return", raw "outcome" outcomeProgram]) = true := by
  native_decide

private def unsupportedRejected : Bool :=
  match admit [raw "boolean" boolProgram] with
  | .error (.unsupportedEntryResultType id actual) =>
      id.value == "boolean" && actual == .bool
  | _ => false

private theorem unsupportedRejected_exact : unsupportedRejected = true := by
  native_decide

private def checkerDiagnosticPreserved : Bool :=
  match admit [raw "broken" unboundProgram] with
  | .error (.coreCheckFailed (.checkedCore id) error) =>
      id.value == "broken" && error.path == [] &&
        error.data == .unboundVariable 14 14
  | _ => false

private theorem checkerDiagnosticPreserved_exact :
    checkerDiagnosticPreserved = true := by
  native_decide

private def duplicateIdPrecedesChecking : Bool :=
  match admit [raw "same" unboundProgram, raw "same" boolProgram] with
  | .error (.duplicateContractId id) => id.value == "same"
  | _ => false

private theorem duplicateIdPrecedesChecking_exact :
    duplicateIdPrecedesChecking = true := by
  native_decide

private def invalidIdCanonical : Bool :=
  let summarize (contracts : List ContractInput) :=
    match admit contracts with
    | .error (.invalidContractId actual) => some actual
    | _ => none
  summarize [raw "!z", raw "#a"] == some "!z" &&
    summarize [raw "#a", raw "!z"] == some "!z"

private theorem invalidIdCanonical_exact : invalidIdCanonical = true := by
  native_decide

private inductive AbiFailure where
  | accepted
  | empty
  | invalidName (name : String)
  | duplicate (signature : String)
  | checker (name : String) (error : Solcore.Core.CheckError)
  | resultType (name : String) (actual : Solcore.Core.Ty)
  | definitions (name : String) (count : Nat)
  | collision (first second : String) (selector : Nat)
  | other
  deriving BEq, DecidableEq

private def summarizeAbi
    (methods : List StaticMethodInput) : AbiFailure :=
  match admit [abi "abi" methods] with
  | .ok _ => .accepted
  | .error (.emptyMethodTable _) => .empty
  | .error (.invalidMethodName _ name) => .invalidName name
  | .error (.duplicateSignature _ _ _ signature) => .duplicate signature
  | .error (.coreCheckFailed (.staticMethod _ name) error) =>
      .checker name error
  | .error (.methodResultTypeMismatch _ name actual) =>
      .resultType name actual
  | .error (.methodDataDefinitionsNonempty _ name count) =>
      .definitions name count
  | .error (.selectorCollision _ first second selector) =>
      .collision first second selector.toUInt32.toNat
  | _ => .other

private theorem staticWordFailurePartition :
    summarizeAbi [] = .empty ∧
    summarizeAbi [method "9bad"] = .invalidName "9bad" ∧
    summarizeAbi [method "same", method "same" unboundProgram] =
      .duplicate "same(uint256)" ∧
    summarizeAbi [method "broken" unboundProgram] =
      .checker "broken" {
        path := []
        data := .unboundVariable 14 14
      } ∧
    summarizeAbi [method "wrong" (returnProgram one)] =
      .resultType "wrong" .word ∧
    summarizeAbi [method "defined" methodWithDefinitions] =
      .definitions "defined" 1 := by
  native_decide

private theorem staticWordAccepted :
    summarizeAbi [method "identity", method "increment" incrementProgram] =
      .accepted := by
  native_decide

private theorem knownSelectorCollision :
    summarizeAbi [method "f38491", method "f116643"] =
      .collision "f116643(uint256)" "f38491(uint256)" 0x77dbd42e := by
  native_decide

private def duplicateCodeIds
    (contracts : List ContractInput) : Option (String × String) :=
  match admit contracts with
  | .error (.duplicateCode first second) => some (first.value, second.value)
  | _ => none

private theorem rawDuplicateCodeCanonical :
    duplicateCodeIds [raw "z", raw "a"] = some ("a", "z") ∧
    duplicateCodeIds [raw "a", raw "z"] = some ("a", "z") := by
  native_decide

private theorem generatedAbiDuplicateCodeCanonical :
    duplicateCodeIds
        [abi "z" [method "identity"], abi "a" [method "identity"]] =
      some ("a", "z") := by
  native_decide

private def generatedDispatcherWire? : Option V3.Program := do
  let package ← match admit [abi "generated" [method "identity"]] with
    | .ok package => some package
    | .error _ => none
  let id ← ContractId.ofString? "generated"
  let entry ← package.lookupEntry? id
  V3.Program.ofCore? entry.program

private def rawGeneratedDuplicateCode : Bool :=
  match generatedDispatcherWire? with
  | none => false
  | some generated =>
      duplicateCodeIds
        [raw "zRaw" generated, abi "aAbi" [method "identity"]] ==
          some ("aAbi", "zRaw")

private theorem rawGeneratedDuplicateCode_exact :
    rawGeneratedDuplicateCode = true := by
  native_decide

private def packageLookupRoundTrips : Bool :=
  match admit [
      raw "zReturn" (returnProgram one),
      abi "middleAbi" [method "identity"],
      raw "aOutcome" outcomeProgram
    ] with
  | .error _ => false
  | .ok package =>
      package.entries.map (fun entry => entry.id.value) ==
          ["aOutcome", "middleAbi", "zReturn"] &&
        package.entries.all (fun entry =>
          (package.lookupEntry? entry.id).isSome &&
          (package.lookup? entry.id).isSome &&
          package.idByCode? entry.contract.code == some entry.id) &&
        (package.lookupRaw? "missing").isNone &&
        (package.lookupRaw? "not valid!").isNone &&
        (package.idByProgram? boolProgram.toCore).isNone

private theorem packageLookupRoundTrips_exact :
    packageLookupRoundTrips = true := by
  native_decide

/-- Optional focused runner for consumers that do not load `Tests.Main`. -/
def testOracleV5ContractAdmission : IO Unit := do
  unless isAccepted (admit [raw "return", raw "outcome" outcomeProgram]) &&
      unsupportedRejected &&
      checkerDiagnosticPreserved && duplicateIdPrecedesChecking &&
      invalidIdCanonical && rawGeneratedDuplicateCode &&
      packageLookupRoundTrips do
    throw (IO.userError "Oracle v5 contract admission regression failed")

end Tests.OracleV5ContractAdmission
