import Solcore.Frontend.SourceInference

/-! End-to-end source inference for proxy values and mapping indexing. -/

set_option autoImplicit false

namespace Tests.SourceStructuralExpressions

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def check (content : String) :
    IO (List SourceInference.CheckedFunction) := do
  match SourceInference.loadAndCheckProgram (workspace content) with
  | .ok checked => pure checked
  | .error errors =>
      throw (IO.userError s!"structural expression checking failed: {reprStr errors}")

private def hasBodyError (content : String)
    (accepts : SourceInference.Error → Bool) : IO Bool :=
  match SourceInference.loadAndCheckProgram (workspace content) with
  | .error errors => pure <| errors.any fun error => match error with
      | .body functionError => accepts functionError.error
      | _ => false
  | .ok _ => pure false

private def testProxyValuesResolveSourceTypes : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "function concrete() returns (@Word) { return @Word; }",
    "function generic<T>() returns (@T) { return @T; }"
  ])
  match checked with
  | [concrete, generic] =>
      assertTrue (decide (concrete.inferredBodyType = .proxy .word))
        "a proxy value did not retain its resolved builtin type"
      assertTrue (match generic.inferredBodyType with
        | .proxy (.parameter parameter) =>
            decide (parameter.owner = generic.declaration) && parameter.index == 0
        | _ => false)
        "a proxy value did not retain its declaration-owned generic parameter"
  | _ => throw (IO.userError "proxy fixture lost a checked function")

private def testMappingIndexInfersValue : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "function read(values: mapping(Word => Bool), key: Word) returns (Bool) {",
    "  return values[key];",
    "}",
    "function readLiteral(values: mapping(Word => Bool)) returns (Bool) {",
    "  return values[1];",
    "}"
  ])
  assertTrue (checked.all fun function =>
      function.inferredBodyType == TypeSystem.Ty.bool &&
        function.predicates.isEmpty && function.evidence.isEmpty)
    "mapping indexing did not infer the mapped value without extra evidence"

private def testMappingKeyUsesCoercion : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "impl Coerce<Bool, Word> {}",
    "function read(values: mapping(Word => Bool), key: Bool) returns (Bool) {",
    "  return values[key];",
    "}"
  ])
  match checked.getLast? with
  | some function =>
      assertTrue (function.predicates.length == 1 &&
          function.evidence.any fun evidence => match evidence with
            | .implementation _ => true
            | .assumption _ => false)
        "a mapping key coercion lost its predicate or implementation evidence"
  | none => throw (IO.userError "mapping coercion fixture checked no function")

private def testNonMappingBaseIsRejected : IO Unit := do
  let rejected ← hasBodyError
    "function bad(value: Word) returns (Word) { return value[0]; }"
    fun error => match error with
      | .unification (.mismatch _ (.mapping _ _)) => true
      | _ => false
  assertTrue rejected "indexing a non-mapping value did not report a type mismatch"

private def testWrongMappingKeyIsRejected : IO Unit := do
  let rejected ← hasBodyError (String.intercalate "\n" [
    "function bad(values: mapping(Word => Bool)) returns (Bool) {",
    "  return values[true];",
    "}"
  ]) fun error => match error with
    | .unification (.mismatch .bool .word) => true
    | .unification (.mismatch .word .bool) => true
    | _ => false
  assertTrue rejected "a mapping index with the wrong key type was accepted"

private def testUnknownProxyTypeIsRejected : IO Unit := do
  let rejected ← hasBodyError
    "function bad() returns (@Word) { return @Missing; }"
    fun error => match error with
      | .typeResolution (.unknownTypeName ["Missing"]) => true
      | _ => false
  assertTrue rejected "an unknown type in a proxy value was accepted"

/-- Exercise source type resolution, unification and coercion through the first
advanced structural expression forms. -/
def testSourceStructuralExpressions : IO Unit := do
  testProxyValuesResolveSourceTypes
  testMappingIndexInfersValue
  testMappingKeyUsesCoercion
  testNonMappingBaseIsRejected
  testWrongMappingKeyIsRejected
  testUnknownProxyTypeIsRejected

end Tests.SourceStructuralExpressions
