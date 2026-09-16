import Solcore.Frontend.SourceInference

/-! End-to-end regressions for value/trait consumers of direct imports. -/

set_option autoImplicit false

namespace Tests.ImportedResolutionConsumers

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def raw (sources : List (String × String)) (entry : String) :
    Workspace.RawWorkspace := {
  entry
  mainSources := sources.map fun source => {
    path := source.1
    content := source.2
  }
  externalLibraries := []
}

private def provider : String := String.intercalate "\n" [
  "trait Eq<T> {}",
  "function remote(value: Bool) returns (Bool) { return value; }",
  "function hidden(value: Bool) returns (Bool) { return value; }"
]

private def expectSuccess (workspace : Workspace.RawWorkspace) : IO Unit := do
  match SourceInference.loadAndCheckProgram workspace with
  | .ok _ => pure ()
  | .error errors => throw (IO.userError s!"checking failed: {reprStr errors}")

private def testSelectedValuesTraitsAndLocalShadowing : IO Unit := do
  let consumer := String.intercalate "\n" [
    "import {remote as imported, Eq as Comparable} from provider;",
    "function remote(value: Word) returns (Word) { return value; }",
    "impl Comparable<Word> {}",
    "function constrained<T>(value: T) returns (T) where T: Comparable { return value; }",
    "function run() returns (Word, Bool) { return (remote(1), imported(true)); }"
  ]
  expectSuccess (raw [("provider.solc", provider), ("consumer.solc", consumer)]
    "consumer.solc")

private def testQualifiedNamespaceValue : IO Unit := do
  let consumer := String.intercalate "\n" [
    "import * as Provider from provider;",
    "function run() returns (Bool) { return Provider.remote(true); }"
  ]
  expectSuccess (raw [("provider.solc", provider), ("consumer.solc", consumer)]
    "consumer.solc")

private def testImportsCloseUnqualifiedVisibility : IO Unit := do
  let consumer := String.intercalate "\n" [
    "import {remote} from provider;",
    "function bad() returns (Bool) { return hidden(true); }"
  ]
  match SourceInference.loadAndCheckProgram
      (raw [("provider.solc", provider), ("consumer.solc", consumer)]
        "consumer.solc") with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .noMatchingOverload "hidden" candidates, .. } =>
            candidates.isEmpty
        | _ => false)
        "an unimported value remained visible after a direct import"
  | .ok _ => throw (IO.userError "an unimported value remained visible")

private def testNoImportFallback : IO Unit := do
  let consumer :=
    "function run() returns (Bool) { return hidden(true); }"
  expectSuccess (raw [("provider.solc", provider), ("consumer.solc", consumer)]
    "consumer.solc")

private def testAmbiguousNamespace : IO Unit := do
  let left := "function choose(value: Word) returns (Word) { return value; }"
  let right := "function choose(value: Word) returns (Word) { return value; }"
  let consumer := String.intercalate "\n" [
    "import * as Shared from left;",
    "import * as Shared from right;",
    "function run() returns (Word) { return Shared.choose(1); }"
  ]
  match SourceInference.loadAndCheckProgram
      (raw [("left.solc", left), ("right.solc", right),
        ("consumer.solc", consumer)] "consumer.solc") with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .ambiguousImportedNamespace "Shared" modules, .. } =>
            modules.length == 2
        | _ => false)
        "ambiguous imported namespace lost its explicit diagnostic"
  | .ok _ => throw (IO.userError "ambiguous imported namespace was selected")

/-- Exercise import-aware trait and value lookup at their semantic consumers. -/
def testImportedResolutionConsumers : IO Unit := do
  testSelectedValuesTraitsAndLocalShadowing
  testQualifiedNamespaceValue
  testImportsCloseUnqualifiedVisibility
  testNoImportFallback
  testAmbiguousNamespace

end Tests.ImportedResolutionConsumers
