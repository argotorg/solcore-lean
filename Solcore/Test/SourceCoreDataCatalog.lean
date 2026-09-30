import Solcore.Frontend.SourceCoreDataCatalog

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value

set_option autoImplicit false

namespace Tests.SourceCoreDataCatalog

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open SourceCoreDataCatalog

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def rejected {α : Type} : Except SourceCoreDataCatalog.Error α → Bool
  | .error _ => true
  | .ok _ => false

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Tree<T> { Leaf(T), Pair(Tree<T>, Tree<T>) }",
    "enum Box { Only }",
    "function identity(value: Word) returns (Word) { return value; }"
  ] }]
}

private def expectIdentity (catalog : Catalog) (type : TypeSystem.Ty) : IO Core.DataTypeId :=
  match catalog.identity? type with
  | some identity => pure identity
  | none => throw (IO.userError s!"missing representation {reprStr type}")

private def expectProjection (checked : Checked) (type : TypeSystem.Ty) (expected : Core.Ty) : IO Unit := do
  match checked.project type with
  | .ok projected => assertTrue (projected.type == expected) "checked catalog projection changed"
  | .error error => throw (IO.userError s!"projection rejected {reprStr error}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"catalog fixture rejected {reprStr errors}")
  let tree ← match program.signatures.dataTypes.find? (·.name == "Tree") with
    | some signature => pure signature
    | none => throw (IO.userError "missing Tree signature")
  let wordTree := TypeSystem.Ty.nominal tree.id [.word]
  let boolTree := TypeSystem.Ty.nominal tree.id [.bool]
  let functionKey := TypeSystem.Ty.function .word .word
  let nested := TypeSystem.Ty.mapping (.proxy .word) (.mapping functionKey wordTree)
  let checked ← match prepare program.signatures 64
      [wordTree, wordTree, boolTree, nested, .proxy .bool, .proxy (.comptime .word), .integer] with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"catalog discovery rejected {reprStr error}")
  let catalog := checked.catalog
  let wordId ← expectIdentity catalog wordTree
  let boolId ← expectIdentity catalog boolTree
  let proxyWord ← expectIdentity catalog (.proxy .word)
  let proxyBool ← expectIdentity catalog (.proxy .bool)
  let proxyStaged ← expectIdentity catalog (.proxy (.comptime .word))
  assertTrue (wordId != boolId) "nominal specialization identities collapsed"
  assertTrue (proxyWord != proxyBool && proxyWord != proxyStaged)
    "observable proxy identities collapsed"
  assertTrue ((catalog.entries.filter (fun entry => decide (entry.sourceType = wordTree))).length == 1)
    "recursive nominal discovery duplicated its identity"
  assertTrue (catalog.definitions.lookupConstructorPayloadType? ⟨wordId, 0⟩ == some .word)
    "nominal Leaf payload changed"
  assertTrue (catalog.definitions.lookupConstructorPayloadType? ⟨wordId, 1⟩ ==
      some (.product (.namedData wordId) (.namedData wordId)))
    "recursive nominal payload references changed"
  let nestedId ← expectIdentity catalog nested
  let innerId ← expectIdentity catalog (.mapping functionKey wordTree)
  assertTrue (catalog.definitions.lookupConstructorPayloadType? ⟨nestedId, 1⟩ ==
      some (.product (.product (.namedData proxyWord) (.namedData innerId)) (.namedData nestedId)))
    "mapping entry or recursive tail layout changed"
  expectProjection checked .integer .integer
  expectProjection checked (.comptime wordTree) (.namedData wordId)
  expectProjection checked functionKey (Core.TaggedFunction.functionType .word .word)
  let leaf ← match tree.constructors.find? (·.name == "Leaf") with
    | some constructor => pure constructor
    | none => throw (IO.userError "missing Leaf constructor")
  let instantiation : DataConstructorInstantiation := {
    constructor := leaf.id
    parameterSubstitution := tree.parameters.zip [.word]
    payloadTypes := [.word]
    resultType := wordTree
  }
  assertTrue ((catalog.resolveConstructor program.signatures instantiation).toOption == some ⟨wordId, 0⟩)
    "authentic constructor rejected"
  for forged in [
      { instantiation with payloadTypes := [.bool] },
      { instantiation with resultType := boolTree },
      { instantiation with parameterSubstitution := [] }] do
    assertTrue (rejected (catalog.resolveConstructor program.signatures forged))
      "forged constructor metadata accepted"
  assertTrue (rejected (prepare program.signatures 2 [wordTree])) "catalog depth budget ignored"
  assertTrue (rejected (prepare program.signatures 64 [.«variable» ⟨0⟩])) "open source type accepted"
  assertTrue (rejected (prepare program.signatures 64 [TypeSystem.Ty.nominal tree.id []]))
    "nominal arity mismatch accepted"
  assertTrue (rejected (prepare { program.signatures with dataTypes := tree :: program.signatures.dataTypes }
    64 [wordTree])) "ambiguous nominal catalog accepted"
  assertTrue (catalog.emptyMapping? (.proxy .word) (.mapping functionKey wordTree) ==
    some (.constructed ⟨nestedId, 0⟩ .unit)) "empty mapping carrier changed"
  IO.println "source Core data catalog GREEN"

end Tests.SourceCoreDataCatalog
