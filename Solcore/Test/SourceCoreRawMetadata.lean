import Solcore.Frontend.SourceCoreRawMetadata
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreRawMetadata.Registry.mk
#check_failure Solcore.Frontend.SourceCoreRawMetadata.Inserted.mk
#check_failure fun (registry : Solcore.Frontend.SourceCoreRawMetadata.Registry) =>
  { registry with metadataValues := [] }

/-! Authenticated raw metadata retains stage wrappers that are invisible to
runtime type compatibility. No executable source value or Core capability is
registered. Public consumer observations are tested in a separate module. -/

set_option autoImplicit false

namespace Tests.SourceCoreRawMetadata

open Solcore Solcore.Frontend SourceInference SourceCoreRawMetadata

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "enum Pair<A, B> { Pair(A, B) }",
    "enum Tree { Leaf(Word), Branch(Tree, Tree) }",
    "function main() returns (Word) { return 7; }"
  ] }] }

private def checked : IO CheckedProgram :=
  match checkProgram workspace with
  | .ok program => pure program
  | .error error => throw (IO.userError s!"raw metadata fixture failed checking: {reprStr error}")

private def data (program : CheckedProgram) (name : String) : IO ProgramDataSignature :=
  match program.signatures.dataTypes.filter (·.name == name) with
  | [signature] => pure signature
  | _ => throw (IO.userError s!"raw metadata data signature missing: {name}")

private def metadata (signature : ProgramDataSignature) (arguments : List TypeSystem.Ty)
    (index : Nat := 0) : IO DataConstructorInstantiation := do
  let constructor ← match signature.constructors[index]? with
    | some constructor => pure constructor
    | none => throw (IO.userError "raw metadata constructor missing")
  let substitution : TypeSystem.ParameterSubstitution := signature.parameters.zip arguments
  pure ⟨constructor.id, substitution, constructor.payloadTypes.map substitution.apply,
    .nominal signature.id arguments⟩

private def inserted (registry : Registry) (type : TypeSystem.Ty) (metadata : Metadata) :
    IO (Inserted registry type metadata) :=
  match registry.intern type metadata with
  | .ok inserted => pure inserted
  | .error error => throw (IO.userError s!"raw metadata insertion failed: {reprStr error}")

example (before : Registry) (expected : TypeSystem.Ty) (metadata : Metadata)
    (accepted : Inserted before expected metadata) :
    accepted.registry.lookup accepted.id = some metadata := accepted.reconstruct

example (before : Registry) (expected : TypeSystem.Ty) (metadata : Metadata)
    (accepted : Inserted before expected metadata) :
    runtimeType expected = runtimeType metadata.type := accepted.runtime_compatible

example (before : Registry) (expected : TypeSystem.Ty) (metadata : Metadata)
    (accepted : Inserted before expected metadata) (oldId : Core.Word) (oldMetadata : Metadata)
    (oldFound : before.lookup oldId = some oldMetadata) :
    accepted.registry.lookup oldId = some oldMetadata := accepted.preserves.lookup oldFound

example (registry : Registry) (left right : Core.Word) (a b : Metadata)
    (leftFound : registry.lookup left = some a) (rightFound : registry.lookup right = some b) :
    (left == right) = decide (a = b) := registry.word_equality_iff leftFound rightFound

example : idAt? (Core.wordModulus - 1) = none := by
  simp [idAt?, Core.Word.ofNat?, Core.wordModulus]

def run : IO Unit := do
  let program ← checked
  let box ← data program "Box"
  let pair ← data program "Pair"
  let tree ← data program "Tree"
  let ordinaryBox ← metadata box [.word]
  let stagedBox ← metadata box [.comptime .word]
  let ordinary : Metadata := .proxy .word
  let staged : Metadata := .proxy (.comptime .word)
  let registry ← match prepare program.signatures [ordinary, .constructor ordinaryBox, ordinary] with
    | .ok registry => pure registry
    | .error error => throw (IO.userError s!"static metadata preparation failed: {reprStr error}")
  assertTrue (registry.length == 2 && registry.staticLength == 2) "static metadata did not deduplicate in discovery order"
  let ordinaryId ← match registry.id? ordinary with
    | some id => pure id
    | none => throw (IO.userError "static proxy ID missing")
  assertTrue (ordinaryId.val == 1) "static metadata IDs are not one based"
  let stagedInsertion ← inserted registry (.proxy .word) staged
  let extended := stagedInsertion.registry
  assertTrue (stagedInsertion.id.val == 3 && extended.staticLength == 2) "dynamic extension changed the static prefix"
  assertTrue (extended.lookup ordinaryId == some ordinary) "dynamic extension changed an old ID"
  assertTrue (extended.lookup stagedInsertion.id == some staged) "dynamic extension erased proxy raw identity"
  assertTrue (ordinaryId != stagedInsertion.id) "runtime-equivalent proxy identities collapsed"
  let repeated ← inserted extended (.comptime (.proxy .word)) staged
  assertTrue (repeated.registry.length == extended.length && repeated.id == stagedInsertion.id)
    "same raw metadata was assigned another slot"
  let nominalInsertion ← inserted repeated.registry (.nominal box.id [.word]) (.constructor stagedBox)
  assertTrue (nominalInsertion.registry.lookup nominalInsertion.id == some (.constructor stagedBox))
    "raw nominal substitution/payload/result metadata changed"
  let mappingRaw : Metadata := .mapping (.comptime .word) (.proxy (.comptime .word))
  let mappingInsertion ← inserted nominalInsertion.registry (.mapping .word (.proxy .word)) mappingRaw
  assertTrue (mappingInsertion.registry.lookup mappingInsertion.id == some mappingRaw) "mapping raw header changed"
  assertTrue (mappingInsertion.registry.staticLength == registry.staticLength) "static prefix grew during input extension"
  let recursive ← metadata tree [] 1
  discard <| inserted mappingInsertion.registry recursive.resultType (.constructor recursive)
  for forged in [
      { stagedBox with payloadTypes := [.bool] },
      { stagedBox with resultType := .nominal box.id [.bool] },
      { stagedBox with constructor := { stagedBox.constructor with constructorIndex := 99 } },
      { stagedBox with parameterSubstitution := stagedBox.parameterSubstitution ++ stagedBox.parameterSubstitution }] do
    assertTrue (!constructorAuthentic program.signatures forged) "forged constructor metadata authenticated"
    match registry.intern forged.resultType (.constructor forged) with
    | .error (.invalidConstructor _) => pure ()
    | _ => throw (IO.userError "forged metadata was interned")
  let pairMetadata ← metadata pair [.word, .bool]
  let reordered := {pairMetadata with parameterSubstitution := pairMetadata.parameterSubstitution.reverse}
  assertTrue (!constructorAuthentic program.signatures reordered) "constructor substitution order was ignored"
  let limited ← match prepare program.signatures [ordinary] { maxEntries := 1 } with
    | .ok registry => pure registry
    | .error error => throw (IO.userError s!"one-entry registry failed: {reprStr error}")
  discard <| inserted limited (.proxy .word) ordinary
  match limited.intern (.proxy .word) staged with
  | .error (.entryBudgetExhausted 1) => pure ()
  | _ => throw (IO.userError "distinct metadata bypassed the registry budget")
  match limited.intern (.proxy .bool) staged with
  | .error (.runtimeTypeMismatch _ _) => pure ()
  | _ => throw (IO.userError "metadata type validation did not precede budget rejection")
  assertTrue ((limited.lookup Core.Word.zero).isNone) "zero resolved as a metadata ID"
  assertTrue ((limited.lookup ⟨99, by decide⟩).isNone) "unregistered metadata ID resolved"
  assertTrue ((idAt? (Core.wordModulus - 1)).isNone) "metadata ID wrapped at the word modulus"
  IO.println "raw metadata static prefixes, authenticated extensions and exact identity GREEN"

end Tests.SourceCoreRawMetadata
