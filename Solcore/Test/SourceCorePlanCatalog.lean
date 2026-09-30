import Solcore.Frontend.SourceCorePlanCatalog
import Solcore.Frontend.SourceCoreDataValues

#check_failure Solcore.Frontend.SourceTypedRuntime.run

set_option autoImplicit false

namespace Tests.SourceCorePlanCatalog

open Solcore Solcore.Frontend Solcore.Core
abbrev SourceValue := SourceCoreDataValues.Value

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Tree<T> { Leaf(T), Pair(Tree<T>, Tree<T>) }",
    "function leaf(value: Word) returns (Tree<Word>) { return .Leaf(value); }",
    "function main(flag: Bool, value: Word) returns (Tree<Word>) { return flag ? leaf(value) : .Pair(leaf(value), leaf(value + 1)); }",
    "function recursive(count: Word, value: Tree<Word>) returns (Tree<Word>) { return count == 0 ? value : recursive(count - 1, Tree.Pair(value, value)); }",
    "function mappingValue(table: mapping(Word => Word)) returns (mapping(Word => Word)) { table[7] += 3; return table; }",
    "function proxyValue() returns (@Tree<Word>) { return @Tree<Word>; }"
  ] }]
}

private def preparedFor (program : CheckedProgram) (name : String) : IO SourceCorePlanCatalog.Prepared := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"automatic catalog function missing: {name}")
  let plan ← match SourceSpecializationWorklist.run program
      [{ declaration := signature.id, parameterSubstitution := [] }] 256 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"automatic catalog specialization failed: {reprStr result}")
  match SourceCorePlanCatalog.prepare program plan 256 with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError s!"automatic catalog preparation failed: {reprStr error}")

private def execute (signatures : ProgramSignatures) (prepared : SourceCorePlanCatalog.Prepared)
    (arguments : List SourceValue) : IO SourceValue := do
  let entry ← match prepared.program.entries with
    | [entry] => pure entry
    | _ => throw (IO.userError "automatic catalog seed count changed")
  let context : SourceCoreDataValues.Context := ⟨prepared.checked, signatures⟩
  let arguments ← (entry.inputs.zip arguments).mapM fun (input, argument) => do
    match SourceCoreDataValues.encode 256 context input.sourceType argument with
    | .ok core => pure core
    | .error error => throw (IO.userError s!"source input rejected: {reprStr error}")
  match entry.run arguments 65536 with
  | .ok result => match result.observation with
      | .succeeded value _ => match SourceCoreDataValues.decode 256 context entry.sourceResultType value with
          | .ok value => pure value
          | .error error => throw (IO.userError s!"source result rejected: {reprStr error}")
      | other => throw (IO.userError s!"automatic catalog execution failed: {reprStr other}")
  | .error error => throw (IO.userError s!"automatic catalog native input rejected: {reprStr error}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"automatic catalog source rejected: {reprStr error}")
  let tree ← match program.signatures.dataTypes.filter (·.name == "Tree") with
    | [tree] => pure tree
    | _ => throw (IO.userError "automatic Tree signature missing")
  let treeType := TypeSystem.Ty.nominal tree.id [.word]
  let substitution := tree.parameters.zip [TypeSystem.Ty.word]
  let metadata := fun index payload => SourceInference.DataConstructorInstantiation.mk
    ⟨tree.id, index⟩ substitution payload treeType
  let word := fun value => SourceCoreDataValues.Value.word (Core.Word.ofNatModulo value)
  let leaf := fun value => SourceCoreDataValues.Value.constructed (metadata 0 [.word]) [word value]
  let pair := fun left right => SourceCoreDataValues.Value.constructed (metadata 1 [treeType, treeType]) [left, right]
  let main ← preparedFor program "main"
  for _ in [0, 1] do
    assertTrue (decide ((← execute program.signatures main [.bool true, word 8]) = leaf 8))
      "automatically discovered nominal output changed"
    assertTrue (decide ((← execute program.signatures main [.bool false, word 8]) = pair (leaf 8) (leaf 9)))
      "automatically discovered recursive payload changed"
  let recursive ← preparedFor program "recursive"
  assertTrue (decide ((← execute program.signatures recursive [word 2, leaf 3]) =
    pair (pair (leaf 3) (leaf 3)) (pair (leaf 3) (leaf 3))))
    "automatic recursive catalog lost constructor identity"
  let mapping ← preparedFor program "mappingValue"
  let entries := [(word 7, word 4), (word 7, word 99), (word 2, word 6)]
  assertTrue (decide ((← execute program.signatures mapping [.mapping .word .word entries]) =
    .mapping .word .word [(word 7, word 7), (word 7, word 99), (word 2, word 6)]))
    "automatic ordered mapping changed duplicate positions"
  assertTrue (decide ((← execute program.signatures (← preparedFor program "proxyValue") []) = .proxy treeType))
    "automatic catalog lost proxy inner type"
  let context : SourceCoreDataValues.Context := ⟨recursive.checked, program.signatures⟩
  assertTrue (match SourceCoreDataValues.encode 256 context treeType
      (.constructed (metadata 0 [.word]) [.integer 3]) with | .error _ => true | _ => false)
    "source input adapter accepted a forged nominal payload"
  IO.println "source Core automatic plan catalogs GREEN"

end Tests.SourceCorePlanCatalog
