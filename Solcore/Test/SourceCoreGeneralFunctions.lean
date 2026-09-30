import Solcore.Frontend.SourceCoreGeneralFunctions

#check_failure Solcore.Frontend.SourceTypedRuntime.run

set_option autoImplicit false

namespace Tests.SourceCoreGeneralFunctions

open Solcore Solcore.Frontend Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Core.Value := .word (Core.Word.ofNatModulo value)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Tree { Leaf(Word), Pair(Tree, Tree) }",
    "function leaf(value: Word) returns (Tree) { return .Leaf(value); }",
    "function branch(left: Tree, right: Tree) returns (Tree) { return .Pair(left, right); }",
    "function choose(flag: Bool, value: Word) returns (Tree) { return flag ? leaf(value) : .Pair(leaf(value), leaf(value + 1)); }",
    "function mutate(value: Tree, replacement: Tree) returns (Tree) {",
    " let setter: function(Tree) returns (Tree) = lam(next: Tree) -> Tree { value = next; return value; };",
    " setter(replacement); return value; }",
    "function transform(value: Tree, change: function(Tree) returns (Tree)) returns (Tree) { return change(value); }",
    "function through(value: Tree) returns (Tree) { return transform(value, lam(input: Tree) -> Tree { return .Pair(input, input); }); }",
    "function recurse(count: Word, value: Tree) returns (Tree) { return count == 0 ? value : recurse(count - 1, Tree.Pair(value, value)); }",
    "function proxyValue() returns (@Word) { return @Word; }",
    "function find(table: mapping(Word => Word), key: Word) returns (Word) { return table[key]; }",
    "function empty() returns (Word) { let table: mapping(Word => Word); return table[1]; }",
    "function missing(table: mapping(Word => Tree), key: Word) returns (Tree) { return table[key]; }",
    "function absent() returns (Tree) { let value: Tree; return value; }"
    , "function select(value: Tree) returns (Word) { match (value) { case .Leaf(x) { return x; } case .Pair(.Leaf(left), .Leaf(right)) { return left + right; } default { return 0; } } }"
    , "function patternCall(value: Tree) returns (Word) { let out: Word; match (value) { case .Leaf(x) { let f: function() returns (Word) = lam() -> Word { return x; }; out = f(); } default { out = 0; } } return out; }"
    , "function matchContinue(value: Tree) returns (Word) { let count: Word = 0; while (count < 2) { count += 1; match (value) { case .Leaf(x) { continue; } default { break; } } count += 10; } return count; }"
  ] }]
}

private def entryFor (program : CheckedProgram) (checked : SourceCoreDataCatalog.Checked) (name : String) :
    IO (SourceCoreGeneralEntry.Entry checked) := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"general function missing: {name}")
  let plan ← match SourceSpecializationWorklist.run program
      [{ declaration := signature.id, parameterSubstitution := [] }] 256 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"general plan failed: {reprStr result}")
  match SourceCoreGeneralFunctions.prepareWithCatalog program plan checked 256 with
  | .ok prepared => match prepared.entries with
      | [entry] => pure entry
      | _ => throw (IO.userError "general seed count changed")
  | .error error => throw (IO.userError s!"{name} general compilation failed: {reprStr error}")

private def expect {checked : SourceCoreDataCatalog.Checked} (entry : SourceCoreGeneralEntry.Entry checked)
    (arguments : List Core.Value) (expected : Core.Value) : IO Unit := do
  for _ in [0, 1] do
    match entry.run arguments 32768 with
    | .ok result => match result.observation with
        | .succeeded actual _ => assertTrue (actual == expected) s!"general function result changed: {reprStr actual}"
        | observation => throw (IO.userError s!"general function failed: {reprStr observation}")
    | .error error => throw (IO.userError s!"general input rejected: {reprStr error}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"general source rejected: {reprStr error}")
  let tree ← match program.signatures.dataTypes.filter (·.name == "Tree") with
    | [tree] => pure tree
    | _ => throw (IO.userError "Tree signature missing")
  let treeType := TypeSystem.Ty.nominal tree.id []
  let checked ← match SourceCoreDataCatalog.prepare program.signatures 256
      [treeType, .mapping .word .word, .mapping .word treeType, .proxy .word,
       .function treeType treeType] with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"general catalog failed: {reprStr error}")
  let treeId ← match checked.catalog.identity? treeType with
    | some id => pure id
    | none => throw (IO.userError "Tree Core identity missing")
  let leaf := fun value => Core.Value.constructed ⟨treeId, 0⟩ (word value)
  let pair := fun left right => Core.Value.constructed ⟨treeId, 1⟩ (.pair left right)
  expect (← entryFor program checked "leaf") [word 17] (leaf 17)
  expect (← entryFor program checked "branch") [leaf 2, leaf 3] (pair (leaf 2) (leaf 3))
  let choose ← entryFor program checked "choose"
  expect choose [.bool true, word 9] (leaf 9)
  expect choose [.bool false, word 9] (pair (leaf 9) (leaf 10))
  expect (← entryFor program checked "mutate") [leaf 1, pair (leaf 8) (leaf 9)] (pair (leaf 8) (leaf 9))
  expect (← entryFor program checked "through") [leaf 7] (pair (leaf 7) (leaf 7))
  let recursive ← entryFor program checked "recurse"
  let twice := pair (leaf 4) (leaf 4)
  expect recursive [word 2, leaf 4] (pair twice twice)
  match recursive.run [word 2, leaf 4] 8 with
  | .ok result => match result.checkpoint? with
      | some checkpoint =>
          match (checkpoint.resume 32768).observation with
          | .succeeded actual _ => assertTrue (actual == pair twice twice) "general checkpoint lost recursive data"
          | other => throw (IO.userError s!"general resume failed: {reprStr other}")
      | none => throw (IO.userError "general recursion did not suspend")
  | .error error => throw (IO.userError s!"general checkpoint input rejected: {reprStr error}")
  let proxy ← match checked.catalog.proxyValue? .word with
    | some value => pure value
    | none => throw (IO.userError "proxy representation missing")
  expect (← entryFor program checked "proxyValue") [] proxy
  let mapId ← match checked.catalog.identity? (.mapping .word .word) with
    | some id => pure id
    | none => throw (IO.userError "mapping representation missing")
  let layout : Core.OrderedMapping.Layout := ⟨.word, .word, mapId⟩
  let find ← entryFor program checked "find"
  let mapping := Core.OrderedMapping.encode layout [(word 3, word 41), (word 7, word 99)]
  expect find [mapping, word 7] (word 99)
  expect find [mapping, word 8] (word 0)
  let empty ← entryFor program checked "empty"
  expect empty [] (word 0)
  match empty.run [] 32768 with
  | .ok result => match result.observation with
      | .succeeded _ store =>
          assertTrue (store.contains (.inRight .unit (Core.OrderedMapping.encode layout [])))
            "uninitialized mapping read did not install its empty value"
      | other => throw (IO.userError s!"empty mapping failed: {reprStr other}")
  | .error error => throw (IO.userError s!"empty mapping input failed: {reprStr error}")
  let missing ← entryFor program checked "missing"
  let emptyTreeMap ← match checked.catalog.emptyMapping? .word treeType with
    | some value => pure value
    | none => throw (IO.userError "Tree mapping representation missing")
  match missing.run [emptyTreeMap, word 2] 32768 with
  | .ok result => match result.observation with
      | .failed reason _ => match missing.failureDiagnostic? reason with
          | some diagnostic =>
              assertTrue (decide (diagnostic.error = .typeMismatch treeType none) && diagnostic.span.isSome)
                "missing mapping default lost its error or source span"
          | none => throw (IO.userError "missing mapping default lost its diagnostic")
      | other => throw (IO.userError s!"missing mapping default changed: {reprStr other}")
  | .error error => throw (IO.userError s!"missing mapping input failed: {reprStr error}")
  let absent ← entryFor program checked "absent"
  match absent.run [] 32768 with
  | .ok result => match result.observation with
      | .failed reason _ => assertTrue ((absent.failureDiagnostic? reason).isSome) "nominal absence lost diagnostic"
      | other => throw (IO.userError s!"nominal absence changed: {reprStr other}")
  | .error error => throw (IO.userError s!"nominal absence input failed: {reprStr error}")
  let select ← entryFor program checked "select"
  expect select [leaf 7] (word 7)
  expect select [pair (leaf 8) (leaf 9)] (word 17)
  expect select [pair (pair (leaf 1) (leaf 2)) (leaf 3)] (word 0)
  expect (← entryFor program checked "patternCall") [leaf 42] (word 42)
  let matchContinue ← entryFor program checked "matchContinue"
  expect matchContinue [leaf 7] (word 2)
  expect matchContinue [pair (leaf 7) (leaf 8)] (word 1)
  IO.println "general Core functions with recursive data GREEN"

end Tests.SourceCoreGeneralFunctions
