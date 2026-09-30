import Solcore.Frontend.SourceCoreGeneralFunctions

#check_failure Solcore.Frontend.SourceTypedRuntime.run

set_option autoImplicit false

namespace Tests.SourceCoreDataPlaces

open Solcore Solcore.Frontend Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def w (value : Nat) : Core.Value := .word (Core.Word.ofNatModulo value)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Tree { Leaf(Word), Pair(Tree, Tree) }",
    "function order() returns (Word) {",
    " let table: mapping(Word => Word); let calls: Word = 0;",
    " let key: function() returns (Word) = lam() -> Word { calls += 1; table[1] = 10; return 1; };",
    " let rhs: function() returns (Word) = lam() -> Word { table[1] = 100; table[2] = 50; return 3; };",
    " table[key()] += rhs(); return table[1] + table[2] + calls; }",
    "function nested() returns (Word) {",
    " let table: mapping(Word => mapping(Word => Word)); let calls: Word = 0;",
    " let first: function() returns (Word) = lam() -> Word { calls += 1; table[1][2] = 10; return 1; };",
    " let second: function() returns (Word) = lam() -> Word { calls += 1; table[1][2] = 20; return 2; };",
    " let rhs: function() returns (Word) = lam() -> Word { table[1][2] = 100; table[1][3] = 7; table[9][9] = 11; return 5; };",
    " table[first()][second()] += rhs(); return table[1][2] + table[1][3] + table[9][9] + calls; }",
    "function replaceLatest() returns (Word) {",
    " let table: mapping(Word => Word); table[1] = 10;",
    " let rhs: function() returns (Word) = lam() -> Word { let fresh: mapping(Word => Word); fresh[3] = 9; table = fresh; return 4; };",
    " table[1] += rhs(); return table[1] + table[3]; }",
    "function ordered(table: mapping(Word => Word)) returns (mapping(Word => Word)) { table[7] = 80; table[9] = 90; return table; }",
    "function unary() returns (Word) { let table: mapping(Word => Word); table[1] = 0; table[1] ~=; return table[1]; }",
    "function header() returns (Word) { let table: mapping(Word => Word); for (let i: Word = 0; i < 3; table[i] += 2, i += 1) { table[i] = i; } return table[0] + table[1] + table[2]; }",
    "function absentDefault() returns (Word) {",
    " let table: mapping(Word => Tree); let count: Word = 0;",
    " let key: function() returns (Word) = lam() -> Word { count += 17; return 1; };",
    " let rhs: function() returns (Tree) = lam() -> Tree { count += 111; return .Leaf(7); };",
    " table[key()] = rhs(); return count; }",
    "function rhsFailure() returns (Word) { let table: mapping(Word => Word); let missing: Word; table[1] += missing; return 0; }"
  ] }]
}

private def entryFor (program : CheckedProgram) (checked : SourceCoreDataCatalog.Checked) (name : String) :
    IO (SourceCoreGeneralEntry.Entry checked) := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"place function missing: {name}")
  let plan ← match SourceSpecializationWorklist.run program
      [{ declaration := signature.id, parameterSubstitution := [] }] 256 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"place specialization failed: {reprStr result}")
  match SourceCoreGeneralFunctions.prepareWithCatalog program plan checked 256 with
  | .ok prepared => match prepared.entries with
      | [entry] => pure entry
      | _ => throw (IO.userError "place seed count changed")
  | .error error => throw (IO.userError s!"{name} place compilation failed: {reprStr error}")

private def expect {checked : SourceCoreDataCatalog.Checked} (entry : SourceCoreGeneralEntry.Entry checked)
    (inputs : List Core.Value) (expected : Core.Value) : IO Unit := do
  match entry.run inputs 65536 with
  | .ok result => match result.observation with
      | .succeeded actual _ =>
        assertTrue (actual == expected) s!"place result changed: {reprStr actual}; expected {reprStr expected}"
      | other => throw (IO.userError s!"place run failed: {reprStr other}")
  | .error error => throw (IO.userError s!"place input rejected: {reprStr error}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"place source rejected: {reprStr error}")
  let tree ← match program.signatures.dataTypes.filter (·.name == "Tree") with
    | [tree] => pure tree
    | _ => throw (IO.userError "place Tree missing")
  let treeType := TypeSystem.Ty.nominal tree.id []
  let checked ← match SourceCoreDataCatalog.prepare program.signatures 256
      [treeType, .mapping .word .word, .mapping .word (.mapping .word .word), .mapping .word treeType] with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"place catalog rejected: {reprStr error}")
  expect (← entryFor program checked "order") [] (w 64)
  let nested ← entryFor program checked "nested"
  expect nested [] (w 45)
  match nested.run [] 32 with
  | .ok result => match result.checkpoint? with
      | some checkpoint => match (checkpoint.resume 65536).observation with
          | .succeeded actual _ => assertTrue (actual == w 45) "place resume repeated keys or lost latest root"
          | other => throw (IO.userError s!"place resume failed: {reprStr other}")
      | none => throw (IO.userError "place run did not suspend")
  | .error error => throw (IO.userError s!"place checkpoint rejected: {reprStr error}")
  expect (← entryFor program checked "replaceLatest") [] (w 23)
  let mapId ← match checked.catalog.identity? (.mapping .word .word) with
    | some identity => pure identity
    | none => throw (IO.userError "place mapping identity missing")
  let layout : Core.OrderedMapping.Layout := ⟨.word, .word, mapId⟩
  expect (← entryFor program checked "ordered")
    [Core.OrderedMapping.encode layout [(w 7, w 1), (w 7, w 2), (w 3, w 4)]]
    (Core.OrderedMapping.encode layout [(w 7, w 80), (w 7, w 2), (w 3, w 4), (w 9, w 90)])
  expect (← entryFor program checked "unary") [] (.word (Core.Word.bitNot (Core.Word.ofNatModulo 0)))
  expect (← entryFor program checked "header") [] (w 9)
  let failing ← entryFor program checked "absentDefault"
  let treeMap ← match checked.catalog.identity? (.mapping .word treeType) with
    | some identity => pure identity
    | none => throw (IO.userError "place Tree mapping identity missing")
  match failing.run [] 65536 with
  | .ok result => match result.observation with
      | .failed reason store => do
          match failing.failureDiagnostic? reason with
          | some diagnostic =>
            assertTrue
              (decide (diagnostic.error = .typeMismatch treeType none) && diagnostic.span.isSome)
              "place missing default lost its exact source diagnostic"
          | none => throw (IO.userError "place missing default lost diagnostic")
          assertTrue (store.contains (.inRight .unit (w 17)) && !store.contains (.inRight .unit (w 128)))
            "place selected after RHS or skipped key effects"
          assertTrue (store.contains (.inLeft (.namedData treeMap) .unit) &&
            !store.contains (.inRight .unit (.constructed ⟨treeMap, 0⟩ .unit)))
            "failed place resolution initialized the mapping root"
      | other => throw (IO.userError s!"place missing default result changed: {reprStr other}")
  | .error error => throw (IO.userError s!"place failing entry rejected: {reprStr error}")
  let rhsFailure ← entryFor program checked "rhsFailure"
  match rhsFailure.run [] 65536 with
  | .ok result => match result.observation with
      | .failed reason store => do
          match rhsFailure.failureDiagnostic? reason with
          | some diagnostic =>
            assertTrue (match diagnostic.error with | .uninitializedLocal _ => true | _ => false)
              "projected assignment replaced RHS failure with operand failure"
          | none => throw (IO.userError "projected RHS failure lost diagnostic")
          assertTrue (store.contains (.inLeft layout.type .unit) &&
            !store.contains (.inRight .unit (Core.OrderedMapping.encode layout [])))
            "RHS failure materialized an empty mapping"
      | other => throw (IO.userError s!"projected RHS failure changed: {reprStr other}")
  | .error error => throw (IO.userError s!"projected RHS input rejected: {reprStr error}")
  IO.println "source Core structural mapping places GREEN"

end Tests.SourceCoreDataPlaces
