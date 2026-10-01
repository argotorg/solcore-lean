import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.Frontend.SourceCorePlanCatalog

/-! Grouped tuple regressions cross the parser, checker and specialization
boundary. Both the public session and the internal prepared body execute Core and
preserve transparent tuple groups, pattern binding and evaluation order. -/

set_option autoImplicit false

namespace Tests.SourceCoreGroupedTuple

open Solcore Solcore.Frontend Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def w (value : Nat) : Core.Word := Core.Word.ofNatModulo value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function plain(left: Word, right: Word) returns (Word) { match ((left, right)) { case (x, y) { return x; } default { return 99; } } }",
    "function grouped(left: Word, right: Word) returns (Word) { match ((left, right)) { case ((x, y)) { return x; } default { return 99; } } }",
    "function deep(left: Word, right: Word) returns (Word) { match ((left, right)) { case ((((x, y)))) { return x; } default { return 99; } } }",
    "function nested(left: Word, right: Word) returns (Word) { match ((left, (true, right))) { case (((x, (flag, y)))) { return flag ? x + y : 0; } default { return 99; } } }",
    "function three(left: Word, right: Word) returns (Word) { match ((left, true, right)) { case (((x, flag, y))) { return flag ? x + y : 0; } default { return 99; } } }",
    "function tripleEffects(left: Word, right: Word) returns (Word) { let count: Word = 0; let next = lam() -> Word { count += 1; return count; }; match ((next(), next(), next())) { case (x, y, z) { return x + y + z + count; } default { return 99; } } }",
    "function unitValue(value: Unit) returns (Word) { match (value) { case ((())) { return 7; } default { return 99; } } }",
    "function chooseArm(left: Word, right: Word) returns (Word) { match ((left, right)) { case ((0, y)) { return y; } case (((x, y))) { return x; } default { return 99; } } }",
    "function effects(left: Word, right: Word) returns (Word) { let count: Word = 0;",
    " match ((lam() -> (Word, Word) { count += 1; return (left, right); })()) {",
    " case (((x, y))) { count += x; } default { count += 99; } } return count; }"
  ]}]
}

private def coreEntry (program : CheckedProgram) (name : String) : IO SourceCorePlanCatalog.Prepared := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"grouped tuple root missing: {name}")
  let plan ← match SourceSpecializationWorklist.run program
      [{declaration := signature.id, parameterSubstitution := []}] 256 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"grouped tuple plan failed: {reprStr result}")
  match SourceCorePlanCatalog.prepare program plan 256 with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError s!"grouped tuple Core compilation failed: {reprStr error}")

private def test (program : CheckedProgram) (name : String) (inputs : List Core.Value)
    (sourceInputs : List SourceCoreExecution.Value) (expected : Nat) : IO Unit := do
  let prepared ← coreEntry program name
  let entry ← match prepared.program.entries with
    | [entry] => pure entry
    | _ => throw (IO.userError "grouped tuple Core entry count changed")
  for _ in [0, 1] do
    match entry.run inputs 32768 with
    | .ok result => match result.observation with
        | .succeeded (.word actual) _ => assertTrue (actual == w expected) s!"{name} Core tuple result changed"
        | result => throw (IO.userError s!"{name} Core tuple run failed: {reprStr result}")
    | .error error => throw (IO.userError s!"{name} Core tuple input failed: {reprStr error}")
  let compiled ← SourceCompilerFeatureSupport.compileNamed program name
  assertTrue ((← compiled.run sourceInputs) == .word (w expected)) s!"{name} public tuple grouping changed"
  compiled.checkResume sourceInputs (.word (w expected)) 0
  match entry.run inputs 0 with
  | .ok result => match result.checkpoint? with
      | some checkpoint => match (checkpoint.resume 32768).observation with
          | .succeeded (.word actual) _ => assertTrue (actual == w expected) s!"{name} tuple resume changed the result"
          | result => throw (IO.userError s!"{name} tuple resume failed: {reprStr result}")
      | none => throw (IO.userError "grouped tuple zero fuel did not suspend")
  | .error error => throw (IO.userError s!"{name} tuple checkpoint input failed: {reprStr error}")

def run : IO Unit := do
  let program ← match checkProgram workspace 4096 with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"grouped tuple source rejected: {reprStr error}")
  let signature ← match program.signatures.functions.filter (·.name == "grouped") with
    | [signature] => pure signature
    | _ => throw (IO.userError "grouped tuple signature missing")
  let function ← match program.functions.filter (fun function => decide (function.declaration = signature.id)) with
    | [function] => pure function
    | _ => throw (IO.userError "grouped tuple checked body missing")
  assertTrue (function.typedBody.nodes.any fun
    | .statement node => match node.form with
        | .matchWith resolution => resolution.cases.any fun arm => match arm.pattern.source with
            | .group _ (.tuple _ 2) => true
            | _ => false
        | _ => false
    | _ => false) "regression did not retain the actual grouped tuple source"
  for (name, expected) in [("plain", 7), ("grouped", 7), ("deep", 7), ("nested", 15), ("three", 15), ("tripleEffects", 9), ("chooseArm", 7), ("effects", 8)] do
    test program name [.word (w 7), .word (w 8)] [.word (w 7), .word (w 8)] expected
  test program "chooseArm" [.word (w 0), .word (w 8)] [.word (w 0), .word (w 8)] 8
  test program "unitValue" [.unit] [.unit] 7
  IO.println "source Core grouped tuple patterns GREEN"

end Tests.SourceCoreGroupedTuple
