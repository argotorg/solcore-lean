import Solcore.Test.SourceCoreUnifiedCorpusSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Checked-source regressions for evidence-bearing first-class functions,
executed through a cached source-compatible Core artifact. -/

set_option autoImplicit false

namespace Tests.SourceTypedRuntimeFirstClassEvidence

open Solcore Solcore.Frontend Solcore.TypeSystem
open Solcore.Frontend.SourceTypedRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word :=
  Core.Word.ofNatModulo value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{
    path := "main.solc"
    content := String.intercalate "\n" [
      "trait Eq<T> {}",
      "impl Eq<Word> {}",
      "trait Mark<T> {}",
      "impl Mark<Word> {}",
      "function keep<T>(value: T) returns (T) where T: Eq { return value; }",
      "function keepBoth<T>(value: T) returns (T) where T: Eq, T: Mark { return value; }",
      "function globalValue() returns (function(Word) returns (Word)) {",
      "  return keep;",
      "}",
      "function globalAliasCall(value: Word) returns (Word) {",
      "  let alias: function(Word) returns(Word) = keep;",
      "  return alias(value);",
      "}",
      "function orderedFactory<T>(witness: T) returns (function(T) returns (T)) where T: Mark, T: Eq {",
      "  return keepBoth;",
      "}",
      "function orderedAliasCall(value: Word) returns (Word) {",
      "  let alias = orderedFactory(value);",
      "  return alias(value);",
      "}",
      "function localFactory<T>(witness: T) returns (function(T) returns (T)) where T: Eq {",
      "  let f = lam(value) { return keep(value); };",
      "  let alias: function(T) returns(T) = f;",
      "  return alias;",
      "}",
      "function qualifiedLocalAliasCall(value: Word) returns (Word) {",
      "  let alias = localFactory(value);",
      "  return alias(value);",
      "}",
      "function repeat<T>(value: T, count: Word) returns (T) where T: Eq {",
      "  return count == 0 ? value : repeat(value, count - 1);",
      "}",
      "function recursiveClosure<T>(witness: T) returns (function(T, Word) returns (T)) where T: Eq {",
      "  let invoke = lam(value: T, count: Word) -> T { return repeat(value, count); };",
      "  return invoke;",
      "}",
      "function genericRecursiveClosureCall(value: Word) returns (Word) {",
      "  let invoke = recursiveClosure(value);",
      "  return invoke(value, 3);",
      "}",
      "function applyStored(f: function(Word) returns(Word), value: Word) returns (Word) {",
      "  let retained: function(Word) returns(Word) = keep;",
      "  return f(value);",
      "}"
    ]
  }]
  externalLibraries := []
}

private def checkedProgram : IO CheckedProgram := do
  match checkProgram workspace with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"first-class evidence fixture failed checking: {reprStr errors}")

private def signatureNamed (program : CheckedProgram) (name : String) :
    IO ProgramFunctionSignature :=
  match program.signatures.functions.filter fun signature =>
      signature.name == name with
  | [signature] => pure signature
  | signatures => throw (IO.userError
      s!"expected one signature named `{name}`, found {signatures.length}")

private structure Prepared where
  program : CheckedProgram
  plan : SourceSpecializationWorklist.Plan
  key : SourceSpecialization.SpecializationKey
  compiled : SourceCoreUnifiedCompilation.Compiled

private def prepareNamed (program : CheckedProgram) (name : String) :
    IO Prepared := do
  let signature ← signatureNamed program name
  let request : SourceSpecializationWorklist.Request := {
    declaration := signature.id
    parameterSubstitution := []
  }
  match SourceSpecializationWorklist.run program [request] 32 with
  | .ok (.complete plan) =>
      match plan.seedKeys with
      | [key] => do
          let compiled ← SourceCoreUnifiedCorpusSupport.preparePlan name program plan key
          pure { program, plan, key, compiled }
      | keys => throw (IO.userError
          s!"`{name}` retained {keys.length} seed keys")
  | .ok outcome => throw (IO.userError
      s!"`{name}` specialization did not complete: {reprStr outcome}")
  | .error error => throw (IO.userError
      s!"`{name}` specialization failed: {reprStr error}")

private def runPrepared (prepared : Prepared)
    (arguments : List Value := []) : IO RunResult :=
  SourceCoreUnifiedCorpusSupport.observe prepared.compiled prepared.key arguments

private def expectWord (label : String) (expected : Nat) : RunResult → IO Unit
  | .done (.word actual) _ =>
      assertTrue (actual == word expected) s!"{label} returned the wrong Word"
  | result => throw (IO.userError s!"{label} returned {reprStr result}")

private def specializationNamed (prepared : Prepared) (name : String) :
    IO SourceSpecialization.SpecializedFunction := do
  let signature ← signatureNamed prepared.program name
  match prepared.plan.specializations.filter fun specialized =>
      specialized.declaration == signature.id with
  | [specialized] => pure specialized
  | specializations => throw (IO.userError
      s!"`{name}` retained {specializations.length} specializations")

private def testConstrainedGlobalValue (program : CheckedProgram) : IO Unit := do
  let valueFactory ← prepareNamed program "globalValue"
  assertTrue (valueFactory.plan.referenceEdges.length == 1)
    "constrained declaration value lost its reference edge"
  let (key, evidence) ← match ← runPrepared valueFactory with
    | .done (.global key evidence) _ => pure (key, evidence)
    | result => throw (IO.userError
        s!"globalValue returned {reprStr result}")
  let target ← match valueFactory.plan.specializations.filter fun specialized =>
      decide (specialized.key = key) with
    | [specialized] => pure specialized
    | specializations => throw (IO.userError
        s!"globalValue retained {specializations.length} reference targets")
  assertTrue (decide (evidence.goals = target.assumptions) &&
      evidence.length == 1)
    "constrained declaration value did not retain its ordered evidence"

  let aliasCall ← prepareNamed program "globalAliasCall"
  expectWord "constrained global alias" 41
    (← runPrepared aliasCall [.word (word 41)])

  let applyStored ← prepareNamed program "applyStored"
  expectWord "evidence-bearing global input" 49
    (← runPrepared applyStored [.global key evidence, .word (word 49)])
  match ← runPrepared applyStored [.global key [], .word (word 49)] with
  | .fault (.typeMismatch _ _) _ => pure ()
  | result => throw (IO.userError
      s!"global input with missing evidence was accepted: {reprStr result}")

private def testPredicateReordering (program : CheckedProgram) : IO Unit := do
  let prepared ← prepareNamed program "orderedAliasCall"
  let factory ← specializationNamed prepared "orderedFactory"
  let target ← specializationNamed prepared "keepBoth"
  assertTrue (factory.assumptions.length == 2 &&
      target.assumptions.length == 2 &&
      decide (factory.assumptions.reverse = target.assumptions))
    "predicate-reordering fixture lost its opposite declaration orders"
  expectWord "predicate-reordered declaration value" 43
    (← runPrepared prepared [.word (word 43)])

private def testQualifiedLocalAliasEscape
    (program : CheckedProgram) : IO Unit := do
  let prepared ← prepareNamed program "qualifiedLocalAliasCall"
  let factory ← specializationNamed prepared "localFactory"
  let forwarded := prepared.plan.callEdges.filter fun edge =>
    decide (edge.caller = factory.key)
  assertTrue (factory.assumptions.length == 1 &&
      forwarded.length == 1)
    "qualified local escape lost its caller assumption or forwarded call"
  expectWord "qualified local alias escape" 45
    (← runPrepared prepared [.word (word 45)])

private def testGenericRecursiveClosure
    (program : CheckedProgram) : IO Unit := do
  let prepared ← prepareNamed program "genericRecursiveClosureCall"
  let recursive ← specializationNamed prepared "repeat"
  let selfEdges := prepared.plan.callEdges.filter fun edge =>
    decide (edge.caller = recursive.key ∧ edge.callee = recursive.key)
  assertTrue (recursive.assumptions.length == 1 && selfEdges.length == 1)
    "escaped generic closure lost recursive evidence forwarding"
  expectWord "generic recursive closure" 47
    (← runPrepared prepared [.word (word 47)])

def testSourceTypedRuntimeFirstClassEvidence : IO Unit := do
  let program ← checkedProgram
  testConstrainedGlobalValue program
  testPredicateReordering program
  testQualifiedLocalAliasEscape program
  testGenericRecursiveClosure program

end Tests.SourceTypedRuntimeFirstClassEvidence
