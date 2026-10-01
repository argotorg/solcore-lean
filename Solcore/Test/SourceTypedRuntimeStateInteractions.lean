import Solcore.Test.SourceCoreUnifiedCorpusSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-!
End-to-end regressions for interactions between typed source execution,
polymorphism, trait evidence, coercions, closures, mutable cells, mappings,
and proxies.

Each case enters through the raw-workspace checker, builds the finite
specialization plan, and caches its Core artifact before execution. The fixtures
use only source forms supported by the upstream Solcore frontend; in particular,
proxy values are used as mapping keys rather than treating enum payloads as
named fields.
-/

set_option autoImplicit false

namespace Tests.SourceTypedRuntimeStateInteractions

open Solcore Solcore.Frontend Solcore.TypeSystem

namespace Runtime

open Solcore.Frontend.SourceTypedRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word :=
  Core.Word.ofNatModulo value

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def checkedProgram (content : String) : IO CheckedProgram := do
  match checkProgram (workspace content) with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"state-interaction fixture failed checking: {reprStr errors}")

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

private def prepareNamed (program : CheckedProgram) (name : String)
    (budget : Nat := 64) : IO Prepared := do
  let signature ← signatureNamed program name
  let request : SourceSpecializationWorklist.Request := {
    declaration := signature.id
    parameterSubstitution := []
  }
  match SourceSpecializationWorklist.run program [request] budget with
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
    (arguments : List Value := []) (fuel : Nat := 300000) : IO RunResult :=
  SourceCoreUnifiedCorpusSupport.observe prepared.compiled prepared.key arguments fuel

private def expectWordAndShallowHeap (label : String) (expected : Nat)
    (plan : SourceSpecializationWorklist.Plan) : RunResult → IO Unit
  | .done (.word actual) state => do
      assertTrue (actual == word expected) s!"{label} returned the wrong Word"
      for cell in state.heap do
        match cell.value with
        | none => pure ()
        | some value =>
            assertTrue (decide (value.type? plan = some cell.type))
              s!"{label} left an initialized cell with a mismatched type"
  | result => throw (IO.userError s!"{label} returned {reprStr result}")

private def source : String := String.intercalate "\n" [
  "trait Witness<T> {}",
  "impl Witness<Word> {}",
  "function retain<T>(value: T) returns (T) where T: Witness {",
  "  return value;",
  "}",
  "function mutateCaptured<T>(value: T, key: Word) returns (Word)",
  "    where T: Witness {",
  "  let total: Word = 1;",
  "  let table: mapping(Word => Word);",
  "  let mutate = lam(item: T) -> Word {",
  "    let checked: T = retain(item);",
  "    total += 2;",
  "    table[key] = total;",
  "    return table[key];",
  "  };",
  "  let fromCall: Word = mutate(value);",
  "  return fromCall + total + table[key];",
  "}",
  "function capturedStateEntry(value: Word) returns (Word) {",
  "  return mutateCaptured(value, 7);",
  "}",
  "trait Coerce<From, To> {",
  "  function coerce(value: From) returns (To);",
  "}",
  "impl Coerce<Bool, Word> {",
  "  function coerce(value: Bool) returns (Word) {",
  "    let scratch: mapping(Word => Word);",
  "    scratch[0] = value ? 40 : 6;",
  "    scratch[0] += 2;",
  "    return scratch[0];",
  "  }",
  "}",
  "impl Coerce<Bool, function() returns(Word)> {",
  "  function coerce(value: Bool) returns (function() returns(Word)) {",
  "    let scratch: mapping(Word => Word);",
  "    scratch[0] = value ? 40 : 6;",
  "    return lam() -> Word {",
  "      scratch[0] += 2;",
  "      return scratch[0];",
  "    };",
  "  }",
  "}",
  "function coercionMapping(value: Bool) returns (Word) {",
  "  let output: mapping(Word => Word);",
  "  output[3] = value;",
  "  return output[3];",
  "}",
  "function coercionResult(value: Bool) returns (Word) {",
  "  return value;",
  "}",
  "function coercionCapturedState(value: Bool) returns (Word) {",
  "  let next: function() returns(Word) = value;",
  "  return next() + next();",
  "}",
  "function genericProxyKey<T>(value: T) returns (Word) {",
  "  let table: mapping(@T => Word);",
  "  table[@T] = 73;",
  "  return table[@T];",
  "}",
  "function proxyKeyEntry(value: Word) returns (Word) {",
  "  return genericProxyKey(value);",
  "}",
  "function recurseClosure<T>(value: T, count: Word) returns (T)",
  "    where T: Witness {",
  "  let loop: function(T, Word) returns (T);",
  "  loop = lam(current: T, remaining: Word) -> T {",
  "    return remaining == 0 ? retain(current) :",
  "      loop(current, remaining - 1);",
  "  };",
  "  return loop(value, count);",
  "}",
  "function recursiveClosureEntry(value: Word) returns (Word) {",
  "  return recurseClosure(value, 3);",
  "}"
]

private def testGenericConstrainedCapturedState
    (program : CheckedProgram) : IO Unit := do
  let prepared ← prepareNamed program "capturedStateEntry"
  expectWordAndShallowHeap "generic constrained captured mutation" 9
    prepared.plan (← runPrepared prepared [.word (word 19)])

private def testStatefulCoercionMethod
    (program : CheckedProgram) : IO Unit := do
  let mapping ← prepareNamed program "coercionMapping"
  expectWordAndShallowHeap "stateful coercion in mapping assignment (true)" 42
    mapping.plan (← runPrepared mapping [.bool true])
  expectWordAndShallowHeap "stateful coercion in mapping assignment (false)" 8
    mapping.plan (← runPrepared mapping [.bool false])

  let result ← prepareNamed program "coercionResult"
  expectWordAndShallowHeap "stateful coercion in function result (true)" 42
    result.plan (← runPrepared result [.bool true])
  expectWordAndShallowHeap "stateful coercion in function result (false)" 8
    result.plan (← runPrepared result [.bool false])

  let captured ← prepareNamed program "coercionCapturedState"
  expectWordAndShallowHeap "coercion closure preserves method state (true)" 86
    captured.plan (← runPrepared captured [.bool true])
  expectWordAndShallowHeap "coercion closure preserves method state (false)" 18
    captured.plan (← runPrepared captured [.bool false])

private def testGenericProxyMappingKey
    (program : CheckedProgram) : IO Unit := do
  let prepared ← prepareNamed program "proxyKeyEntry"
  expectWordAndShallowHeap "generic proxy mapping key" 73
    prepared.plan (← runPrepared prepared [.word (word 5)])

private def testRecursiveClosureSelfCellAndEvidence
    (program : CheckedProgram) : IO Unit := do
  let prepared ← prepareNamed program "recursiveClosureEntry"
  expectWordAndShallowHeap "recursive closure self-cell and evidence" 67
    prepared.plan (← runPrepared prepared [.word (word 67)])

private def testAll : IO Unit := do
  let program ← checkedProgram source
  testGenericConstrainedCapturedState program
  testStatefulCoercionMethod program
  testGenericProxyMappingKey program
  testRecursiveClosureSelfCellAndEvidence program
  IO.println "cached Core source state interactions GREEN"

end Runtime

/-- Exercise stateful interactions through checked source-compatible Core code. -/
def testSourceTypedRuntimeStateInteractions : IO Unit :=
  Runtime.testAll

end Tests.SourceTypedRuntimeStateInteractions
