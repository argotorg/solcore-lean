import Solcore

/-!
Whole-program rejection and resource-boundary regressions for direct
Core-representable staged calls.

Unlike the carrier-level tamper suite, these cases use only checked source and
the public preparation boundary.  They fix which unsupported call features
fail explicitly and ensure finite specialization does not make recursive
staged evaluation appear executable.
-/

set_option autoImplicit false

namespace Tests.SourceStagedValueCallsTamper

open Solcore Solcore.Frontend
open Solcore.Frontend.SourceProgramExecution

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def mainModule : IO Workspace.ModuleId := do
  match Workspace.CanonicalSourcePath.parse "main.solc" with
  | none => throw (IO.userError
      "invalid staged-value call boundary module path")
  | some canonical => pure {
      library := .main
      path := canonical.modulePath
    }

private def limits (specializationBudget : Nat) : Limits := {
  checkingFuel := 1024
  specializationBudget
  executionFuel := 4096
}

private def word (value : Nat) : Core.Word :=
  Core.Word.ofNatModulo value

private def predicateSource : String := String.intercalate "\n" [
  "trait Marker<T> {}",
  "impl Marker<Word> {}",
  "function marked<T>(comptime value: T) returns (comptime<T>) where T: Marker {",
  "  return value;",
  "}",
  "function relay<T>(comptime value: T) returns (comptime<T>) where T: Marker {",
  "  return marked(value);",
  "}",
  "function wrapper(comptime value: Word) returns (Word) where Word: Marker {",
  "  return relay(value);",
  "}",
  "function entry() returns (Word) { return wrapper(3); }"
]

private def testPredicateEvidenceForwarded : IO Unit := do
  let moduleId ← mainModule
  let prepared ← match prepare (workspace predicateSource)
      (Seed.named moduleId "entry") (limits 4) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"predicate-bearing marked calls failed: {reprStr error}")
  let store : Core.Store := [.bool false, .word (word 29)]
  assertTrue (decide (prepared.run? [] 4096 store =
      some (.done (.word (word 3)) store)))
    "proof-only staged call evidence changed the value or store"
  match prepared.entry.elaborated.resolved with
  | .letE temporary (.word argument)
      (.letE _ (.var reference) (.word result)) =>
      assertTrue (decide (temporary = reference ∧ argument = word 3 ∧
          result = word 3))
        "predicate-bearing nested staged result was not materialized"
  | resolved => throw (IO.userError
      s!"predicate-bearing staged calls have the wrong shape: {reprStr resolved}")

private def coercionSource : String := String.intercalate "\n" [
  "trait Coerce<From, To> {",
  "  function coerce(value: From) returns (To);",
  "}",
  "impl Coerce<Bool, Word> {",
  "  function coerce(value: Bool) returns (Word) {",
  "    return value ? 41 : 7;",
  "  }",
  "}",
  "function staged() returns (comptime<Bool>) { return true; }",
  "function entry() returns (Word) { return staged(); }"
]

private def testResultCoercionRejected : IO Unit := do
  let moduleId ← mainModule
  match prepare (workspace coercionSource) (Seed.named moduleId "entry")
      (limits 2) with
  | .error (.linking (.sourceCore error)) =>
      match error.reason with
      | .coercionsPresent coercions =>
          assertTrue (!coercions.isEmpty)
            "result-coercion rejection lost its coercion path"
      | reason => throw (IO.userError
          s!"marked result coercion failed for the wrong reason: {reprStr reason}")
  | result => throw (IO.userError
      s!"a coerced marked result escaped staged evaluation: {reprStr result}")

private def expectRecursiveCall (label content root : String)
    (budget : Nat) : IO Unit := do
  let moduleId ← mainModule
  match prepare (workspace content) (Seed.named moduleId root)
      (limits budget) with
  | .error (.linking (.recursiveCallCycle _)) => pure ()
  | result => throw (IO.userError
      s!"{label}: recursive staged call was not rejected: {reprStr result}")

private def selfRecursiveSource : String := String.intercalate "\n" [
  "function loop(comptime value: Word) returns (comptime<Word>) {",
  "  return loop(value);",
  "}",
  "function entry() returns (Word) { return loop(1); }"
]

private def mutualRecursiveSource : String := String.intercalate "\n" [
  "function left(comptime value: Word) returns (comptime<Word>) {",
  "  return right(value);",
  "}",
  "function right(comptime value: Word) returns (comptime<Word>) {",
  "  return left(value);",
  "}",
  "function entry() returns (Word) { return left(1); }"
]

private def eagerRecursiveSource : String := String.intercalate "\n" [
  "function constant(comptime value: Word) returns (comptime<Word>) {",
  "  return value;",
  "}",
  "function loop(comptime value: Word) returns (comptime<Word>) {",
  "  return loop(value);",
  "}",
  "function entry() returns (Word) {",
  "  return true ? constant(1) : loop(0);",
  "}"
]

private def testRecursiveRejections : IO Unit := do
  expectRecursiveCall "self recursion" selfRecursiveSource "entry" 2
  expectRecursiveCall "mutual recursion" mutualRecursiveSource "entry" 3
  expectRecursiveCall "eager unselected recursion" eagerRecursiveSource
    "entry" 3

private def deepAcyclicSource : String := String.intercalate "\n" [
  "function leaf(comptime value: Word) returns (comptime<Word>) {",
  "  return value + 1;",
  "}",
  "function stepOne(value: Word) returns (comptime<Word>) {",
  "  return leaf(value) + 1;",
  "}",
  "function stepTwo(value: Word) returns (comptime<Word>) {",
  "  return stepOne(value) + 1;",
  "}",
  "function stepThree(value: Word) returns (comptime<Word>) {",
  "  return stepTwo(value) + 1;",
  "}",
  "function entry() returns (Word) { return stepThree(5); }"
]

private def testDeepAcyclicCall : IO Unit := do
  let moduleId ← mainModule
  let prepared ← match prepare (workspace deepAcyclicSource)
      (Seed.named moduleId "entry") (limits 5) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"deep acyclic staged calls failed with sufficient budget: {reprStr error}")
  let expectedWord := word 9
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = .word expectedWord ∧
      prepared.entry.elaborated.core = .word expectedWord))
    "deep acyclic staged chain was not reified as one closed Word"
  let store : Core.Store := [.bool true, .word (word 37)]
  assertTrue (decide (prepared.run? [] 4096 store =
      some (.done (.word expectedWord) store)))
    "deep acyclic staged chain changed its value or store"

private def ordinaryEvidenceLetSource : String := String.intercalate "\n" [
  "trait Coerce<From, To> {",
  "  function coerce(value: From) returns (To);",
  "}",
  "impl Coerce<Bool, Word> {",
  "  function coerce(value: Bool) returns (Word) { return 91; }",
  "}",
  "function entry() returns (Word) {",
  "  let alias: Word = true;",
  "  return alias;",
  "}"
]

private def testOrdinaryEvidenceLetPreserved : IO Unit := do
  let moduleId ← mainModule
  let prepared ← match prepare (workspace ordinaryEvidenceLetSource)
      (Seed.named moduleId "entry") (limits 1) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"ordinary evidence-bearing let regressed: {reprStr error}")
  assertTrue (decide (prepared.run? [] 4096 =
      some (.done (.word (word 91)) [])))
    "general staged caching bypassed ordinary coercion evidence execution"

private def comptimeInputDraftSource : String := String.intercalate "\n" [
  "function staged() returns (comptime<Word>) { return 7; }",
  "function direct(comptime unused: Word) returns (Word) {",
  "  return staged();",
  "}",
  "function cached(comptime unused: Word) returns (Word) {",
  "  let closed: Word = staged();",
  "  return closed;",
  "}",
  "function entryDirect() returns (Word) { return direct(1); }",
  "function entryCached() returns (Word) { return cached(1); }"
]

private def testIndependentComptimeInputDraft : IO Unit := do
  let moduleId ← mainModule
  let store : Core.Store := [.bool false, .word (word 33)]
  for (name, cached) in [("entryDirect", false), ("entryCached", true)] do
    let prepared ← match prepare (workspace comptimeInputDraftSource)
        (Seed.named moduleId name) (limits 3) with
      | .ok prepared => pure prepared
      | .error error => throw (IO.userError
          s!"{name}: input-independent staged draft was rejected: {reprStr error}")
    assertTrue (decide (prepared.run? [] 4096 store =
        some (.done (.word (word 7)) store)))
      s!"{name}: input-independent staged draft changed its value or store"
    match prepared.entry.elaborated.resolved, cached with
    | .letE temporary (.word argument)
        (.letE _ (.var reference) (.word result)), false =>
        assertTrue (decide (temporary = reference ∧ argument = word 1 ∧
            result = word 7))
          "direct input-independent call did not reify its marked result"
    | .letE temporary (.word argument)
        (.letE _ (.var reference)
          (.letE closed (.word result) (.var closedReference))), true =>
        assertTrue (decide (temporary = reference ∧ closed = closedReference ∧
            argument = word 1 ∧ result = word 7))
          "cached input-independent call did not reify its let initializer"
    | resolved, _ => throw (IO.userError
        s!"{name}: unexpected resolved draft shape: {reprStr resolved}")

private def knownComptimeInputSource : String := String.intercalate "\n" [
  "function increment(comptime value: Word) returns (comptime<Word>) {",
  "  return value + 1;",
  "}",
  "function helper(comptime value: Word) returns (Word) {",
  "  return increment(value);",
  "}",
  "function entry() returns (Word) { return helper(7); }",
  "function entryAlias() returns (Word) {",
  "  let known: Word = 12;",
  "  return helper(known);",
  "}",
  "function entryPair() returns ((Word, Word)) {",
  "  return (helper(2), helper(9));",
  "}"
]

private def testKnownComptimeInputPropagation : IO Unit := do
  let moduleId ← mainModule
  let store : Core.Store := [.word (word 41), .bool true]
  let prepared ← match prepare (workspace knownComptimeInputSource)
      (Seed.named moduleId "entry") (limits 3) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"known comptime input did not reach its runtime draft: {reprStr error}")
  assertTrue (decide (prepared.run? [] 4096 store =
      some (.done (.word (word 8)) store)))
    "known comptime input produced the wrong staged result or changed the store"
  match prepared.entry.elaborated.resolved with
  | .letE temporary (.word argument)
      (.letE _ (.var reference) (.word result)) =>
      assertTrue (decide (temporary = reference ∧ argument = word 7 ∧
          result = word 8))
        "known comptime input was not materialized inside the callee draft"
  | resolved => throw (IO.userError
      s!"known comptime input has the wrong resolved shape: {reprStr resolved}")

  let pair ← match prepare (workspace knownComptimeInputSource)
      (Seed.named moduleId "entryPair") (limits 3) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"distinct known inputs failed to prepare: {reprStr error}")
  assertTrue (decide (pair.run? [] 4096 store = some (.done
      (.pair (.word (word 3)) (.word (word 10))) store)))
    "two call sites sharing one type specialization also shared a staged value"

  let alias ← match prepare (workspace knownComptimeInputSource)
      (Seed.named moduleId "entryAlias") (limits 3) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"caller-local known alias failed to prepare: {reprStr error}")
  assertTrue (decide (alias.inputTypes = [] ∧
      alias.run? [] 4096 store = some (.done (.word (word 13)) store)))
    "caller-local staged alias did not reach the runtime callee draft"

private def mixedKnownInputSource : String := String.intercalate "\n" [
  "function choose(comptime flag: Bool) returns (comptime<Word>) {",
  "  return flag ? 2 : 9;",
  "}",
  "function helper(comptime flag: Bool, value: Word, select: Bool) returns (Word) {",
  "  let selected: Word = choose(flag);",
  "  return select ? selected : value;",
  "}",
  "function entry(value: Word, select: Bool) returns (Word) {",
  "  return helper(true, value, select);",
  "}"
]

private def testMixedKnownAndRuntimeInputs : IO Unit := do
  let moduleId ← mainModule
  let prepared ← match prepare (workspace mixedKnownInputSource)
      (Seed.named moduleId "entry") (limits 3) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"mixed staged/runtime inputs failed to prepare: {reprStr error}")
  assertTrue (decide (prepared.inputTypes = [.word, .bool]))
    "runtime arguments disappeared from the linked Core input context"
  let store : Core.Store := [.bool false, .word (word 77)]
  assertTrue (decide (prepared.run? [.word (word 40), .bool true] 4096 store =
      some (.done (.word (word 2)) store)))
    "known Bool input did not materialize the selected marked value"
  assertTrue (decide (prepared.run? [.word (word 40), .bool false] 4096 store =
      some (.done (.word (word 40)) store)))
    "runtime Word or Bool input was erased while propagating staged knowledge"

private def productKnownInputSource : String := String.intercalate "\n" [
  "function stagedProduct(comptime value: (Word, Bool)) returns (comptime<(Word, Bool)>) {",
  "  return value;",
  "}",
  "function helper(comptime value: (Word, Bool)) returns ((Word, Bool)) {",
  "  return stagedProduct(value);",
  "}",
  "function entry() returns ((Word, Bool)) {",
  "  return helper((4, true));",
  "}"
]

private def testProductKnownInput : IO Unit := do
  let moduleId ← mainModule
  let prepared ← match prepare (workspace productKnownInputSource)
      (Seed.named moduleId "entry") (limits 3) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"known product input failed to prepare: {reprStr error}")
  let expected := Core.Value.pair (.word (word 4)) (.bool true)
  let store : Core.Store := [.word (word 19)]
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.run? [] 4096 store = some (.done expected store)))
    "known product input did not retain its staged structure or store"
  match prepared.entry.elaborated.resolved with
  | .letE temporary (.pair (.word argumentWord) (.bool argumentFlag))
      (.letE _ (.var reference)
        (.pair (.word resultWord) (.bool resultFlag))) =>
      assertTrue (decide (temporary = reference ∧
          argumentWord = word 4 ∧ argumentFlag ∧
          resultWord = word 4 ∧ resultFlag))
        "product-valued marked result was not reified inside the runtime draft"
  | resolved => throw (IO.userError
      s!"known product input has the wrong resolved shape: {reprStr resolved}")

private def unavailableKnownInputSource : String := String.intercalate "\n" [
  "function identity(comptime value: Word) returns (comptime<Word>) {",
  "  return value;",
  "}",
  "function helper(comptime value: Word) returns (Word) {",
  "  return identity(value);",
  "}",
  "function producer(value: Word) returns (Word) { return value; }",
  "function runtimeEntry(value: Word) returns (Word) {",
  "  return helper(value);",
  "}",
  "function deferredEntry(value: Word) returns (Word) {",
  "  return helper(producer(value));",
  "}"
]

private def testUnavailableKnownInputsRejected : IO Unit := do
  let moduleId ← mainModule
  match prepare (workspace unavailableKnownInputSource)
      (Seed.named moduleId "runtimeEntry") (limits 3) with
  | .error (.linking (.runtimeArgumentToComptimeParameter _ _ 0 _)) =>
      pure ()
  | result => throw (IO.userError
      s!"runtime actual was promoted to a known comptime input: {reprStr result}")
  match prepare (workspace unavailableKnownInputSource)
      (Seed.named moduleId "deferredEntry") (limits 4) with
  | .error (.linking (.comptimeArgumentDeferred _ _ 0 _)) => pure ()
  | result => throw (IO.userError
      s!"deferred actual was promoted to a known comptime input: {reprStr result}")

/-- Fix proof-only evidence forwarding, the remaining coercion boundary, eager
recursion rejection, ordinary evidence-let compatibility, known/unavailable
runtime-draft staging, mixed runtime inputs, structural values, and successful
finite evaluation of a sufficiently budgeted acyclic chain. -/
def testSourceStagedValueCallsTamper : IO Unit := do
  testPredicateEvidenceForwarded
  testResultCoercionRejected
  testRecursiveRejections
  testDeepAcyclicCall
  testOrdinaryEvidenceLetPreserved
  testIndependentComptimeInputDraft
  testKnownComptimeInputPropagation
  testMixedKnownAndRuntimeInputs
  testProductKnownInput
  testUnavailableKnownInputsRejected

end Tests.SourceStagedValueCallsTamper
