import Solcore.Frontend.SourceInference

/-!
Focused end-to-end regressions for overload selection with the builtin
`Int<target>` obligation owned by an integer-literal argument.  Candidate
checking specializes that existing obligation without allocating a second
one or preferring Word over another supported builtin target.
-/

set_option autoImplicit false

namespace Tests.SourceLiteralOverloadRanking

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def rawWorkspace (lines : List String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{
    path := "main.solc"
    content := String.intercalate "\n" lines
  }]
  externalLibraries := []
}

private def checkProgram (lines : List String) :
    IO (List SourceInference.CheckedFunction) := do
  match SourceInference.loadAndCheckProgram (rawWorkspace lines) with
  | .ok checked => pure checked
  | .error errors =>
      throw (IO.userError s!"literal overload fixture failed: {reprStr errors}")

private def hasBuiltinIntEvidence
    (function : SourceInference.CheckedFunction) (target : TypeSystem.Ty)
    (implementation : BuiltinImplId) : Bool :=
  function.solvedRequirements.any fun solved =>
    solved.predicate == ProgramSignatures.builtinIntPredicate target &&
      match solved.evidence with
      | .implementation (.byImpl goal (.builtin actual) premises) =>
          goal == solved.predicate && actual == implementation &&
            premises.isEmpty
      | _ => false

private def expectLastChecked (lines : List String) :
    IO SourceInference.CheckedFunction := do
  match (← checkProgram lines).getLast? with
  | some function => pure function
  | none => throw (IO.userError "literal overload fixture checked no functions")

private def testWordAndIntegerStayAmbiguous : IO Unit := do
  let lines := [
    "function choose(value: Word) returns (Bool) { return true; }",
    "function choose(value: integer) returns (Bool) { return false; }",
    "function run() returns (Bool) { return choose(1); }"
  ]
  match SourceInference.loadAndCheckProgram (rawWorkspace lines) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .ambiguousOverload "choose" candidates, .. } =>
            candidates.length == 2
        | _ => false)
        "Word and integer literal targets acquired an artificial preference"
  | .ok _ =>
      throw (IO.userError "Word and integer literal overloads were ranked")

private def testResultContextSelectsBuiltinTarget : IO Unit := do
  let wordRun ← expectLastChecked [
    "function choose(value: Word) returns (Word) { return value; }",
    "function choose(value: integer) returns (integer) { return value; }",
    "function run() returns (Word) { return choose(1); }"
  ]
  assertTrue (hasBuiltinIntEvidence wordRun .word .intWord)
    "Word result context did not select Int<Word> evidence"
  let integerRun ← expectLastChecked [
    "function choose(value: Word) returns (Word) { return value; }",
    "function choose(value: integer) returns (integer) { return value; }",
    "function run() returns (integer) { return choose(1); }"
  ]
  assertTrue (hasBuiltinIntEvidence integerRun .integer .intInteger)
    "integer result context did not select Int<integer> evidence"

private def testInapplicableBoolDoesNotBlockWord : IO Unit := do
  let run ← expectLastChecked [
    "function choose(value: Bool) returns (Bool) { return value; }",
    "function choose(value: Word) returns (Bool) { return true; }",
    "function run() returns (Bool) { return choose(1); }"
  ]
  assertTrue (decide (run.inferredBodyType = TypeSystem.Ty.bool))
    "inapplicable Bool overload blocked the Word literal candidate"
  assertTrue (hasBuiltinIntEvidence run .word .intWord)
    "viable Word candidate lost the literal's unique Int<Word> evidence"
  let literals := run.typedBody.nodes.filterMap fun
    | .expression node => match node.form with
        | .integerLiteral _ resolution => some (node, resolution)
        | _ => none
    | .statement _ => none
  match run.solvedRequirements, literals with
  | [solved], [(node, resolution)] =>
      assertTrue (decide (solved.id = ⟨0⟩ ∧
          solved.predicate = ProgramSignatures.builtinIntPredicate .word ∧
          resolution.requirement = solved.id ∧
          node.requirements = [solved.id]))
        "speculative overload candidates duplicated the literal requirement"
  | solved, carriers => throw (IO.userError
      s!"expected one literal row/carrier, found {solved.length}/{carriers.length}")

private def testOpenGenericDoesNotBlockWord : IO Unit := do
  let run ← expectLastChecked [
    "function choose<T>(value: T) returns (Bool) { return true; }",
    "function choose(value: Word) returns (Bool) { return true; }",
    "function run() returns (Bool) { return choose(1); }"
  ]
  assertTrue (hasBuiltinIntEvidence run .word .intWord)
    "an unresolved generic literal target blocked the concrete Word candidate"

private def testGroundCandidateOutranksCheaperDeferredCandidate : IO Unit := do
  let run ← expectLastChecked [
    "trait Coerce<From, To> {}",
    "impl Coerce<Bool, Word> {}",
    "function choose(value: Word) returns (Bool) { return true; }",
    "function choose<T>(value: T) returns (Word) { return 0; }",
    "function run() returns (Word) { return choose(1); }"
  ]
  assertTrue (hasBuiltinIntEvidence run .word .intWord)
    "a cheaper deferred generic candidate outranked a ground Word candidate"
  assertTrue (run.solvedRequirements.any fun solved =>
      solved.predicate.subject == TypeSystem.Ty.bool &&
        solved.predicate.arguments == [TypeSystem.Ty.word])
    "the selected ground candidate lost its Bool-to-Word result coercion"

private def testNestedGenericDefersUntilOuterCandidate : IO Unit := do
  let run ← expectLastChecked [
    "trait Eq<T> {}",
    "impl Eq<Word> {}",
    "function keep<T>(value: T) returns (T) where T: Eq { return value; }",
    "function choose(value: Word) returns (Bool) { return true; }",
    "function choose(value: integer) returns (Bool) { return false; }",
    "function run() returns (Bool) { return choose(keep(1)); }"
  ]
  assertTrue (hasBuiltinIntEvidence run .word .intWord)
    "an inner generic call rejected its literal before the outer Word candidate"
  assertTrue (run.solvedRequirements.any fun solved =>
      solved.predicate.trait != ProgramTraitId.builtin .int &&
        solved.predicate.subject == TypeSystem.Ty.word)
    "the outer candidate did not revalidate the inner generic Eq requirement"

private def testLetBoundLiteralParticipatesInRanking : IO Unit := do
  let run ← expectLastChecked [
    "function choose<T>(value: T) returns (Bool) { return true; }",
    "function choose(value: Word) returns (Bool) { return true; }",
    "function run() returns (Bool) {",
    "  let value = 1;",
    "  return choose(value);",
    "}"
  ]
  assertTrue (hasBuiltinIntEvidence run .word .intWord)
    "a let-bound flexible literal made a generic overload look ground"

private def testSoleDeferredCandidateFailsAtFinalization : IO Unit := do
  let lines := [
    "function keep<T>(value: T) returns (T) { return value; }",
    "function bad() { keep(1); return; }"
  ]
  match SourceInference.loadAndCheckProgram (rawWorkspace lines) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .unresolvedIntegerLiteralTarget _ (.variable _),
            .. } => true
        | _ => false)
        "a sole deferred generic candidate did not reach final literal validation"
  | .ok _ => throw (IO.userError
      "a sole generic overload left an unconstrained literal target accepted")

/-- Exercise builtin-Int overload viability, equal-cost ambiguity, contextual
selection, and nonblocking unsupported candidates. -/
def testSourceLiteralOverloadRanking : IO Unit := do
  testWordAndIntegerStayAmbiguous
  testResultContextSelectsBuiltinTarget
  testInapplicableBoolDoesNotBlockWord
  testOpenGenericDoesNotBlockWord
  testGroundCandidateOutranksCheaperDeferredCandidate
  testNestedGenericDefersUntilOuterCandidate
  testLetBoundLiteralParticipatesInRanking
  testSoleDeferredCandidateFailsAtFinalization

end Tests.SourceLiteralOverloadRanking
