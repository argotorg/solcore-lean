import Solcore.Frontend.SourceInference
import Solcore
import Solcore.Frontend.SourceCoreElaboration
import Solcore.Core.Machine
import Solcore.Frontend.SourceSpecialization
import Solcore.Frontend.SourceCoreDirectLinking
import Solcore.Test.SourceCoreUnifiedCorpusSupport
import Solcore.Frontend.ProgramChecking
import Solcore.Frontend.SourceStageAnalysis

/-!
# Specialization and coercion tests

Whole-program specialization, stage classification, source coercion, literal overloads and pattern
matching.
-/

section
-- leanmerge: from Solcore.Test.SourceCoercionRanking
/-! Per-argument coercion and exact-over-coercible overload regressions. -/

set_option autoImplicit false

namespace Tests.SourceCoercionRanking

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def check (content : String) :
    IO (List SourceInference.CheckedFunction) := do
  match SourceInference.loadAndCheckProgram (workspace content) with
  | .ok checked => pure checked
  | .error errors =>
      throw (IO.userError s!"source inference failed: {reprStr errors}")

private def finalFunction
    (checked : List SourceInference.CheckedFunction) :
    IO SourceInference.CheckedFunction :=
  match checked.getLast? with
  | some function => pure function
  | none => throw (IO.userError "source inference returned no checked function")

private def testTwoArgumentsBothCoerced : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "impl Coerce<Word, Box> {}",
    "function accept(left: Box, right: Box) returns (Box) { return left; }",
    "function convert(left: Word, right: Word) returns (Box) {",
    "  return accept(left, right);",
    "}"
  ])
  let function ← finalFunction checked
  assertTrue (function.predicates.length == 2 && function.evidence.length == 2)
    "two source arguments did not retain two independent coercions"

private def testOneExactOneCoerced : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "impl Coerce<Word, Box> {}",
    "function accept(left: Word, right: Box) returns (Box) { return right; }",
    "function convert(left: Word, right: Word) returns (Box) {",
    "  return accept(left, right);",
    "}"
  ])
  let function ← finalFunction checked
  assertTrue (function.predicates.length == 1 && function.evidence.length == 1)
    "an exact argument introduced coercion evidence"

private def testTupleArgumentStaysWhole : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "impl Coerce<Word, Box> {}",
    "function accept(value: (Box, Box)) returns ((Box, Box)) { return value; }",
    "function reject(left: Word, right: Word) returns ((Box, Box)) {",
    "  return accept((left, right));",
    "}"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            predicate.subject == TypeSystem.Ty.product .word .word
        | _ => false)
        "one tuple argument was recursively treated as two coercible arguments"
  | .ok _ =>
      throw (IO.userError "element coercions were incorrectly applied inside a tuple")

private def testExactOverloadWins : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "impl Coerce<Word, Box> {}",
    "function choose(value: Box) returns (Bool) { return true; }",
    "function choose(value: Word) returns (Word) { return value; }",
    "function select(value: Word) returns (Word) { return choose(value); }"
  ])
  let function ← finalFunction checked
  assertTrue (function.inferredBodyType == TypeSystem.Ty.word &&
      function.predicates.isEmpty && function.evidence.isEmpty)
    "a coercible overload competed with an exact overload"

private def testMissingPerArgumentCoercion : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "enum Flag { Only }",
    "impl Coerce<Word, Box> {}",
    "function accept(left: Box, right: Flag) returns (Box) { return left; }",
    "function reject(left: Word, right: Word) returns (Box) {",
    "  return accept(left, right);",
    "}"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            predicate.subject == TypeSystem.Ty.word &&
              predicate.arguments.length == 1
        | _ => false)
        "a missing coercion for one argument did not reject the call"
  | .ok _ => throw (IO.userError "a missing per-argument coercion was accepted")

private def testMethodProofCountDoesNotDistortEdgeCost : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Ready<T> {}",
    "trait Stable<T> {}",
    "trait Coerce<From, To> {",
    "  function coerce(value: From) returns (To)",
    "      where From: Ready, From: Stable;",
    "}",
    "enum A { Only }",
    "enum B { Only }",
    "enum Mid { Only }",
    "enum C { Only }",
    "impl Ready<A> {}",
    "impl Stable<A> {}",
    "impl Ready<Mid> {}",
    "impl Stable<Mid> {}",
    "impl Coerce<A, B> {",
    "  function coerce(value: A) returns (B)",
    "      where A: Ready, A: Stable { return value; }",
    "}",
    "impl Coerce<A, Mid> {",
    "  function coerce(value: A) returns (Mid)",
    "      where A: Ready, A: Stable { return value; }",
    "}",
    "impl Coerce<Mid, C> {",
    "  function coerce(value: Mid) returns (C)",
    "      where Mid: Ready, Mid: Stable { return value; }",
    "}",
    "function choose(value: B) returns (Word) { return 1; }",
    "function choose(value: C) returns (Word) { return 2; }",
    "function run(value: A) returns (Word) { return choose(value); }"
  ]
  let loaded ← match loadProgram (workspace source) with
    | .ok loaded => pure loaded
    | .error errors => throw (IO.userError
        s!"coercion-cost fixture failed to load: {reprStr errors}")
  let signatures ← match buildProgramSignatures loaded.environment with
    | .ok signatures => pure signatures
    | .error errors => throw (IO.userError
        s!"coercion-cost signatures failed: {reprStr errors}")
  let checked ← match SourceInference.checkFunctionBodies
      loaded.environment signatures with
    | .ok checked => pure checked
    | .error errors => throw (IO.userError
        s!"coercion-cost inference failed: {reprStr errors}")
  let run ← finalFunction checked
  let declaration ← match loaded.environment.valuesNamed "run" with
    | [declaration] => pure declaration
    | declarations => throw (IO.userError
        s!"expected one run declaration, found {declarations.length}")
  let namedType (name : String) : IO TypeSystem.Ty :=
    match loaded.environment.typesNamed name with
    | [declaration] => pure (.nominal declaration.id)
    | declarations => throw (IO.userError
        s!"expected one type `{name}`, found {declarations.length}")
  let namedTrait (name : String) : IO Resolved.DeclarationId :=
    match loaded.environment.traitsNamed name with
    | [declaration] => pure declaration.id
    | declarations => throw (IO.userError
        s!"expected one trait `{name}`, found {declarations.length}")
  let a ← namedType "A"
  let b ← namedType "B"
  let c ← namedType "C"
  let coerce ← namedTrait "Coerce"
  let ready ← namedTrait "Ready"
  let stable ← namedTrait "Stable"
  let context : SourceInference.Context := {
    environment := loaded.environment
    signatures
    scope := .ofDeclaration declaration
  }
  let state := SourceInference.State.initial declaration.id
  let argument : SourceInference.InferredExpression := {
    id := { occurrence := { owner := declaration.id, index := 0 } }
    type := a
  }
  let directFit ← match SourceInference.Detail.fitArguments context state
      [argument] [b] with
    | .ok (some fitted) => pure fitted
    | .ok none => throw (IO.userError "one-edge coercion did not fit")
    | .error error => throw (IO.userError
        s!"one-edge coercion failed: {reprStr error}")
  let longFit ← match SourceInference.Detail.fitArguments context state
      [argument] [c] with
    | .ok (some fitted) => pure fitted
    | .ok none => throw (IO.userError "two-edge coercion did not fit")
    | .error error => throw (IO.userError
        s!"two-edge coercion failed: {reprStr error}")
  assertTrue (decide (directFit.cost = 1 ∧ longFit.cost = 2 ∧
      directFit.state.requirements.length = 3 ∧
      longFit.state.requirements.length = 6))
    "coercion ranking counted proof obligations instead of path edges"
  let expected : List ProgramPredicate := [
    { trait := coerce, subject := a, arguments := [b] },
    { trait := ready, subject := a, arguments := [] },
    { trait := stable, subject := a, arguments := [] }
  ]
  assertTrue (decide (run.predicates = expected))
    "a two-edge overload outranked the one-edge overload with method evidence"

/-- Exercise direct coercion per source argument without flattening tuple values. -/
def testSourceCoercionRanking : IO Unit := do
  testTwoArgumentsBothCoerced
  testOneExactOneCoerced
  testTupleArgumentStaysWhole
  testExactOverloadWins
  testMissingPerArgumentCoercion
  testMethodProofCountDoesNotDistortEdgeCost

end Tests.SourceCoercionRanking
end

section
-- leanmerge: from Solcore.Test.SourceLiteralOverloadRanking
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

private def testSoleDeferredCandidateDefaultsToWord : IO Unit := do
  let run ← expectLastChecked [
    "function keep<T>(value: T) returns (T) { return value; }",
    "function bad() { keep(1); return; }"
  ]
  assertTrue (decide (run.inferredBodyType = TypeSystem.Ty.unit))
    "a defaulted discarded generic call changed the function result type"
  assertTrue (hasBuiltinIntEvidence run .word .intWord)
    "a sole deferred generic candidate did not default its literal to Word"
  let calls := run.typedBody.nodes.filterMap fun
    | .expression node => match node.form with
        | .call _ _ (.declaration instantiation) => some instantiation
        | _ => none
    | .statement _ => none
  assertTrue (calls.any fun instantiation =>
      decide (instantiation.parameterSubstitution.map Prod.snd = [.word] ∧
        instantiation.type = .function .word .word))
    "literal defaulting did not close the selected generic instantiation"

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
  testSoleDeferredCandidateDefaultsToWord

end Tests.SourceLiteralOverloadRanking
end

section
-- leanmerge: from Solcore.Test.SourceMultiStepCoercion
/-!
End-to-end contracts for bounded, shortest-path source coercion.
-/

set_option autoImplicit false

namespace Tests.SourceMultiStepCoercion

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private structure SuccessfulFixture where
  environment : ProgramEnvironment
  checked : List SourceInference.CheckedFunction

private def check (content : String) : IO SuccessfulFixture := do
  match loadProgram (workspace content) with
  | .error errors =>
      throw (IO.userError s!"multi-step coercion loading failed: {reprStr errors}")
  | .ok loaded =>
      match SourceInference.checkLoadedProgram loaded with
      | .error errors =>
          throw (IO.userError
            s!"multi-step coercion checking failed: {reprStr errors}")
      | .ok checked => pure { environment := loaded.environment, checked }

private def checkedNamed (fixture : SuccessfulFixture) (name : String) :
    IO SourceInference.CheckedFunction :=
  match fixture.checked.find? fun function =>
      match fixture.environment.declaration? function.declaration with
      | some declaration => declaration.name == some name
      | none => false with
  | some function => pure function
  | none => throw (IO.userError s!"checked function `{name}` was not found")

private def namedType (environment : ProgramEnvironment) (name : String) :
    IO TypeSystem.Ty :=
  match environment.typesNamed name with
  | [declaration] => pure (.nominal declaration.id)
  | declarations =>
      throw (IO.userError
        s!"expected one type `{name}`, found {declarations.length}")

private def namedTrait (environment : ProgramEnvironment) (name : String) :
    IO Resolved.DeclarationId :=
  match environment.traitsNamed name with
  | [declaration] => pure declaration.id
  | declarations =>
      throw (IO.userError
        s!"expected one trait `{name}`, found {declarations.length}")

private def implementationIds (environment : ProgramEnvironment) :
    List Resolved.DeclarationId :=
  (environment.declarations.filter fun declaration =>
    declaration.kind == .implementation).map (·.id)

private def coercionPredicate (trait : Resolved.DeclarationId)
    (source target : TypeSystem.Ty) : ProgramPredicate := {
  trait
  subject := source
  arguments := [target]
}

private def isImplementationEvidence
    (predicate : ProgramPredicate) (implementation : Resolved.DeclarationId) :
    SourceInference.PredicateEvidence → Bool
  | .implementation (.byImpl goal selected premises) =>
      decide (goal = predicate) && decide (selected = implementation) &&
        premises.isEmpty
  | .assumption _ => false

private def isAssumptionEvidence
    (predicate : ProgramPredicate) : SourceInference.PredicateEvidence → Bool
  | .assumption actual => decide (actual = predicate)
  | .implementation _ => false

private def testTwoStepPathRetainsOrderedEvidence : IO Unit := do
  let fixture ← check (String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum A { Only }",
    "enum B { Only }",
    "enum C { Only }",
    "impl Coerce<A, B> {}",
    "impl Coerce<B, C> {}",
    "function accept(value: C) returns (C) { return value; }",
    "function convert(value: A) returns (C) { return accept(value); }"
  ])
  let convert ← checkedNamed fixture "convert"
  let a ← namedType fixture.environment "A"
  let b ← namedType fixture.environment "B"
  let c ← namedType fixture.environment "C"
  let coerce ← namedTrait fixture.environment "Coerce"
  let first := coercionPredicate coerce a b
  let second := coercionPredicate coerce b c
  assertTrue (decide (convert.predicates = [first, second]))
    "A -> B -> C did not retain its predicates in path order"
  match implementationIds fixture.environment, convert.evidence with
  | firstImpl :: secondImpl :: [], firstEvidence :: secondEvidence :: [] =>
      assertTrue (isImplementationEvidence first firstImpl firstEvidence &&
          isImplementationEvidence second secondImpl secondEvidence)
        "A -> B -> C did not retain ordered implementation evidence"
  | implementations, evidence =>
      throw (IO.userError
        s!"unexpected implementation/evidence counts: {implementations.length}/{evidence.length}")

private def testDirectPathBeatsTwoStepPath : IO Unit := do
  let fixture ← check (String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum A { Only }",
    "enum B { Only }",
    "enum C { Only }",
    "impl Coerce<A, B> {}",
    "impl Coerce<B, C> {}",
    "impl Coerce<A, C> {}",
    "function accept(value: C) returns (C) { return value; }",
    "function convert(value: A) returns (C) { return accept(value); }"
  ])
  let convert ← checkedNamed fixture "convert"
  let a ← namedType fixture.environment "A"
  let c ← namedType fixture.environment "C"
  let coerce ← namedTrait fixture.environment "Coerce"
  let direct := coercionPredicate coerce a c
  assertTrue (decide (convert.predicates = [direct]))
    "a direct coercion did not outrank a two-step coercion"
  match implementationIds fixture.environment, convert.evidence with
  | _ :: _ :: directImpl :: [], [evidence] =>
      assertTrue (isImplementationEvidence direct directImpl evidence)
        "the direct coercion retained evidence from the longer path"
  | implementations, evidence =>
      throw (IO.userError
        s!"unexpected implementation/evidence counts: {implementations.length}/{evidence.length}")

private def testDefaultImplementationCoercionPriority : IO Unit := do
  let ordinaryFixture ← check (String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum A { Only }",
    "enum B { Only }",
    "default impl Coerce<A, B> {}",
    "impl Coerce<A, B> {}",
    "function accept(value: B) returns (B) { return value; }",
    "function convert(value: A) returns (B) { return accept(value); }"
  ])
  let ordinaryConvert ← checkedNamed ordinaryFixture "convert"
  let ordinaryA ← namedType ordinaryFixture.environment "A"
  let ordinaryB ← namedType ordinaryFixture.environment "B"
  let ordinaryCoerce ← namedTrait ordinaryFixture.environment "Coerce"
  let ordinaryPredicate :=
    coercionPredicate ordinaryCoerce ordinaryA ordinaryB
  match implementationIds ordinaryFixture.environment,
      ordinaryConvert.evidence with
  | _defaultImpl :: ordinaryImpl :: [], [evidence] =>
      assertTrue (decide (ordinaryConvert.predicates = [ordinaryPredicate]) &&
          isImplementationEvidence ordinaryPredicate ordinaryImpl evidence)
        "a default coercion duplicated its edge or outranked an ordinary implementation"
  | implementations, evidence =>
      throw (IO.userError
        s!"unexpected ordinary/default coercion evidence: {implementations.length}/{evidence.length}")

  let fallbackFixture ← check (String.intercalate "\n" [
    "trait Ready<T> {}",
    "trait Coerce<From, To> {}",
    "enum A { Only }",
    "enum B { Only }",
    "enum Missing { Only }",
    "default impl Coerce<A, B> {}",
    "impl Coerce<A, B> where Missing: Ready {}",
    "function accept(value: B) returns (B) { return value; }",
    "function convert(value: A) returns (B) { return accept(value); }"
  ])
  let fallbackConvert ← checkedNamed fallbackFixture "convert"
  let fallbackA ← namedType fallbackFixture.environment "A"
  let fallbackB ← namedType fallbackFixture.environment "B"
  let fallbackCoerce ← namedTrait fallbackFixture.environment "Coerce"
  let fallbackPredicate :=
    coercionPredicate fallbackCoerce fallbackA fallbackB
  match implementationIds fallbackFixture.environment,
      fallbackConvert.evidence with
  | defaultImpl :: _ordinaryImpl :: [], [evidence] =>
      assertTrue (decide (fallbackConvert.predicates = [fallbackPredicate]) &&
          isImplementationEvidence fallbackPredicate defaultImpl evidence)
        "a failed ordinary coercion premise did not fall back to the default tier"
  | implementations, evidence =>
      throw (IO.userError
        s!"unexpected fallback coercion evidence: {implementations.length}/{evidence.length}")

private def testIrrelevantAmbiguousBranchDoesNotBlock : IO Unit := do
  let fixture ← check (String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum A { Only }",
    "enum B { Only }",
    "enum C { Only }",
    "enum Dead { Only }",
    "impl Coerce<A, Dead> {}",
    "impl Coerce<A, Dead> {}",
    "impl Coerce<A, B> {}",
    "impl Coerce<B, C> {}",
    "function accept(value: C) returns (C) { return value; }",
    "function convert(value: A) returns (C) { return accept(value); }"
  ])
  let convert ← checkedNamed fixture "convert"
  let a ← namedType fixture.environment "A"
  let b ← namedType fixture.environment "B"
  let c ← namedType fixture.environment "C"
  let coerce ← namedTrait fixture.environment "Coerce"
  let first := coercionPredicate coerce a b
  let second := coercionPredicate coerce b c
  assertTrue (decide (convert.predicates = [first, second]))
    "an irrelevant ambiguous branch blocked the unique coercion path"
  match implementationIds fixture.environment, convert.evidence with
  | _ :: _ :: firstImpl :: secondImpl :: [],
      firstEvidence :: secondEvidence :: [] =>
      assertTrue (isImplementationEvidence first firstImpl firstEvidence &&
          isImplementationEvidence second secondImpl secondEvidence)
        "the unique path retained evidence from an irrelevant ambiguous branch"
  | implementations, evidence =>
      throw (IO.userError
        s!"unexpected implementation/evidence counts: {implementations.length}/{evidence.length}")

private def testAssumptionEdgeRetainsEvidence : IO Unit := do
  let fixture ← check (String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum A { Only }",
    "enum B { Only }",
    "enum C { Only }",
    "impl Coerce<B, C> {}",
    "function accept(value: C) returns (C) { return value; }",
    "function convert(value: A) returns (C) where A: Coerce<B> {",
    "  return accept(value);",
    "}"
  ])
  let convert ← checkedNamed fixture "convert"
  let a ← namedType fixture.environment "A"
  let b ← namedType fixture.environment "B"
  let c ← namedType fixture.environment "C"
  let coerce ← namedTrait fixture.environment "Coerce"
  let first := coercionPredicate coerce a b
  let second := coercionPredicate coerce b c
  assertTrue (decide (convert.predicates = [first, second]))
    "an assumption-backed coercion edge was not retained in path order"
  match implementationIds fixture.environment, convert.evidence with
  | [implementation], [firstEvidence, secondEvidence] =>
      assertTrue (isAssumptionEvidence first firstEvidence &&
          isImplementationEvidence second implementation secondEvidence)
        "assumption and implementation evidence were not retained in path order"
  | implementations, evidence =>
      throw (IO.userError
        s!"unexpected implementation/evidence counts: {implementations.length}/{evidence.length}")

private def testGenericEdgeSolvesWherePredicate : IO Unit := do
  let fixture ← check (String.intercalate "\n" [
    "trait Ready<T> {}",
    "trait Coerce<From, To> {}",
    "enum Token { Only }",
    "enum Box<T> { Wrap(T) }",
    "enum Mid<T> { Wrap(T) }",
    "enum Out { Only }",
    "impl Ready<Token> {}",
    "impl<T> Coerce<Box<T>, Mid<T>> where T: Ready {}",
    "impl Coerce<Mid<Token>, Out> {}",
    "function accept(value: Out) returns (Out) { return value; }",
    "function convert(value: Box<Token>) returns (Out) { return accept(value); }"
  ])
  let convert ← checkedNamed fixture "convert"
  let token ← namedType fixture.environment "Token"
  let box := TypeSystem.Ty.application
    (← namedType fixture.environment "Box") token
  let mid := TypeSystem.Ty.application
    (← namedType fixture.environment "Mid") token
  let out ← namedType fixture.environment "Out"
  let ready ← namedTrait fixture.environment "Ready"
  let coerce ← namedTrait fixture.environment "Coerce"
  let first := coercionPredicate coerce box mid
  let second := coercionPredicate coerce mid out
  let premise : ProgramPredicate := { trait := ready, subject := token, arguments := [] }
  assertTrue (decide (convert.predicates = [first, second]))
    "a ground generic coercion edge did not instantiate its target"
  match implementationIds fixture.environment, convert.evidence with
  | readyImpl :: genericImpl :: secondImpl :: [],
      .implementation (.byImpl firstGoal firstSelected [
        .byImpl premiseGoal premiseSelected []]) :: secondEvidence :: [] =>
      assertTrue (decide (firstGoal = first) &&
          decide (firstSelected = genericImpl) &&
          decide (premiseGoal = premise) &&
          decide (premiseSelected = readyImpl) &&
          isImplementationEvidence second secondImpl secondEvidence)
        "a generic coercion edge did not retain its nested where evidence"
  | implementations, evidence =>
      throw (IO.userError
        s!"unexpected implementation/evidence shape: {implementations.length}/{evidence.length}")

private def testMethodPredicateFailureFallsBackToTwoSteps : IO Unit := do
  let fixture ← check (String.intercalate "\n" [
    "trait Allowed<From, To> {}",
    "trait Coerce<From, To> {",
    "  function coerce(value: From) returns (To) where From: Allowed<To>;",
    "}",
    "impl Allowed<Bool, Unit> {}",
    "impl Allowed<Unit, Word> {}",
    "impl Coerce<Bool, Word> {",
    "  function coerce(value: Bool) returns (Word)",
    "      where Bool: Allowed<Word> { return 99; }",
    "}",
    "impl Coerce<Bool, Unit> {",
    "  function coerce(value: Bool) returns (Unit)",
    "      where Bool: Allowed<Unit> { return; }",
    "}",
    "impl Coerce<Unit, Word> {",
    "  function coerce(value: Unit) returns (Word)",
    "      where Unit: Allowed<Word> { return 7; }",
    "}",
    "function accept(value: Word) returns (Word) { return value; }",
    "function convert(value: Bool) returns (Word) { return accept(value); }"
  ])
  let convert ← checkedNamed fixture "convert"
  let allowed ← namedTrait fixture.environment "Allowed"
  let coerce ← namedTrait fixture.environment "Coerce"
  let primaryFirst := coercionPredicate coerce .bool .unit
  let methodFirst : ProgramPredicate := {
    trait := allowed
    subject := .bool
    arguments := [.unit]
  }
  let primarySecond := coercionPredicate coerce .unit .word
  let methodSecond : ProgramPredicate := {
    trait := allowed
    subject := .unit
    arguments := [.word]
  }
  let expected := [primaryFirst, methodFirst, primarySecond, methodSecond]
  assertTrue (decide (convert.predicates = expected) &&
      decide (convert.evidence.map SourceInference.PredicateEvidence.goal =
        expected))
    "a blocked direct edge did not fall back with primary/method evidence in edge order"
  assertTrue (convert.evidence.all fun evidence =>
      evidence matches .implementation _)
    "the viable two-step coercion did not retain implementation evidence"

private def isExplicitPathAmbiguity : SourceInference.Error → Bool
  | .ambiguousCoercion _ _ _ _ => true
  | _ => false

private def hasBodyError (errors : List SourceInference.ProgramCheckError)
    (accepts : SourceInference.Error → Bool) : Bool :=
  errors.any fun error => match error with
    | .body functionError => accepts functionError.error
    | _ => false

private def testAmbiguousDirectPathDoesNotFallBack : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum A { Only }",
    "enum B { Only }",
    "enum C { Only }",
    "impl Coerce<A, B> {}",
    "impl Coerce<B, C> {}",
    "impl Coerce<A, C> {}",
    "impl Coerce<A, C> {}",
    "function accept(value: C) returns (C) { return value; }",
    "function convert(value: A) returns (C) { return accept(value); }"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (hasBodyError errors fun error => match error with
        | .inconclusiveTrait _ => true
        | _ => false)
        "an ambiguous direct coercion incorrectly fell back to a longer path"
  | .ok _ =>
      throw (IO.userError "an ambiguous direct coercion was silently selected")

private def testEqualLengthPathsAreAmbiguous : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum A { Only }",
    "enum B { Only }",
    "enum C { Only }",
    "enum D { Only }",
    "impl Coerce<A, B> {}",
    "impl Coerce<B, D> {}",
    "impl Coerce<A, C> {}",
    "impl Coerce<C, D> {}",
    "function accept(value: D) returns (D) { return value; }",
    "function convert(value: A) returns (D) { return accept(value); }"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (hasBodyError errors isExplicitPathAmbiguity)
        "two equal-length coercion paths did not report explicit ambiguity"
  | .ok _ =>
      throw (IO.userError "one of two equal-length coercion paths was selected")

private def testCycleTerminates : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum A { Only }",
    "enum B { Only }",
    "enum C { Only }",
    "impl Coerce<A, B> {}",
    "impl Coerce<B, A> {}",
    "function accept(value: C) returns (C) { return value; }",
    "function convert(value: A) returns (C) { return accept(value); }"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (hasBodyError errors fun error => match error with
        | .noTraitImplementation _ => true
        | .inconclusiveTrait (.cycle _) => true
        | _ => false)
        "a cyclic coercion graph did not terminate with a finite failure"
  | .ok _ => throw (IO.userError "a coercion cycle synthesized a path to C")

private def boundedChainSource (edgeCount : Nat) : String :=
  let typeNames := (List.range (edgeCount + 1)).map fun index => s!"T{index}"
  let declarations := typeNames.map fun name => s!"enum {name}" ++ " { Only }"
  let implementations := (List.range edgeCount).map fun index =>
    s!"impl Coerce<T{index}, T{index + 1}>" ++ " {}"
  String.intercalate "\n" (["trait Coerce<From, To> {}"] ++ declarations ++
    implementations ++ [
      s!"function accept(value: T{edgeCount}) returns (T{edgeCount})" ++
        " { return value; }",
      s!"function convert(value: T0) returns (T{edgeCount})" ++
        " { return accept(value); }"
    ])

private def testDepthBoundaryIsExplicit : IO Unit := do
  let withinBound ← check (boundedChainSource 4)
  let convert ← checkedNamed withinBound "convert"
  assertTrue (convert.predicates.length == 4 && convert.evidence.length == 4)
    "a coercion path at the configured depth bound did not succeed"
  match SourceInference.loadAndCheckProgram
      (workspace (boundedChainSource 5)) 4096 with
  | .error errors =>
      assertTrue (hasBodyError errors fun error => match error with
        | .coercionDepthLimit _ _ 4 => true
        | _ => false)
        "bounded coercion search did not expose depth exhaustion explicitly"
  | .ok _ =>
      throw (IO.userError "a coercion path beyond the documented bound succeeded")

/-- Exercise shortest-path selection, evidence order, ambiguity, cycle safety,
and the explicit bounded-search failure through parsed source. -/
def testSourceMultiStepCoercion : IO Unit := do
  testTwoStepPathRetainsOrderedEvidence
  testDirectPathBeatsTwoStepPath
  testDefaultImplementationCoercionPriority
  testIrrelevantAmbiguousBranchDoesNotBlock
  testAssumptionEdgeRetainsEvidence
  testGenericEdgeSolvesWherePredicate
  testMethodPredicateFailureFallsBackToTwoSteps
  testAmbiguousDirectPathDoesNotFallBack
  testEqualLengthPathsAreAmbiguous
  testCycleTerminates
  testDepthBoundaryIsExplicit

end Tests.SourceMultiStepCoercion
end

section
-- leanmerge: from Solcore.Test.SourcePatternMatching
/-! End-to-end regressions for typed numeric match patterns. -/

set_option autoImplicit false

namespace Tests.SourcePatternMatching

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.Frontend.SourceProgramExecution Solcore.TypeSystem

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def word (value : Nat) : Core.Word :=
  Core.Word.ofNatModulo value

private def mainModule : IO Workspace.ModuleId := do
  match Workspace.CanonicalSourcePath.parse "main.solc" with
  | none => throw (IO.userError "invalid source-pattern test module path")
  | some canonical => pure {
      library := .main
      path := canonical.modulePath
    }

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def checkedProgram (content : String) : IO CheckedProgram := do
  match checkProgram (workspace content) with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"source-pattern fixture failed checking: {reprStr errors}")

private def checkedNamed (program : CheckedProgram) (name : String) :
    IO CheckedFunction :=
  match program.functions.find? fun function =>
      (program.environment.declaration? function.declaration).any fun entry =>
        entry.name == some name with
  | some function => pure function
  | none => throw (IO.userError s!"checked function `{name}` was not found")

private def signatureNamed (program : CheckedProgram) (name : String) :
    IO ProgramFunctionSignature :=
  match program.signatures.functions.find? fun signature =>
      (program.environment.declaration? signature.id).any fun entry =>
        entry.name == some name with
  | some signature => pure signature
  | none => throw (IO.userError s!"signature `{name}` was not found")

private def matchResolutions (function : CheckedFunction) :
    List MatchResolution :=
  function.typedBody.nodes.filterMap fun
    | .statement { form := .matchWith resolution, .. } => some resolution
    | _ => none

private def sourceGroupDepth : MatchPatternSource → Nat
  | .group _ inner => sourceGroupDepth inner + 1
  | _ => 0

private def solvedByBuiltinInt (target : Ty)
    (solved : SolvedRequirement) : Bool :=
  solved.predicate == ProgramSignatures.builtinIntPredicate target &&
    match solved.evidence with
    | .implementation (.byImpl goal implementation premises) =>
        goal == solved.predicate && premises.isEmpty &&
          implementation == if target == Ty.word then
            ProgramImplId.builtin .intWord
          else
            ProgramImplId.builtin .intInteger
    | .assumption _ => false

private def expectInferenceError (label content : String)
    (accept : SourceInference.Error → Bool) : IO Unit := do
  match SourceInference.loadAndCheckProgram (workspace content) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body failure => accept failure.error
        | _ => false) s!"{label} had the wrong inference failure"
  | .ok _ => throw (IO.userError s!"{label} was unexpectedly accepted")

private def testPatternDefaultAndLateConstraint : IO Unit := do
  let program ← checkedProgram (String.intercalate "\n" [
    "function acceptInteger(value: integer) returns (integer) { return value; }",
    "function defaulted() returns (Word) {",
    "  match (1) {",
    "    case (((1))) { return 11; }",
    "    default { return 22; }",
    "  }",
    "}",
    "function lateInteger() returns (integer) {",
    "  let value = 1;",
    "  match (value) {",
    "    case 0 { return acceptInteger(value); }",
    "    default { return value; }",
    "  }",
    "}",
    "function generic<T>(tag: Word, value: T) returns (T) {",
    "  match (tag) {",
    "    case ((0)) { return value; }",
    "    default { return value; }",
    "  }",
    "}",
    "function pick<T>(tag: T, value: T) returns (T) {",
    "  match (tag) {",
    "    case _ { return value; }",
    "  }",
    "}"
  ])
  let defaulted ← checkedNamed program "defaulted"
  let resolution ← match matchResolutions defaulted with
    | [resolution] => pure resolution
    | resolutions => throw (IO.userError
        s!"defaulted retained {resolutions.length} match nodes")
  let pattern ← match resolution.cases with
    | [arm] => pure arm.pattern
    | cases => throw (IO.userError
        s!"defaulted retained {cases.length} explicit cases")
  let patternRequirement ← match pattern.resolution with
    | .integerLiteral (.decimal "1") literal =>
        assertTrue (decide (literal.rawValue = 1 ∧
          literal.targetType = Ty.word ∧
          pattern.type = Ty.word ∧
          pattern.requirements = [literal.requirement] ∧
          resolution.requirements = [literal.requirement] ∧
          sourceGroupDepth pattern.source = 3))
          "grouped pattern carrier lost source, type, or requirement metadata"
        pure literal.requirement
    | other => throw (IO.userError
        s!"defaulted retained the wrong pattern carrier: {reprStr other}")
  assertTrue (decide (patternRequirement.index = 1 ∧
      defaulted.solvedRequirements.map (·.id.index) = [0, 1, 2, 3]) &&
      defaulted.solvedRequirements.all (solvedByBuiltinInt .word))
    "pattern-only defaulting did not close expression and pattern rows as Word"
  let late ← checkedNamed program "lateInteger"
  let latePattern ← match matchResolutions late with
    | [{ cases := [arm], .. }] => pure arm.pattern
    | resolutions => throw (IO.userError
        s!"late integer fixture retained {resolutions.length} malformed matches")
  assertTrue (late.solvedRequirements.length == 2 &&
      late.solvedRequirements.all (solvedByBuiltinInt .integer) &&
      match latePattern.resolution with
      | .integerLiteral _ literal =>
          decide (latePattern.type = .integer ∧
            literal.targetType = .integer)
      | _ => false)
    "body inference did not constrain the pattern before Word defaulting"
  let signature ← signatureNamed program "generic"
  let generic ← checkedNamed program "generic"
  let parameter ← match signature.scheme.parameters with
    | [parameter] => pure parameter
    | parameters => throw (IO.userError
        s!"generic fixture retained {parameters.length} type parameters")
  let specialized ← match SourceSpecialization.specializeFunction signature
      generic [(parameter, .bool)] with
    | .ok specialized => pure specialized
    | .error error => throw (IO.userError
        s!"generic match specialization failed: {reprStr error}")
  let specializedPattern ← match matchResolutions specialized.function with
    | [{ cases := [arm], .. }] => pure arm.pattern
    | resolutions => throw (IO.userError
        s!"specialization retained {resolutions.length} malformed matches")
  assertTrue (decide (specialized.function.inferredBodyType = Ty.bool ∧
      specializedPattern.type = Ty.word) &&
      match specializedPattern.resolution with
      | .integerLiteral _ literal => literal.targetType == Ty.word
      | _ => false)
    "specialization did not preserve and close the pattern carrier"
  let pickSignature ← signatureNamed program "pick"
  let pick ← checkedNamed program "pick"
  let pickParameter ← match pickSignature.scheme.parameters with
    | [parameter] => pure parameter
    | parameters => throw (IO.userError
        s!"pick fixture retained {parameters.length} type parameters")
  let specializedPick ← match SourceSpecialization.specializeFunction
      pickSignature pick [(pickParameter, .bool)] with
    | .ok specialized => pure specialized
    | .error error => throw (IO.userError
        s!"generic wildcard match specialization failed: {reprStr error}")
  let specializedWildcard ←
    match matchResolutions specializedPick.function with
    | [{ cases := [arm], .. }] => pure arm.pattern
    | resolutions => throw (IO.userError
        s!"wildcard specialization retained {resolutions.length} malformed matches")
  assertTrue (decide (specializedPick.function.inferredBodyType = Ty.bool ∧
      specializedWildcard.type = Ty.bool ∧
      specializedWildcard.resolution = .wildcard ∧
      specializedWildcard.requirements = []))
    "specialization did not substitute a rigid wildcard pattern type"

private def testWildcardOnlyLiteralDefault : IO Unit := do
  let source :=
    "function wildcardOnly() { match (1) { case _ { return; } } }"
  let program ← checkedProgram source
  let checked ← checkedNamed program "wildcardOnly"
  let resolution ← match matchResolutions checked with
    | [resolution] => pure resolution
    | resolutions => throw (IO.userError
        s!"wildcard-only fixture retained {resolutions.length} match nodes")
  let pattern ← match resolution.cases with
    | [arm] => pure arm.pattern
    | cases => throw (IO.userError
        s!"wildcard-only fixture retained {cases.length} match cases")
  let literal ← match checked.typedBody.lookupExpression? resolution.scrutinee with
    | some node =>
        match node.form, node.requirements with
        | .integerLiteral (.decimal "1") literal, [requirement] =>
            if node.type = Ty.word && literal.targetType = Ty.word &&
                literal.requirement = requirement then
              pure literal
            else
              throw (IO.userError
                "wildcard-only scrutinee lost its Word literal metadata")
        | _, _ => throw (IO.userError
            s!"wildcard-only scrutinee retained the wrong node: {reprStr node}")
    | other => throw (IO.userError
        s!"wildcard-only scrutinee retained the wrong node: {reprStr other}")
  assertTrue (decide (pattern.type = Ty.word ∧
      pattern.resolution = .wildcard ∧
      pattern.requirements = [] ∧
      resolution.requirements = [] ∧
      checked.inferredBodyType = Ty.unit ∧
      checked.solvedRequirements.map (·.id) = [literal.requirement]) ∧
      checked.solvedRequirements.all (solvedByBuiltinInt .word))
    "expression defaulting did not close a wildcard-only match as Word"
  let limits : Limits := {
    checkingFuel := 1024
    specializationBudget := 16
    executionFuel := 4096
  }
  let moduleId ← mainModule
  let prepared ← match prepare (workspace source)
      (Seed.named moduleId "wildcardOnly") limits with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"wildcard-only match preparation failed: {reprStr error}")
  match prepared.run? [] limits.executionFuel with
  | some (.done .unit []) => pure ()
  | result => throw (IO.userError
      s!"wildcard-only match had runtime result {reprStr result}")

private def testPatternInferenceRejections : IO Unit := do
  expectInferenceError "unreachable arm static checking"
    (String.intercalate "\n" [
      "function bad(tag: Word) returns (Word) {",
      "  match (tag) {",
      "    case _ { return 1; }",
      "    case 0 { return missing; }",
      "  }",
      "}"
    ]) fun error => error matches .unknownVariable "missing"
  expectInferenceError "match branch scope isolation"
    (String.intercalate "\n" [
      "function bad(tag: Word) returns (Word) {",
      "  match (tag) {",
      "    case 0 { let local: Word = 1; return local; }",
      "    default { return local; }",
      "  }",
      "}"
    ]) fun error => error matches .unknownVariable "local"
  expectInferenceError "Bool numeric pattern"
    "function bad(tag: Bool) returns (Word) { match (tag) { case 0 { return 1; } default { return 2; } } }"
    fun error => match error with
      | .nonNumericPatternType _ type => type == Ty.bool
      | _ => false
  expectInferenceError "nominal numeric pattern"
    (String.intercalate "\n" [
      "enum Box { Only }",
      "function bad(tag: Box) returns (Word) {",
      "  match (tag) { case 0 { return 1; } default { return 2; } }",
      "}"
    ]) fun error => match error with
      | .nonNumericPatternType _ (.constructor (.declaration _)) => true
      | _ => false
  expectInferenceError "rigid generic numeric pattern"
    (String.intercalate "\n" [
      "trait Int<T> {}",
      "function bad<T>(tag: T) returns (Word) where T: Int {",
      "  match (tag) { case 0 { return 1; } default { return 2; } }",
      "}"
    ]) fun error => error matches .nonNumericPatternType _ (.parameter _)
  let unsupported : List (String × String × String) := [
    ("string pattern", "case \"text\" { return 1; }", "string literal"),
    ("comptime pattern", "case comptime 0 { return 1; }", "comptime")
  ]
  for (label, arm, kind) in unsupported do
    expectInferenceError label
      (String.intercalate "\n" [
        "enum Box { Only }",
        "function bad(tag: Word) returns (Word) {",
        "  match (tag) {",
        "    " ++ arm,
        "    default { return 2; }",
        "  }",
        "}"
      ]) fun error => match error with
        | .unsupportedPattern _ actual => actual == kind
        | _ => false
  expectInferenceError "uncovered literal match"
    "function bad(tag: Word) returns (Word) { match (tag) { case 0 { return 1; } } }"
    fun error => error matches .nonExhaustiveMatch _
  expectInferenceError "fallthrough case"
    "function bad(tag: Word) returns (Word) { match (tag) { case _ { let value: Word = 1; } } }"
    fun error => error matches .unification _
  expectInferenceError "fallthrough default"
    "function bad(tag: Word) returns (Word) { match (tag) { case 0 { return 1; } default { let value: Word = 2; } } }"
    fun error => error matches .unification _

private def guardWords : Resolved.Expr → List Core.Word
  | .ifE (.binary .wordEq _ (.word literal)) _ rest =>
      literal :: guardWords rest
  | _ => []

private def resolvedLetBinders : Resolved.Expr → List Resolved.LocalId
  | .unit | .bool _ | .word _ | .var _ => []
  | .pair left right | .binary _ left right | .wordLt left right =>
      resolvedLetBinders left ++ resolvedLetBinders right
  | .unary _ operand => resolvedLetBinders operand
  | .letE binder value body =>
      binder :: resolvedLetBinders value ++ resolvedLetBinders body
  | .ifE condition thenBranch elseBranch =>
      resolvedLetBinders condition ++ resolvedLetBinders thenBranch ++
        resolvedLetBinders elseBranch

private def generousLimits : Limits := {
  checkingFuel := 1024
  specializationBudget := 16
  executionFuel := 4096
}

private def assertPreparedResult (label : String) (prepared : PreparedEntry)
    (input expected : Nat) : IO Unit :=
  match prepared.run? [.word (word input)] generousLimits.executionFuel with
  | some (.done (.word actual) []) =>
      assertTrue (actual == word expected) s!"{label} returned the wrong Word"
  | result => throw (IO.userError s!"{label} had runtime result {reprStr result}")

private def testModuloOrderingAndPublicExecution : IO Unit := do
  let modulus := toString Core.wordModulus
  let successor := toString (Core.wordModulus + 1)
  let source := String.intercalate "\n" [
    "function route(tag: Word) returns (Word) {",
    "  match (tag) {",
    "    case " ++ modulus ++ " { return 10; }",
    "    case 0 { return 20; }",
    "    case " ++ successor ++ " { return 30; }",
    "    case 0x01 { return 40; }",
    "    default { return 50; }",
    "  }",
    "}"
  ]
  let moduleId ← mainModule
  let prepared ← match prepare (workspace source)
      (Seed.named moduleId "route") generousLimits with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"modulo match preparation failed: {reprStr error}")
  match prepared.entry.elaborated.inputs.ids,
      prepared.entry.elaborated.resolved with
  | [input], .letE hidden (.var actual) body =>
      assertTrue (decide (actual = input ∧ hidden ≠ input) &&
          guardWords body == [word 0, word 0, word 1, word 1])
        "match lowering lost once-only scrutinee binding or source guard order"
  | _, resolved => throw (IO.userError
      s!"match lowering has the wrong resolved shape: {reprStr resolved}")
  assertPreparedResult "modulo-zero first arm" prepared 0 10
  assertPreparedResult "modulo-one first arm" prepared 1 30
  assertPreparedResult "match default" prepared 2 50
  match run (workspace source) (Seed.named moduleId "route")
      [.word (word 1)] generousLimits with
  | .ok (.done (.word actual) []) =>
      assertTrue (actual == word 30)
        "public source execution changed ordered modulo pattern selection"
  | result => throw (IO.userError
      s!"public source match execution failed: {reprStr result}")

private def testDirectCallHiddenLocalCollision : IO Unit := do
  let source := String.intercalate "\n" [
    "function identity(value: Word) returns (Word) { return value; }",
    "function routed(value: Word) returns (Word) {",
    "  match (identity(value)) {",
    "    case 0 { return 7; }",
    "    default { return 9; }",
    "  }",
    "}"
  ]
  let moduleId ← mainModule
  let prepared ← match prepare (workspace source)
      (Seed.named moduleId "routed") generousLimits with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"call-backed match preparation failed: {reprStr error}")
  let binders := resolvedLetBinders prepared.entry.elaborated.resolved
  let rootOwned := binders.filter fun binder =>
    decide (binder.owner = prepared.key.declaration)
  assertTrue (decide (binders.eraseDups.length = binders.length) &&
      rootOwned.any (fun binder => binder.binderIndex == 1) &&
      rootOwned.any (fun binder => binder.binderIndex == 2))
    "match hidden local collided with a direct-call temporary"
  assertPreparedResult "call-backed match hit" prepared 0 7
  assertPreparedResult "call-backed match default" prepared 1 9

private def testDiscardedTailStillLowers : IO Unit := do
  let source := String.intercalate "\n" [
    "function helper(value: Word) returns (Word) { return value; }",
    "function early(tag: Word) returns (Word) {",
    "  match (tag) {",
    "    case _ { return 7; }",
    "    case 0 { return helper(8); }",
    "    default { return helper(9); }",
    "  }",
    "}"
  ]
  let moduleId ← mainModule
  let prepared ← match prepare (workspace source)
      (Seed.named moduleId "early") generousLimits with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"early-wildcard match did not consume its discarded tail: {reprStr error}")
  assertPreparedResult "early wildcard ordered selection" prepared 0 7

/-- Exercise pattern-only defaulting, contextual preservation, specialization,
defensive rejection, modulo lowering, ordered selection, linking, and execution. -/
def testSourcePatternMatching : IO Unit := do
  testPatternDefaultAndLateConstraint
  testWildcardOnlyLiteralDefault
  testPatternInferenceRejections
  testModuloOrderingAndPublicExecution
  testDirectCallHiddenLocalCollision
  testDiscardedTailStillLowers
  IO.println "typed source integer-pattern inference and execution GREEN"

end Tests.SourcePatternMatching
end

section
-- leanmerge: from Solcore.Test.SourcePatternMatchingTamper
/-! Adversarial regressions for the occurrence-addressed typed match carrier.
Every malformed value below is obtained by changing one checked match fixture,
so Source Core must reject stale or forged metadata rather than trusting it. -/

set_option autoImplicit false

namespace Tests.SourcePatternMatchingTamper

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def checkedFunction : IO CheckedFunction := do
  let checked ← match checkProgram (workspace (String.intercalate "\n" [
      "function choose(tag: Word, zero: Word, other: Word) returns (Word) {",
      "  match (tag) {",
      "    case 0 { return zero; }",
      "    case _ { return other; }",
      "  }",
      "}"
    ])) with
    | .ok checked => pure checked
    | .error errors => throw (IO.userError
        s!"typed-match fixture failed checking: {reprStr errors}")
  match checked.functions with
  | [function] => pure function
  | functions => throw (IO.userError
      s!"typed-match fixture produced {functions.length} functions")

private structure Fixture where
  function : CheckedFunction
  statement : StatementId
  resolution : MatchResolution
  literalCase : TypedMatchCase
  wildcardCase : TypedMatchCase
  literalSource : Syntax.CoreLiteralValue
  literalResolution : IntegerLiteralResolution

private def fixture : IO Fixture := do
  let function ← checkedFunction
  let (statement, resolution) ← match function.typedBody.roots with
    | [.statement statement] =>
        match function.typedBody.lookupStatement? statement with
        | some { form := .matchWith resolution, .. } =>
            pure (statement, resolution)
        | _ => throw (IO.userError
            "typed-match fixture lost its match statement")
    | _ => throw (IO.userError
        "typed-match fixture does not have one statement root")
  let (literalCase, wildcardCase) ← match resolution.cases with
    | [literalCase, wildcardCase] => pure (literalCase, wildcardCase)
    | cases => throw (IO.userError
        s!"typed-match fixture retained {cases.length} explicit cases")
  let (literalSource, literalResolution) ←
      match literalCase.pattern.resolution with
    | .integerLiteral source resolution => pure (source, resolution)
    | _ => throw (IO.userError
        "typed-match fixture lost its integer pattern resolution")
  unless wildcardCase.pattern.resolution == .wildcard do
    throw (IO.userError "typed-match fixture lost its wildcard resolution")
  unless literalCase.pattern.requirements ==
      [literalResolution.requirement] &&
      wildcardCase.pattern.requirements.isEmpty &&
      resolution.requirements == [literalResolution.requirement] do
    throw (IO.userError
      "typed-match fixture lost exact pattern requirement ownership")
  pure {
    function
    statement
    resolution
    literalCase
    wildcardCase
    literalSource
    literalResolution
  }

private def changeStatement (source : TypedSource) (id : StatementId)
    (change : StatementNode → StatementNode) : TypedSource := {
  source with
  nodes := source.nodes.map fun
    | .expression node => .expression node
    | .statement node =>
        if node.id = id then .statement { change node with id }
        else .statement node
}

private def changeExpression (source : TypedSource) (id : ExpressionId)
    (change : ExpressionNode → ExpressionNode) : TypedSource := {
  source with
  nodes := source.nodes.map fun
    | .expression node =>
        if node.id = id then .expression { change node with id }
        else .expression node
    | .statement node => .statement node
}

private def withResolution (fixture : Fixture)
    (resolution : MatchResolution) : CheckedFunction := {
  fixture.function with
  typedBody := changeStatement fixture.function.typedBody fixture.statement
    fun node => { node with form := .matchWith resolution }
}

private def withCases (fixture : Fixture)
    (literalCase : TypedMatchCase := fixture.literalCase)
    (wildcardCase : TypedMatchCase := fixture.wildcardCase)
    (requirements : List RequirementId := fixture.resolution.requirements) :
    CheckedFunction :=
  withResolution fixture {
    fixture.resolution with
    cases := [literalCase, wildcardCase]
    requirements
  }

private def changeSolved (fixture : Fixture)
    (change : SolvedRequirement → SolvedRequirement) : CheckedFunction := {
  fixture.function with
  solvedRequirements := fixture.function.solvedRequirements.map fun solved =>
    if solved.id = fixture.literalResolution.requirement then change solved
    else solved
}

private def expectErrorAt (label : String) (function : CheckedFunction)
    (site : SourceCoreElaboration.ErrorSite)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
  match SourceCoreElaboration.elaborateFunction function with
  | .ok _ => throw (IO.userError
      s!"{label}: malformed typed match reached Semantic Core")
  | .error error =>
      assertTrue (decide (error.site = site) && accept error.reason)
        s!"{label}: wrong elaboration error {reprStr error}"

private def expectError (fixture : Fixture) (label : String)
    (function : CheckedFunction)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit :=
  expectErrorAt label function (.occurrence fixture.statement.occurrence) accept

private def intPredicate (target : TypeSystem.Ty) : ProgramPredicate :=
  ProgramSignatures.builtinIntPredicate target

private def testCheckedBaseline (fixture : Fixture) : IO Unit := do
  let lowered ← match
      SourceCoreElaboration.elaborateFunction fixture.function with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"checked typed match did not lower: {reprStr error}")
  let run (tag : Nat) := Core.runStateful 40
    (.initial lowered.core [
      .word (Core.Word.ofNatModulo tag),
      .word (Core.Word.ofNatModulo 11),
      .word (Core.Word.ofNatModulo 22)
    ])
  assertTrue (decide (run 0 =
      .done (.word (Core.Word.ofNatModulo 11)) [] &&
      run 7 = .done (.word (Core.Word.ofNatModulo 22)) []))
    "checked typed match did not preserve literal/wildcard branch selection"

private def testRequirementAttachments (fixture : Fixture) : IO Unit := do
  let requirement := fixture.literalResolution.requirement
  let matchMismatch := withResolution fixture {
    fixture.resolution with requirements := []
  }
  expectError fixture "match requirement list" matchMismatch fun reason =>
    reason == .matchRequirementsMismatch [requirement] []

  let detachedLiteral : TypedMatchCase := {
    fixture.literalCase with
    pattern := { fixture.literalCase.pattern with requirements := [] }
  }
  let literalMismatch := withCases fixture detachedLiteral
    fixture.wildcardCase []
  expectError fixture "integer pattern requirement attachment"
    literalMismatch fun reason =>
      reason == .integerLiteralRequirementsMismatch [requirement] []

  let forged : RequirementId := ⟨requirement.index + 1000⟩
  let attachedWildcard : TypedMatchCase := {
    fixture.wildcardCase with
    pattern := { fixture.wildcardCase.pattern with requirements := [forged] }
  }
  let wildcardMismatch := withCases fixture fixture.literalCase
    attachedWildcard [requirement, forged]
  expectError fixture "wildcard pattern requirement attachment"
    wildcardMismatch fun reason =>
      reason == .matchPatternRequirementsMismatch [] [forged]

private def testPatternPayloads (fixture : Fixture) : IO Unit := do
  let sourceMismatch : TypedMatchCase := {
    fixture.literalCase with
    pattern := {
      fixture.literalCase.pattern with
      resolution := .integerLiteral (.decimal "1")
        fixture.literalResolution
    }
  }
  expectError fixture "pattern source payload"
    (withCases fixture sourceMismatch) fun reason =>
      reason == .matchPatternSourceMismatch

  let rawMismatch : TypedMatchCase := {
    fixture.literalCase with
    pattern := {
      fixture.literalCase.pattern with
      resolution := .integerLiteral fixture.literalSource {
        fixture.literalResolution with
        rawValue := fixture.literalResolution.rawValue + 1
      }
    }
  }
  expectError fixture "pattern decoded value"
    (withCases fixture rawMismatch) fun reason =>
      reason == .integerLiteralRawValueMismatch
        fixture.literalResolution.rawValue
        (fixture.literalResolution.rawValue + 1)

  let patternTypeMismatch : TypedMatchCase := {
    fixture.literalCase with
    pattern := { fixture.literalCase.pattern with type := .bool }
  }
  expectError fixture "pattern/scrutinee type"
    (withCases fixture patternTypeMismatch) fun reason =>
      reason == .matchPatternTypeMismatch .word .bool

  let targetMismatch : TypedMatchCase := {
    fixture.literalCase with
    pattern := {
      fixture.literalCase.pattern with
      resolution := .integerLiteral fixture.literalSource {
        fixture.literalResolution with targetType := .bool
      }
    }
  }
  expectError fixture "pattern target type"
    (withCases fixture targetMismatch) fun reason =>
      reason == .integerLiteralTargetTypeMismatch .bool .word

private def testPatternEvidence (fixture : Fixture) : IO Unit := do
  let requirement := fixture.literalResolution.requirement
  let expected := fixture.literalResolution.predicate
  let wrong := intPredicate .bool
  let predicateMismatch := changeSolved fixture fun solved => {
    solved with predicate := wrong
  }
  expectError fixture "pattern predicate" predicateMismatch fun reason =>
    reason == .integerLiteralPredicateMismatch requirement expected wrong

  let evidenceGoalMismatch := changeSolved fixture fun solved => {
    solved with
    evidence := .implementation
      (.byImpl wrong (.builtin .intWord) [])
  }
  expectError fixture "pattern evidence goal" evidenceGoalMismatch fun reason =>
    reason == .integerLiteralEvidenceGoalMismatch requirement expected wrong

  let implementationMismatch := changeSolved fixture fun solved => {
    solved with
    evidence := .implementation
      (.byImpl expected (.builtin .intInteger) [])
  }
  expectError fixture "pattern implementation" implementationMismatch
    fun reason => reason == .integerLiteralImplementationMismatch requirement
      (.builtin .intWord) (.builtin .intInteger)

  let premise : TypedTraitResolution.Evidence :=
    .byImpl expected (.builtin .intWord) []
  let premiseMismatch := changeSolved fixture fun solved => {
    solved with
    evidence := .implementation
      (.byImpl expected (.builtin .intWord) [premise])
  }
  expectError fixture "pattern evidence premises" premiseMismatch fun reason =>
    reason == .integerLiteralPremiseCountMismatch requirement 0 1

private def testHiddenScrutineeIdentity (fixture : Fixture) : IO Unit := do
  let foreignOwner := {
    fixture.function.declaration with
    declarationIndex := fixture.function.declaration.declarationIndex + 1
  }
  let foreignHidden := {
    fixture.resolution.hiddenScrutinee with owner := foreignOwner
  }
  let ownerMismatch := withResolution fixture {
    fixture.resolution with hiddenScrutinee := foreignHidden
  }
  expectError fixture "hidden scrutinee owner" ownerMismatch fun reason =>
    reason == .matchHiddenOwnerMismatch fixture.function.declaration foreignOwner

  let input ← match fixture.function.typedBody.inputs with
    | input :: _ => pure input
    | [] => throw (IO.userError "typed-match fixture lost its input scope")
  let collision := withResolution fixture {
    fixture.resolution with hiddenScrutinee := input.id
  }
  expectError fixture "hidden scrutinee scope collision" collision fun reason =>
    reason == .duplicateMatchHidden input.id

  let branchExpression ← match fixture.literalCase.body with
    | [statement] =>
        match fixture.function.typedBody.lookupStatement? statement with
        | some { form := .returnStmt (some expression), .. } => pure expression
        | _ => throw (IO.userError
            "typed-match fixture lost its literal branch return")
    | body => throw (IO.userError
        s!"typed-match literal branch retained {body.length} statements")
  let hiddenReference : CheckedFunction := {
    fixture.function with
    typedBody := changeExpression fixture.function.typedBody branchExpression
      fun node => {
        node with
        form := .reference "forged-hidden"
          (.local fixture.resolution.hiddenScrutinee)
      }
  }
  expectErrorAt "hidden scrutinee branch visibility" hiddenReference
    (.occurrence branchExpression.occurrence) fun reason =>
      reason == .unknownLocal fixture.resolution.hiddenScrutinee

/-- Validate the checked baseline and reject adversarial mutations at every
trust boundary carried by an executable typed source match. -/
def testSourcePatternMatchingTamper : IO Unit := do
  let fixture ← fixture
  testCheckedBaseline fixture
  testRequirementAttachments fixture
  testPatternPayloads fixture
  testPatternEvidence fixture
  testHiddenScrutineeIdentity fixture

end Tests.SourcePatternMatchingTamper
end

section
-- leanmerge: from Solcore.Test.SourceSpecialization
/-! End-to-end and rejection regressions for closing checked generic source
functions at concrete declaration arguments. -/

set_option autoImplicit false

namespace Tests.SourceSpecialization

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.Frontend.SourceStageAnalysis
open Solcore.TypeSystem

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def checkedProgram : IO CheckedProgram := do
  let content := String.intercalate "\n" [
    "function select<A, B>(left: A, right: B) returns (A) { return left; }",
    "function identity<T>(value: T) returns (T) { return value; }",
    "function stagedIdentity<T>(comptime value: T) returns (comptime<T>) { return value; }",
    "function phantom<T, U>(value: T) returns (T) { return value; }",
    "function apply<T>(f: function(T) returns (T), value: T) returns (T) { return f(value); }",
    "function localPoly(flag: Bool) returns (Word, Bool) {",
    "  let id = lam(value) { return value; };",
    "  return (id(1), id(flag));",
    "}"
  ]
  match checkProgram (workspace content) with
  | .ok checked => pure checked
  | .error errors => throw (IO.userError
      s!"specialization fixture failed checking: {reprStr errors}")

private def checkedNamed (program : CheckedProgram) (name : String) :
    IO (ProgramFunctionSignature × CheckedFunction) := do
  let signatures := program.signatures.functions.filter fun signature =>
    signature.name == name
  let signature ← match signatures with
    | [signature] => pure signature
    | _ => throw (IO.userError
        s!"expected one signature named `{name}`, found {signatures.length}")
  let functions := program.functions.filter fun function =>
    function.declaration == signature.id
  match functions with
  | [function] => pure (signature, function)
  | _ => throw (IO.userError
      s!"expected one checked body named `{name}`, found {functions.length}")

private def word (value : Nat) : Core.Word :=
  ⟨value % Core.wordModulus, Nat.mod_lt _ (by simp [Core.wordModulus])⟩

private def specializeOrThrow (label : String)
    (signature : ProgramFunctionSignature) (function : CheckedFunction)
    (supplied : ParameterSubstitution) :
    IO Solcore.Frontend.SourceSpecialization.SpecializedFunction := do
  match Solcore.Frontend.SourceSpecialization.specializeFunction
      signature function supplied with
  | .ok specialized => pure specialized
  | .error error => throw (IO.userError
      s!"{label}: specialization failed: {reprStr error}")

private def elaborateOrThrow (label : String) (function : CheckedFunction) :
    IO SourceCoreElaboration.ElaboratedFunction := do
  match SourceCoreElaboration.elaborateFunction function with
  | .ok elaborated => pure elaborated
  | .error error => throw (IO.userError
      s!"{label}: specialized body did not lower: {reprStr error}")

private def expectError (label : String)
    (actual : Except Solcore.Frontend.SourceSpecialization.Error
      Solcore.Frontend.SourceSpecialization.SpecializedFunction)
    (expected : Solcore.Frontend.SourceSpecialization.Error) : IO Unit := do
  match actual with
  | .ok _ => throw (IO.userError
      s!"{label}: invalid specialization was accepted")
  | .error error =>
      assertTrue (decide (error = expected))
        s!"{label}: expected {reprStr expected}, found {reprStr error}"

private def testSelect (program : CheckedProgram) : IO Unit := do
  let (signature, function) ← checkedNamed program "select"
  let (a, b) ← match signature.scheme.parameters with
    | [a, b] => pure (a, b)
    | parameters => throw (IO.userError
        s!"select lost its two parameters: {reprStr parameters}")
  let supplied : ParameterSubstitution := [(b, .bool), (a, .word)]
  let specialized ← specializeOrThrow "select" signature function supplied
  assertTrue (decide (
      specialized.key.declaration = signature.id ∧
      specialized.key.arguments = [.word, .bool] ∧
      specialized.declaration = function.declaration ∧
      specialized.parameterSubstitution = [(a, .word), (b, .bool)] ∧
      specialized.function.declaration = function.declaration ∧
      specialized.function.typedBody.owner = function.typedBody.owner ∧
      specialized.function.typedBody.roots = function.typedBody.roots ∧
      specialized.function.typedBody.nodes.map Node.id =
        function.typedBody.nodes.map Node.id))
    "select did not canonicalize arguments or preserve source identities"
  let elaborated ← elaborateOrThrow "select" specialized.function
  assertTrue (decide (elaborated.inputs.values = [.word, .bool] ∧
      elaborated.returnType = .word ∧
      Core.infer? elaborated.inputs.values elaborated.core = some .word))
    "select did not elaborate to its concrete Core signature"
  assertTrue (decide (Core.runStateful 32
      (.initial elaborated.core [.word (word 41), .bool true]) =
        .done (.word (word 41)) []))
    "specialized select did not return its Word input"

private def testIdentity (program : CheckedProgram) : IO Unit := do
  let (signature, function) ← checkedNamed program "identity"
  let parameter ← match signature.scheme.parameters with
    | [parameter] => pure parameter
    | parameters => throw (IO.userError
        s!"identity lost its parameter: {reprStr parameters}")
  let specialized ← specializeOrThrow "identity" signature function
    [(parameter, .bool)]
  let boolInput ← match specialized.function.typedBody.inputs with
    | [input] => pure input
    | inputs => throw (IO.userError
        s!"Bool identity retained {inputs.length} inputs")
  assertTrue (decide (specialized.key.arguments = [.bool] ∧
      specialized.parameterSubstitution = [(parameter, .bool)] ∧
      specialized.stageAnalysis.binderStage? boolInput.id = some .runtime))
    "identity did not retain its Bool specialization key"
  let elaborated ← elaborateOrThrow "identity" specialized.function
  assertTrue (decide (Core.infer? elaborated.inputs.values elaborated.core =
      some .bool ∧ Core.runStateful 16
        (.initial elaborated.core [.bool true]) = .done (.bool true) []))
    "Bool identity did not typecheck and execute"
  let integerSpecialized ← specializeOrThrow "integer identity" signature function
    [(parameter, .integer)]
  let integerInput ← match integerSpecialized.function.typedBody.inputs with
    | [input] => pure input
    | inputs => throw (IO.userError
        s!"integer identity retained {inputs.length} inputs")
  assertTrue (decide
      (integerSpecialized.stageAnalysis.binderStage? integerInput.id =
        some .comptime))
    "specialization did not recompute an integer input as comptime-only"

private def testStagedIdentityMarkers (program : CheckedProgram) : IO Unit := do
  let (signature, function) ← checkedNamed program "stagedIdentity"
  let parameter ← match signature.scheme.parameters with
    | [parameter] => pure parameter
    | parameters => throw (IO.userError
        s!"stagedIdentity lost its parameter: {reprStr parameters}")
  let input ← match function.typedBody.inputs with
    | [input] => pure input
    | inputs => throw (IO.userError
        s!"stagedIdentity retained {inputs.length} inputs")
  assertTrue (decide (signature.parameterComptime = [true] ∧
      signature.returnComptime ∧ input.comptime ∧
      function.returnComptime ∧
      signature.scheme.body = .function (.parameter parameter)
        (.parameter parameter)))
    "generic comptime contract did not reach the checked carrier"
  let specialized ← specializeOrThrow "stagedIdentity" signature function
    [(parameter, .word)]
  let specializedInput ← match specialized.function.typedBody.inputs with
    | [input] => pure input
    | inputs => throw (IO.userError
        s!"specialized stagedIdentity retained {inputs.length} inputs")
  assertTrue (decide (specialized.function.type = .function .word .word ∧
      specializedInput.scheme = .mono .word ∧ specializedInput.comptime ∧
      specialized.function.returnComptime ∧
      specialized.stageAnalysis.binderStage? specializedInput.id =
        some .comptime))
    "specialization changed comptime flags or left them in semantic types"

private def testPhantomParameter (program : CheckedProgram) : IO Unit := do
  let (signature, function) ← checkedNamed program "phantom"
  let (t, unused) ← match signature.scheme.parameters with
    | [t, unused] => pure (t, unused)
    | parameters => throw (IO.userError
        s!"phantom lost its two parameters: {reprStr parameters}")
  let specialized ← specializeOrThrow "phantom" signature function
    [(unused, .word), (t, .bool)]
  assertTrue (decide (specialized.key.arguments = [.bool, .word] ∧
      specialized.parameterSubstitution = [(t, .bool), (unused, .word)]))
    "the unused declaration parameter disappeared from the canonical key"
  let elaborated ← elaborateOrThrow "phantom" specialized.function
  assertTrue (decide (Core.runStateful 16
      (.initial elaborated.core [.bool false]) = .done (.bool false) []))
    "phantom specialization did not execute at its used Bool parameter"

private def testIndirectMetadataSpecialization
    (program : CheckedProgram) : IO Unit := do
  let (signature, function) ← checkedNamed program "apply"
  let parameter ← match signature.scheme.parameters with
    | [parameter] => pure parameter
    | parameters => throw (IO.userError
        s!"apply lost its generic parameter: {reprStr parameters}")
  let specialized ← specializeOrThrow "apply" signature function
    [(parameter, .word)]
  let calls := specialized.function.typedBody.nodes.filterMap fun
    | .expression node =>
        match node.form with
        | .call _ _ (.indirect metadata) => some (node, metadata)
        | _ => none
    | .statement _ => none
  match calls with
  | [(node, metadata)] =>
      assertTrue (decide (node.type = .word ∧ node.coercions = [] ∧
          metadata.argumentTypeBeforeCoercion = .word ∧
          metadata.argumentTypeAfterCoercion = .word ∧
          metadata.argumentCoercions = [] ∧
          metadata.hasValidArgumentCoercionPath))
        "specialization did not close indirect call metadata at Word"
  | _ => throw (IO.userError
      s!"expected one specialized indirect call, found {calls.length}")

private def replaceExpression (function : CheckedFunction)
    (id : ExpressionId) (change : ExpressionNode → ExpressionNode) :
    CheckedFunction := {
  function with typedBody := {
    function.typedBody with
    nodes := function.typedBody.nodes.map fun
      | .expression node =>
          if node.id = id then .expression { change node with id }
          else .expression node
      | .statement node => .statement node
  }
}

private def replaceStatement (function : CheckedFunction)
    (id : StatementId) (change : StatementNode → StatementNode) :
    CheckedFunction := {
  function with typedBody := {
    function.typedBody with
    nodes := function.typedBody.nodes.map fun
      | .expression node => .expression node
      | .statement node =>
          if node.id = id then .statement { change node with id }
          else .statement node
  }
}

private def testLocalPolymorphicLambda
    (program : CheckedProgram) : IO Unit := do
  let (signature, function) ← checkedNamed program "localPoly"
  let bindings := function.typedBody.nodes.filterMap fun
    | .statement node@{ form := .letDecl binder (some initializer), .. } =>
        if binder.name == "id" then some (node, binder, initializer) else none
    | _ => none
  let (statement, binder, initializer) ← match bindings with
    | [binding] => pure binding
    | _ => throw (IO.userError
        "localPoly lost its unique initialized id binder")
  let quantified ← match binder.scheme.quantified with
    | [quantified] => pure quantified
    | variables => throw (IO.userError
        s!"localPoly id has the wrong quantified variables: {reprStr variables}")
  let lambdaNode ← match function.typedBody.lookupExpression? initializer with
    | some node@{ form := .lambda [_] _ _, .. } => pure node
    | _ => throw (IO.userError
        "localPoly id initializer is not a direct unary lambda")
  let specialized ← specializeOrThrow "local polymorphic lambda"
    signature function []
  let specializedBinder ← match specialized.function.typedBody.lookupStatement?
      statement.id with
    | some { form := .letDecl selected (some selectedInitializer), .. } =>
        if selectedInitializer = initializer then pure selected
        else throw (IO.userError
          "specialization changed the polymorphic initializer identity")
    | _ => throw (IO.userError
        "specialization changed the polymorphic let shape")
  let (specializedLambda, specializedParameter, specializedReturnType) ← match
      specialized.function.typedBody.lookupExpression? initializer with
    | some node@{ form := .lambda [parameter] returnType _, .. } =>
        pure (node, parameter, returnType)
    | _ => throw (IO.userError
        "specialization changed the direct lambda initializer")
  assertTrue (Solcore.Frontend.SourceSpecialization.isDirectLambdaInitializer
      specialized.function.typedBody initializer)
    "specialization no longer recognizes the direct lambda initializer"
  assertTrue (decide (specializedBinder.scheme = binder.scheme ∧
      specializedLambda.type = lambdaNode.type ∧
      specializedParameter.scheme.quantified = [] ∧
      specializedParameter.scheme.body = Ty.variable quantified ∧
      specializedReturnType = Ty.variable quantified ∧
      specialized.function.substitution.any fun entry =>
        entry.2 = .variable quantified))
    "specialization did not retain the principal lambda scheme and lexical residual"
  let instantiatedReferenceTypes := specialized.function.typedBody.nodes.filterMap fun
    | .expression node =>
        match node.form with
        | .reference _ (.local selected) =>
            if selected = binder.id then some node.type else none
        | _ => none
    | .statement _ => none
  assertTrue (instantiatedReferenceTypes.length == 2 &&
      instantiatedReferenceTypes.any (· == .function .word .word) &&
      instantiatedReferenceTypes.any (· == .function .bool .bool))
    "polymorphic references outside the initializer did not remain ground"

  let fresh : TypeVarId := ⟨991⟩
  let quantifiedParameter : TypedBinder := {
    specializedParameter with
    scheme := {
      quantified := [fresh]
      body := specializedParameter.scheme.body
    }
  }
  let badLambdaParameter := replaceExpression function initializer fun node =>
    match node.form with
    | .lambda _ returnType body => {
        node with form := .lambda [quantifiedParameter] returnType body
      }
    | _ => node
  expectError "quantified lambda parameter"
    (Solcore.Frontend.SourceSpecialization.specializeFunction signature
      badLambdaParameter [])
    (.polymorphicBinder quantifiedParameter.id [fresh])

  let uninitialized := replaceStatement function statement.id fun node => {
    node with form := .letDecl binder none
  }
  expectError "uninitialized polymorphic let"
    (Solcore.Frontend.SourceSpecialization.specializeFunction signature
      uninitialized [])
    (.polymorphicBinder binder.id [quantified])

  let indirectInitializer := replaceExpression function initializer fun node => {
    node with form := .proxy node.type
  }
  expectError "non-lambda polymorphic initializer"
    (Solcore.Frontend.SourceSpecialization.specializeFunction signature
      indirectInitializer [])
    (.polymorphicBinder binder.id [quantified])

  let forItem : ForItemForm := .letDecl binder (some initializer)
  let forBinder := replaceStatement function statement.id fun node => {
    node with form := .forLoop [forItem] initializer [] []
  }
  expectError "polymorphic for binder"
    (Solcore.Frontend.SourceSpecialization.specializeFunction signature
      forBinder [])
    (.polymorphicBinder binder.id [quantified])

  let pattern : TypedMatchPattern := {
    source := .binder statement.span binder.name
    type := binder.scheme.body
    resolution := .binder binder
  }
  let patternBinder := replaceStatement function statement.id fun node => {
    node with form := .matchWith {
      scrutinee := initializer
      hiddenScrutinee := binder.id
      cases := [{ span := statement.span, pattern, body := [] }]
      defaultBody := none
    }
  }
  expectError "polymorphic pattern binder"
    (Solcore.Frontend.SourceSpecialization.specializeFunction signature
      patternBinder [])
    (.polymorphicBinder binder.id [quantified])

  let leakedInput ← match function.typedBody.inputs with
    | [input] => pure { input with scheme := .mono (Ty.variable quantified) }
    | inputs => throw (IO.userError
        s!"localPoly retained {inputs.length} inputs")
  let leaked : CheckedFunction := {
    function with typedBody := {
      function.typedBody with inputs := [leakedInput]
    }
  }
  expectError "lexically escaped quantified variable"
    (Solcore.Frontend.SourceSpecialization.specializeFunction signature leaked [])
    (.residualType (.flexible quantified))

  let sharedAcrossScopes : CheckedFunction := {
    function with typedBody := {
      function.typedBody with
      roots := function.typedBody.roots ++ [.expression initializer]
    }
  }
  expectError "polymorphic initializer shared across lexical scopes"
    (Solcore.Frontend.SourceSpecialization.specializeFunction signature
      sharedAcrossScopes [])
    (.conflictingResidualScope (.expression initializer) [quantified] [])

  let unboundVariable : TypeVarId := ⟨992⟩
  let unbound : CheckedFunction := {
    function with substitution :=
      function.substitution ++
        [(unboundVariable, Ty.variable unboundVariable)]
  }
  expectError "unbound substitution residual"
    (Solcore.Frontend.SourceSpecialization.specializeFunction signature unbound [])
    (.residualType (.flexible unboundVariable))

private def returnedExpression (function : CheckedFunction) : IO ExpressionId :=
  match function.typedBody.roots with
  | [.statement statement] =>
      match function.typedBody.lookupStatement? statement with
      | some { form := .returnStmt (some expression), .. } => pure expression
      | _ => throw (IO.userError
          "integer-specialization fixture root is not a valued return")
  | _ => throw (IO.userError
      "integer-specialization fixture does not have one statement root")

private def testIntegerLiteralMetadataSpecialization
    (program : CheckedProgram) : IO Unit := do
  let (signature, function) ← checkedNamed program "identity"
  let parameter ← match signature.scheme.parameters with
    | [parameter] => pure parameter
    | parameters => throw (IO.userError
        s!"identity lost its integer-metadata parameter: {reprStr parameters}")
  let expression ← returnedExpression function
  let requirement : RequirementId := ⟨211⟩
  let resolution : IntegerLiteralResolution := {
    rawValue := 9
    targetType := .parameter parameter
    requirement
  }
  let predicate := resolution.predicate
  let carrier := replaceExpression function expression fun node => {
    node with
    form := .integerLiteral (.decimal "9") resolution
    requirements := [requirement]
  }
  let carrier : CheckedFunction := {
    carrier with solvedRequirements := [{
      id := requirement
      predicate
      evidence := .implementation
        (.byImpl predicate (.builtin .intWord) [])
    }]
  }
  let specialized ← specializeOrThrow "integer metadata" signature carrier
    [(parameter, .word)]
  let closedNode ← match specialized.function.typedBody.lookupExpression?
      expression with
    | some node => pure node
    | none => throw (IO.userError
        "specialization lost the integer-literal expression")
  match closedNode.form with
  | .integerLiteral source closed =>
      assertTrue (decide (source = .decimal "9" ∧
          closed.rawValue = 9 ∧ closed.targetType = .word ∧
          closed.requirement = requirement ∧
          closed.predicate = ProgramSignatures.builtinIntPredicate .word ∧
          specialized.function.solvedRequirements.map (·.predicate) =
            [ProgramSignatures.builtinIntPredicate .word] ∧
          specialized.function.solvedRequirements.map (·.evidence.goal) =
            [ProgramSignatures.builtinIntPredicate .word]))
        "rigid specialization did not close integer metadata and evidence together"
  | _ => throw (IO.userError
      "rigid specialization changed the integer-literal expression form")
  let elaborated ← elaborateOrThrow "integer metadata" specialized.function
  assertTrue (decide (Core.runStateful 16
      (.initial elaborated.core [.word (word 99)]) =
        .done (.word (word 9)) []))
    "specialized integer literal did not execute through builtin Int<Word>"
  let unknown : TypeParameterId := ⟨signature.id, 99⟩
  let hidden := replaceExpression function expression fun node => {
    node with form := .integerLiteral (.decimal "9") {
      resolution with targetType := .parameter unknown
    }
  }
  expectError "hidden integer target"
    (Solcore.Frontend.SourceSpecialization.specializeFunction signature hidden
      [(parameter, .word)])
    (.undeclaredObservedParameter unknown)

private def testValidationErrors (program : CheckedProgram) : IO Unit := do
  let (signature, function) ← checkedNamed program "select"
  let (identitySignature, identityFunction) ← checkedNamed program "identity"
  let (a, b) ← match signature.scheme.parameters with
    | [a, b] => pure (a, b)
    | parameters => throw (IO.userError
        s!"select lost its validation parameters: {reprStr parameters}")
  let foreign ← match identitySignature.scheme.parameters with
    | [parameter] => pure parameter
    | parameters => throw (IO.userError
        s!"identity lost its validation parameter: {reprStr parameters}")
  let specialize := Solcore.Frontend.SourceSpecialization.specializeFunction
    signature function
  expectError "missing parameter" (specialize [(a, .word)])
    (.missingSuppliedParameter b)
  expectError "duplicate parameter"
    (specialize [(a, .word), (a, .word), (b, .bool)])
    (.duplicateSuppliedParameter a)
  let unknown : TypeParameterId := ⟨signature.id, 100⟩
  expectError "unknown parameter"
    (specialize [(a, .word), (b, .bool), (unknown, .word)])
    (.unknownSuppliedParameter unknown)
  expectError "foreign parameter"
    (specialize [(a, .word), (b, .bool), (foreign, .word)])
    (.suppliedParameterOwnerMismatch signature.id foreign)
  let metavariable : TypeVarId := ⟨77⟩
  expectError "non-ground argument"
    (specialize [(a, .variable metavariable), (b, .bool)])
    (.nonConcreteArgument a (.flexible metavariable))
  expectError "declaration mismatch"
    (Solcore.Frontend.SourceSpecialization.specializeFunction
      signature identityFunction [(a, .word), (b, .bool)])
    (.declarationMismatch signature.id identityFunction.declaration)
  let (firstInput, secondInput) ← match function.typedBody.inputs with
    | [first, second] => pure (first, second)
    | inputs => throw (IO.userError
        s!"select lost its two input binders: {inputs.length}")
  let markedInput : TypedBinder := { firstInput with comptime := true }
  let wrongParameterComptime : CheckedFunction := {
    function with typedBody := {
      function.typedBody with inputs := [markedInput, secondInput]
    }
  }
  expectError "parameter comptime mismatch"
    (Solcore.Frontend.SourceSpecialization.specializeFunction
      signature wrongParameterComptime [(a, .word), (b, .bool)])
    (.parameterComptimeMismatch [false, false] [true, false])
  let wrongReturnComptime : CheckedFunction := {
    function with returnComptime := true
  }
  expectError "return comptime mismatch"
    (Solcore.Frontend.SourceSpecialization.specializeFunction
      signature wrongReturnComptime [(a, .word), (b, .bool)])
    (.returnComptimeMismatch false true)
  let openVariable : TypeVarId := ⟨78⟩
  let bound : TypeVarId := ⟨79⟩
  let openInput : TypedBinder := {
    firstInput with scheme := .mono (.variable openVariable)
  }
  let polymorphicInput : TypedBinder := {
    secondInput with scheme := { quantified := [bound], body := .variable bound }
  }
  let polymorphic : CheckedFunction := {
    function with typedBody := {
      function.typedBody with inputs := [openInput, polymorphicInput]
    }
  }
  expectError "polymorphic local boundary"
    (Solcore.Frontend.SourceSpecialization.specializeFunction signature
      polymorphic [(b, .bool), (a, .word)])
    (.polymorphicBinder secondInput.id [bound])
  let predicate : ProgramPredicate := {
    trait := signature.id
    subject := .word
    arguments := []
  }
  let goal : ProgramPredicate := { predicate with subject := .bool }
  let requirement : SolvedRequirement := {
    id := ⟨19⟩
    predicate
    evidence := .assumption goal
  }
  let malformed : CheckedFunction := {
    function with solvedRequirements := [requirement]
  }
  expectError "evidence goal mismatch"
    (Solcore.Frontend.SourceSpecialization.specializeFunction signature malformed
      [(b, .bool), (a, .word)])
    (.evidenceGoalMismatch requirement.id predicate goal)

/-- Exercise canonical specialization, Core execution, phantom declaration
parameters, and exact boundary errors from a checked raw workspace. -/
def testSourceSpecialization : IO Unit := do
  let program ← checkedProgram
  testSelect program
  testIdentity program
  testStagedIdentityMarkers program
  testPhantomParameter program
  testIndirectMetadataSpecialization program
  testLocalPolymorphicLambda program
  testIntegerLiteralMetadataSpecialization program
  testValidationErrors program

end Tests.SourceSpecialization
end

section
-- leanmerge: from Solcore.Test.SourceSpecializationWorklist
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! End-to-end regressions for finite whole-program specialization discovery. -/

set_option autoImplicit false

namespace Tests.SourceSpecializationWorklist

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.TypeSystem

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{
    path := "main.solc"
    content := String.intercalate "\n" [
      "trait Eq<T> {}",
      "impl Eq<Word> {}",
      "impl Eq<Bool> {}",
      "trait Coerce<From, To> {",
      "  function coerce(value: From) returns (To);",
      "}",
      "function coercionClosureHelper() returns (function(Word) returns (Word)) { return identity; }",
      "impl Coerce<Word, Bool> {",
      "  function coerce(value: Word) returns (Bool) {",
      "    coercionClosureHelper();",
      "    return true;",
      "  }",
      "}",
      "function identity<T>(value: T) returns (T) { return value; }",
      "function globalIdentity<T>(value: T) returns (T) { return value; }",
      "function choose3<A, B, C>(first: A, second: B, third: C) returns (C) { return third; }",
      "function twice<T>(value: T) returns (T) { return identity(identity(value)); }",
      "function contextualLocal(flag: Bool) returns (Word, Bool) {",
      "  let f = lam(value) { return identity(value); };",
      "  f(2);",
      "  return (f(1), f(flag));",
      "}",
      "function unusedContextualLocal() returns (Word) {",
      "  let f = lam(value) { return identity(value); };",
      "  return 9;",
      "}",
      "function nestedContextualLocal(flag: Bool) returns (Word, Bool) {",
      "  let outer = lam(value) {",
      "    let inner = lam(nestedValue) { return identity(nestedValue); };",
      "    return inner(value);",
      "  };",
      "  return (outer(1), outer(flag));",
      "}",
      "function groundInnerUnderPolymorphicOuter(flag: Bool) returns (Word, Word) {",
      "  let outer = lam(value) {",
      "    let inner = lam(item) { return globalIdentity(item); };",
      "    return inner(1);",
      "  };",
      "  return (outer(1), outer(flag));",
      "}",
      "function siblingContextualLocal(flag: Bool) returns (Word, Bool) {",
      "  let outer = lam(value) {",
      "    let left = lam(item) { return identity(item); };",
      "    let right = lam(item) { return identity(item); };",
      "    left(value);",
      "    return right(value);",
      "  };",
      "  return (outer(1), outer(flag));",
      "}",
      "function depthThreeContextualLocal(flag: Bool) returns (Word, Bool) {",
      "  let outer = lam(value) {",
      "    let middle = lam(item) {",
      "      let inner = lam(nestedValue) { return identity(nestedValue); };",
      "      return inner(item);",
      "    };",
      "    return middle(value);",
      "  };",
      "  return (outer(1), outer(flag));",
      "}",
      "function scopeAwareRecursiveContextualLocal(flag: Bool) returns (Word, Bool) {",
      "  let outer = lam(value) {",
      "    let middle = lam(item) {",
      "      let inner = lam(nestedValue) {",
      "        return choose3(value, item, nestedValue);",
      "      };",
      "      return inner(value);",
      "    };",
      "    return middle(value);",
      "  };",
      "  return (outer(1), outer(flag));",
      "}",
      "function mixedScopeDepthThreeContextualLocal(flag: Bool) returns (Word) {",
      "  let outer = lam(value) {",
      "    let middle = lam(item) {",
      "      let inner = lam(pair) { return identity(pair); };",
      "      return inner((value, item));",
      "    };",
      "    return middle(value);",
      "  };",
      "  outer(1);",
      "  outer(flag);",
      "  return 9;",
      "}",
      "function reusedBinderMixedScopeContextualLocal(flag: Bool) returns (Word) {",
      "  let outer = lam(value) {",
      "    let adapter = lam(item) { return identity(item); };",
      "    adapter(value);",
      "    let middle = lam(item) { return adapter((value, item)); };",
      "    return middle(value);",
      "  };",
      "  outer(1);",
      "  outer(flag);",
      "  return 9;",
      "}",
      "function monomorphicLambdaWrapper() returns (Word) {",
      "  let outer = lam() {",
      "    let f = lam(item) { return identity(item); };",
      "    return f(1);",
      "  };",
      "  return outer();",
      "}",
      "function unusedNestedContextualLocal() returns (Word) {",
      "  let outer = lam(value) {",
      "    let inner = lam(item) { return identity(item); };",
      "    return inner(value);",
      "  };",
      "  return 9;",
      "}",
      "function first<T>(value: T) returns (T) { return value; }",
      "function second<T>(value: T) returns (T) { return value; }",
      "function nested(value: Word) returns (Word) { return first(second(value)); }",
      "function pick<A, B>(left: A, right: B) returns (A) { return left; }",
      "function select(left: Word, right: Bool) returns (Word) { return pick(left, right); }",
      "function loop<T>(value: T) returns (T) { return loop(value); }",
      "function cycleLeft<T>(value: T) returns (T) { return cycleRight(value); }",
      "function cycleRight<U>(value: U) returns (U) { return cycleLeft(value); }",
      "function grow<T>(value: T) { grow((value, value)); return; }",
      "function keep<T>(value: T) returns (T) where T: Eq { return value; }",
      "function qualifiedLocal(flag: Bool) returns (Word, Bool) {",
      "  let f = lam(value) { return keep(value); };",
      "  return (f(1), f(flag));",
      "}",
      "function guarded<T>(guard: T) returns (Word) where T: Eq { return 1; }",
      "function requireBool(value: Bool) returns (Bool) { return value; }",
      "function qualifiedLocalCoerced(flag: Bool) returns (Bool, Bool) {",
      "  let f = lam(value) { return requireBool(guarded(value)); };",
      "  return (f(1), f(flag));",
      "}",
      "function qualifiedLocalResultCoerced(flag: Bool) returns (Bool, Bool) {",
      "  let f = lam(value) -> Bool { return guarded(value); };",
      "  return (f(1), f(flag));",
      "}",
      "function constrained(value: Word) returns (Word) { return keep(value); }",
      "function keepAs<T, U>(guard: T, value: U) returns (U) where T: Eq { return value; }",
      "function localProof(flag: Bool) returns (Word, Bool) {",
      "  let f = lam(value) { return keepAs(1, value); };",
      "  return (f(2), f(flag));",
      "}",
      "function asValue() returns (function(Word) returns (Word)) { return identity; }",
      "function apply(f: function(Word) returns (Word), value: Word) returns (Word) { return f(value); }",
      "function applyProduct(f: function((Word, Bool)) returns (Word), pair: (Word, Bool)) returns (Word) { return f(pair); }",
      "function applySplit(f: function(Word, Bool) returns (Word), left: Word, right: Bool) returns (Word) { return f(left, right); }"
    ]
  }]
  externalLibraries := []
}

private def checkedProgram : IO CheckedProgram := do
  match checkProgram workspace with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"specialization-worklist fixture failed checking: {reprStr errors}")

private def signatureNamed (program : CheckedProgram) (name : String) :
    IO ProgramFunctionSignature := do
  match program.signatures.functions.filter fun signature =>
      signature.name == name with
  | [signature] => pure signature
  | signatures => throw (IO.userError
      s!"expected one signature named `{name}`, found {signatures.length}")

private def traitNamed (program : CheckedProgram) (name : String) :
    IO ProgramTraitSignature := do
  match program.signatures.traits.filter fun signature =>
      signature.name == name with
  | [signature] => pure signature
  | signatures => throw (IO.userError
      s!"expected one trait named `{name}`, found {signatures.length}")

private def functionFor (program : CheckedProgram)
    (signature : ProgramFunctionSignature) : IO CheckedFunction := do
  match program.functions.filter fun function =>
      function.declaration == signature.id with
  | [function] => pure function
  | functions => throw (IO.userError
      s!"expected one body named `{signature.name}`, found {functions.length}")

private def replaceFunction (program : CheckedProgram)
    (replacement : CheckedFunction) : CheckedProgram := {
  program with
  functions := program.functions.map fun function =>
    if function.declaration == replacement.declaration then
      replacement
    else
      function
}

private def firstDirectCall? : List Node → Option (ExpressionId × ExpressionId)
  | [] => none
  | .expression { id, form := .call callee _ (.declaration _), .. } :: _ =>
      some (id, callee)
  | _ :: rest => firstDirectCall? rest

private def firstIndirectCall? :
    List Node → Option (ExpressionNode × IndirectCallResolution)
  | [] => none
  | .expression node@{ form := .call _ _ (.indirect metadata), .. } :: _ =>
      some (node, metadata)
  | _ :: rest => firstIndirectCall? rest

private def setExpressionType (nodes : List Node) (target : ExpressionId)
    (type : Ty) : List Node :=
  nodes.map fun node => match node with
  | .expression expression =>
      if expression.id == target then
        .expression { expression with type }
      else
        node
  | .statement _ => node

private def setLocalBinderScheme (nodes : List Node)
    (target : Resolved.LocalId) (scheme : Scheme) : List Node :=
  nodes.map fun node => match node with
  | .statement statement =>
      match statement.form with
      | .letDecl binder initializer =>
          if binder.id == target then
            .statement {
              statement with
              form := .letDecl { binder with scheme } initializer
            }
          else
            node
      | _ => node
  | .expression _ => node

private def setLocalBinderRequirements (nodes : List Node)
    (target : Resolved.LocalId)
    (requirements : List LocalSchemeRequirement) : List Node :=
  nodes.map fun node => match node with
  | .statement statement =>
      match statement.form with
      | .letDecl binder initializer =>
          if binder.id == target then
            .statement {
              statement with
              form := .letDecl { binder with schemeRequirements := requirements }
                initializer
            }
          else
            node
      | _ => node
  | .expression _ => node

private def setExpressionRequirements (nodes : List Node)
    (target : ExpressionId) (requirements : List RequirementId) : List Node :=
  nodes.map fun node => match node with
  | .expression expression =>
      if expression.id == target then
        .expression { expression with requirements }
      else
        node
  | .statement _ => node

private def setExpressionCoercions (nodes : List Node) (target : ExpressionId)
    (coercions : List CoercionStep) : List Node :=
  nodes.map fun node => match node with
  | .expression expression =>
      if expression.id == target then
        .expression { expression with coercions }
      else
        node
  | .statement _ => node

private def setIndirectMetadata (nodes : List Node) (target : ExpressionId)
    (metadata : IndirectCallResolution) : List Node :=
  nodes.map fun node => match node with
  | .expression expression =>
      if expression.id == target then
        match expression.form with
        | .call callee arguments (.indirect _) =>
            .expression {
              expression with
              form := .call callee arguments (.indirect metadata)
            }
        | _ => node
      else
        node
  | .statement _ => node

private def setCallResolution (nodes : List Node) (target : ExpressionId)
    (resolution : CallResolution) : List Node :=
  nodes.map fun node => match node with
  | .expression expression =>
      if expression.id == target then
        match expression.form with
        | .call callee arguments _ =>
            .expression {
              expression with
              form := .call callee arguments resolution
            }
        | _ => node
      else
        node
  | .statement _ => node

private def setDirectInstantiationMarkers (nodes : List Node)
    (call callee : ExpressionId) (parameterComptime : List Bool)
    (returnComptime : Bool) : List Node :=
  nodes.map fun node => match node with
  | .expression expression =>
      if expression.id == callee then
        match expression.form with
        | .reference name (.declaration instantiation) =>
            .expression {
              expression with
              form := .reference name (.declaration {
                instantiation with parameterComptime, returnComptime
              })
            }
        | _ => node
      else if expression.id == call then
        match expression.form with
        | .call target arguments (.declaration instantiation) =>
            .expression {
              expression with
              form := .call target arguments (.declaration {
                instantiation with parameterComptime, returnComptime
              })
            }
        | _ => node
      else
        node
  | .statement _ => node

private def eraseExpression (nodes : List Node)
    (target : ExpressionId) : List Node :=
  nodes.filter fun node => match node with
  | .expression expression => expression.id != target
  | .statement _ => true

private def monomorphicRequest (signature : ProgramFunctionSignature) :
    SourceSpecializationWorklist.Request := {
  declaration := signature.id
  parameterSubstitution := []
}

private def unaryRequest (signature : ProgramFunctionSignature) (type : Ty) :
    IO SourceSpecializationWorklist.Request := do
  match signature.scheme.parameters with
  | [parameter] => pure {
      declaration := signature.id
      parameterSubstitution := [(parameter, type)]
    }
  | parameters => throw (IO.userError
      s!"expected one generic parameter for `{signature.name}`, found {parameters.length}")

private def runOrThrow (label : String) (program : CheckedProgram)
    (requests : List SourceSpecializationWorklist.Request) (budget : Nat) :
    IO SourceSpecializationWorklist.Outcome := do
  match SourceSpecializationWorklist.run program requests budget with
  | .ok outcome => pure outcome
  | .error error => throw (IO.userError
      s!"{label}: worklist failed: {reprStr error}")

private def testBreadthFirstDiscovery (program : CheckedProgram) : IO Unit := do
  let identity ← signatureNamed program "identity"
  let twice ← signatureNamed program "twice"
  let request ← unaryRequest twice .word
  let twiceKey : SourceSpecialization.SpecializationKey := {
    declaration := twice.id
    arguments := [.word]
  }
  match ← runOrThrow "twice" program [request] 2 with
  | .complete plan =>
      assertTrue (decide (plan.seedKeys = [twiceKey] ∧
          plan.specializations.map (·.declaration) =
          [twice.id, identity.id]))
        "canonical roots or FIFO first-discovery order were not retained"
      assertTrue (decide (plan.specializations.map (·.key.arguments) =
          [[.word], [.word]]))
        "a nested direct-call instantiation did not specialize to Word"
      assertTrue (decide (plan.callEdges.length = 2 ∧
          (plan.callEdges.map (·.occurrence)).eraseDups.length = 2 ∧
          plan.callEdges.all fun edge =>
            edge.caller.declaration = twice.id ∧
            edge.callee.declaration = identity.id))
        "two syntactic calls to one canonical callee did not retain two edges"
      assertTrue plan.referenceEdges.isEmpty
        "direct-call callee children were duplicated as reference edges"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"canonical complete plan failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"twice: expected a complete plan, found {reprStr outcome}")
  match ← runOrThrow "twice budget" program [request] 1 with
  | .budgetExhausted plan next pending =>
      assertTrue (decide (plan.specializations.length = 1 ∧
          plan.callEdges.length = 2 ∧ next.declaration = identity.id ∧
          next.arguments = [.word] ∧ pending.length = 2))
        "budget exhaustion did not expose the first unseen canonical key"
  | outcome => throw (IO.userError
      s!"twice budget: expected exhaustion, found {reprStr outcome}")
  match ← runOrThrow "duplicate roots" program [request, request] 2 with
  | .complete plan =>
      assertTrue (decide (plan.seedKeys = [twiceKey, twiceKey] ∧
          plan.specializations.length = 2 ∧ plan.callEdges.length = 2))
        "duplicate roots were lost or charged as duplicate specializations"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"duplicate canonical roots failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"duplicate roots: expected a complete plan, found {reprStr outcome}")

private def testContextualLocalPolymorphicCalls
    (program : CheckedProgram) : IO Unit := do
  let identity ← signatureNamed program "identity"
  let contextual ← signatureNamed program "contextualLocal"
  let function ← functionFor program contextual
  let (binder, initializer) ← match function.typedBody.nodes.filterMap fun
      | .statement { form := .letDecl binder (some initializer), .. } =>
          if binder.name == "f" then some (binder, initializer) else none
      | _ => none with
    | [(binder, initializer)] => pure (binder, initializer)
    | bindings => throw (IO.userError
        s!"contextualLocal retained {bindings.length} binders named `f`")
  let quantified ← match binder.scheme.quantified with
    | [quantified] => pure quantified
    | variables => throw (IO.userError
        s!"contextualLocal `f` retained {variables.length} quantified variables")
  let declarationParameter ← match identity.scheme.parameters with
    | [parameter] => pure parameter
    | parameters => throw (IO.userError
        s!"identity retained {parameters.length} declaration parameters")
  let (call, callee, callInstantiation) ← match
      function.typedBody.nodes.findSome? fun
        | .expression node@{
            form := .call callee _ (.declaration instantiation), .. } =>
            if instantiation.declaration == identity.id then
              some (node, callee, instantiation)
            else
              none
        | _ => none with
    | some selected => pure selected
    | none => throw (IO.userError
        "contextualLocal lost its declaration call to identity")
  let calleeNode ← match function.typedBody.lookupExpression? callee with
    | some node@{ form := .reference _ (.declaration _), .. } => pure node
    | _ => throw (IO.userError
        "contextualLocal identity call lost its declaration-reference child")
  let localReferenceTypes := function.typedBody.nodes.filterMap fun
    | .expression node@{ form := .reference _ (.local selected), .. } =>
        if selected == binder.id then some node.rawType else none
    | _ => none
  let residual := Ty.variable quantified
  assertTrue (SourceSpecialization.isDirectLambdaInitializer
      function.typedBody initializer && decide (
        binder.scheme.body = .function residual residual ∧
        call.rawType = residual ∧ call.type = residual ∧
        callInstantiation.parameterSubstitution =
          [(declarationParameter, residual)] ∧
        callInstantiation.type = .function residual residual ∧
        callInstantiation.predicates = [] ∧
        calleeNode.rawType = .function residual residual ∧
        localReferenceTypes = [
          Ty.function .word .word,
          Ty.function .word .word,
          Ty.function .bool .bool]))
    "contextualLocal did not retain its principal template and three concrete uses"

  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := contextual.id
    arguments := []
  }
  let wordKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.word]
  }
  let boolKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.bool]
  }
  let request := monomorphicRequest contextual
  match ← runOrThrow "contextual local calls" program [request] 3 with
  | .complete plan =>
      let expectedEdges : List SourceSpecializationWorklist.CallEdge := [{
        caller := entryKey
        occurrence := call.id
        callee := wordKey
      }, {
        caller := entryKey
        occurrence := call.id
        callee := boolKey
      }]
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) = [entryKey, wordKey, boolKey] ∧
          plan.callEdges = expectedEdges ∧
          plan.callEdges.eraseDups.length = 2 ∧
          plan.referenceEdges = []))
        "contextual local calls lost canonical keys or exact deduplicated edges"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"contextual local plan failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"contextual local calls: expected a complete plan, found {reprStr outcome}")

  match ← runOrThrow "contextual local budget one" program [request] 1 with
  | .budgetExhausted plan next pending =>
      assertTrue (decide (
          plan.specializations.map (·.key) = [entryKey] ∧
          plan.callEdges.length = 2 ∧
          plan.callEdges.map (·.occurrence) = [call.id, call.id] ∧
          next = wordKey ∧ pending.length = 2))
        "contextual local budget one lost its concrete frontier or edge ledger"
  | outcome => throw (IO.userError
      s!"contextual local budget one: expected exhaustion, found {reprStr outcome}")

  match ← runOrThrow "contextual local budget two" program [request] 2 with
  | .budgetExhausted plan next pending =>
      assertTrue (decide (
          plan.specializations.map (·.key) = [entryKey, wordKey] ∧
          plan.callEdges.length = 2 ∧ next = boolKey ∧
          pending.length = 1))
        "contextual local budget two lost its second concrete frontier"
  | outcome => throw (IO.userError
      s!"contextual local budget two: expected exhaustion, found {reprStr outcome}")

  let unused ← signatureNamed program "unusedContextualLocal"
  match ← runOrThrow "unused contextual local" program
      [monomorphicRequest unused] 1 with
  | .complete plan =>
      assertTrue (decide (plan.specializations.map (·.key.declaration) =
          [unused.id] ∧ plan.callEdges = [] ∧ plan.referenceEdges = []))
        "an unused polymorphic lambda unnecessarily specialized its open body"
  | outcome => throw (IO.userError
      s!"unused contextual local: expected a complete plan, found {reprStr outcome}")

  let wordReference ← match function.typedBody.nodes.findSome? fun
      | .expression node@{ form := .reference _ (.local selected), .. } =>
          if selected == binder.id &&
              node.rawType == Ty.function .word .word then
            some node
          else
            none
      | _ => none with
    | some reference => pure reference
    | none => throw (IO.userError
        "contextualLocal lost its concrete Word reference to `f`")
  let mismatchedScheme : Scheme := {
    binder.scheme with body := .function residual .bool
  }
  let mismatchedFunction : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := setLocalBinderScheme function.typedBody.nodes
        binder.id mismatchedScheme
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction program mismatchedFunction) [request] 3 with
  | .error (.localPolymorphicInstanceMismatch occurrence binderId scheme
      (.function .word .word)) =>
      assertTrue (decide (occurrence = wordReference.id ∧ binderId = binder.id ∧
          scheme = mismatchedScheme))
        "local scheme-instance mismatch lost its occurrence or binder"
  | result => throw (IO.userError
      s!"a malformed ground local scheme instance was accepted: {reprStr result}")

private def testDepthTwoContextualLocalPolymorphicCalls
    (program : CheckedProgram) : IO Unit := do
  let identity ← signatureNamed program "identity"
  let nested ← signatureNamed program "nestedContextualLocal"
  let function ← functionFor program nested
  let call ← match function.typedBody.nodes.findSome? fun
      | .expression node@{
          form := .call _ _ (.declaration instantiation), .. } =>
          if instantiation.declaration == identity.id then some node else none
      | _ => none with
    | some call => pure call
    | none => throw (IO.userError
        "nestedContextualLocal lost its declaration call to identity")
  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := nested.id
    arguments := []
  }
  let wordKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.word]
  }
  let boolKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.bool]
  }
  let expectedEdges : List SourceSpecializationWorklist.CallEdge := [{
    caller := entryKey
    occurrence := call.id
    callee := wordKey
  }, {
    caller := entryKey
    occurrence := call.id
    callee := boolKey
  }]
  let request := monomorphicRequest nested

  match ← runOrThrow "depth-two contextual local calls" program
      [request] 3 with
  | .complete plan =>
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) = [entryKey, wordKey, boolKey] ∧
          plan.callEdges = expectedEdges ∧
          plan.callEdges.eraseDups.length = 2 ∧
          plan.callEdges.map (·.occurrence) = [call.id, call.id] ∧
          plan.referenceEdges = []))
        "depth-two local calls lost canonical keys or exact deduplicated edges"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"depth-two local plan failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"depth-two local calls: expected a complete plan, found {reprStr outcome}")

  match ← runOrThrow "depth-two contextual budget one" program
      [request] 1 with
  | .budgetExhausted plan next pending =>
      assertTrue (decide (
          plan.specializations.map (·.key) = [entryKey] ∧
          plan.callEdges = expectedEdges ∧ next = wordKey ∧
          pending.length = 2))
        "depth-two budget one lost its concrete frontier or edge ledger"
  | outcome => throw (IO.userError
      s!"depth-two budget one: expected exhaustion, found {reprStr outcome}")

  match ← runOrThrow "depth-two contextual budget two" program
      [request] 2 with
  | .budgetExhausted plan next pending =>
      assertTrue (decide (
          plan.specializations.map (·.key) = [entryKey, wordKey] ∧
          plan.callEdges = expectedEdges ∧ next = boolKey ∧
          pending.length = 1))
        "depth-two budget two lost its second concrete frontier"
  | outcome => throw (IO.userError
      s!"depth-two budget two: expected exhaustion, found {reprStr outcome}")

private def testGroundInnerUnderPolymorphicOuter
    (program : CheckedProgram) : IO Unit := do
  let identity ← signatureNamed program "globalIdentity"
  let entry ← signatureNamed program "groundInnerUnderPolymorphicOuter"
  let function ← functionFor program entry
  let outer ← match function.typedBody.nodes.findSome? fun
      | .statement { form := .letDecl binder (some _), .. } =>
          if binder.name == "outer" then some binder else none
      | _ => none with
    | some binder => pure binder
    | none => throw (IO.userError
        "ground-inner fixture lost its `outer` binder")
  let inner ← match function.typedBody.nodes.findSome? fun
      | .statement { form := .letDecl binder (some _), .. } =>
          if binder.name == "inner" then some binder else none
      | _ => none with
    | some binder => pure binder
    | none => throw (IO.userError
        "ground-inner fixture lost its `inner` binder")
  let quantified ← match inner.scheme.quantified with
    | [quantified] => pure quantified
    | variables => throw (IO.userError
        s!"ground-inner `inner` retained {variables.length} quantified variables")
  let declarationParameter ← match identity.scheme.parameters with
    | [parameter] => pure parameter
    | parameters => throw (IO.userError
        s!"globalIdentity retained {parameters.length} parameters")
  let innerReference ← match function.typedBody.nodes.filterMap fun
      | .expression node@{ form := .reference _ (.local selected), .. } =>
          if selected == inner.id then some node else none
      | _ => none with
    | [reference] => pure reference
    | references => throw (IO.userError
        s!"ground-inner fixture retained {references.length} inner references")
  let (call, instantiation) ← match
      function.typedBody.nodes.findSome? fun
        | .expression node@{
            form := .call _ _ (.declaration instantiation), .. } =>
            if instantiation.declaration == identity.id then
              some (node, instantiation)
            else
              none
        | _ => none with
    | some selected => pure selected
    | none => throw (IO.userError
        "ground-inner fixture lost its globalIdentity call")
  let residual := Ty.variable quantified
  assertTrue (decide (
      outer.scheme.quantified.length = 1 ∧
      inner.scheme.body = .function residual residual ∧
      innerReference.rawType = .function .word .word ∧
      instantiation.parameterSubstitution = [(declarationParameter, residual)] ∧
      instantiation.type = .function residual residual))
    "ground-inner fixture lost its ground use or open helper metadata"

  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := entry.id
    arguments := []
  }
  let wordKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.word]
  }
  let expectedEdge : SourceSpecializationWorklist.CallEdge := {
    caller := entryKey
    occurrence := call.id
    callee := wordKey
  }
  match ← runOrThrow "ground inner under polymorphic outer" program
      [monomorphicRequest entry] 2 with
  | .complete plan =>
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) = [entryKey, wordKey] ∧
          plan.callEdges = [expectedEdge] ∧
          plan.callEdges.eraseDups.length = 1 ∧
          plan.referenceEdges = []))
        "ground inner use was duplicated or lost across outer contexts"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .error error => throw (IO.userError
          s!"ground-inner plan failed replay validation: {reprStr error}")
      | .ok () => do
          let compiled ← SourceCoreUnifiedCorpusSupport.preparePlan
            "ground inner under polymorphic outer" program plan entryKey
          match ← SourceCoreUnifiedCorpusSupport.observe compiled entryKey [.bool true] with
          | .done (.product (.word left) (.word right)) _ =>
              let expected := Core.Word.ofNatModulo 1
              assertTrue (left == expected && right == expected)
                "ground-inner cached Core returned the wrong Word pair"
          | result => throw (IO.userError
              s!"ground-inner cached Core returned {reprStr result}")
  | outcome => throw (IO.userError
      s!"ground-inner worklist expected a complete plan, found {reprStr outcome}")

private def testSiblingContextualLocalPolymorphicCalls
    (program : CheckedProgram) : IO Unit := do
  let identity ← signatureNamed program "identity"
  let siblings ← signatureNamed program "siblingContextualLocal"
  let function ← functionFor program siblings
  let calls := function.typedBody.nodes.filterMap fun
    | .expression node@{
        form := .call _ _ (.declaration instantiation), .. } =>
        if instantiation.declaration == identity.id then some node else none
    | _ => none
  let (leftCall, rightCall) ← match calls with
    | [leftCall, rightCall] => pure (leftCall, rightCall)
    | calls => throw (IO.userError
        s!"siblingContextualLocal retained {calls.length} identity calls")
  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := siblings.id
    arguments := []
  }
  let wordKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.word]
  }
  let boolKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.bool]
  }
  let expectedEdges : List SourceSpecializationWorklist.CallEdge := [
    { caller := entryKey, occurrence := leftCall.id, callee := wordKey },
    { caller := entryKey, occurrence := leftCall.id, callee := boolKey },
    { caller := entryKey, occurrence := rightCall.id, callee := wordKey },
    { caller := entryKey, occurrence := rightCall.id, callee := boolKey }
  ]
  match ← runOrThrow "sibling contextual local calls" program
      [monomorphicRequest siblings] 3 with
  | .complete plan =>
      let exactEdges :=
        plan.callEdges.length == expectedEdges.length &&
        plan.callEdges.eraseDups.length == expectedEdges.length &&
        plan.callEdges.all expectedEdges.contains &&
        expectedEdges.all plan.callEdges.contains
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) = [entryKey, wordKey, boolKey] ∧
          plan.referenceEdges = []) && exactEdges)
        "sibling contexts lost a concrete key or one of four exact call edges"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"sibling contextual plan failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"sibling contextual calls: expected a complete plan, found {reprStr outcome}")

private def testDepthThreeContextualLocalPolymorphicCalls
    (program : CheckedProgram) : IO Unit := do
  let identity ← signatureNamed program "identity"
  let nested ← signatureNamed program "depthThreeContextualLocal"
  let function ← functionFor program nested
  let call ← match function.typedBody.nodes.findSome? fun
      | .expression node@{
          form := .call _ _ (.declaration instantiation), .. } =>
          if instantiation.declaration == identity.id then some node else none
      | _ => none with
    | some call => pure call
    | none => throw (IO.userError
        "depth-three fixture lost its declaration call to identity")
  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := nested.id
    arguments := []
  }
  let wordKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.word]
  }
  let boolKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.bool]
  }
  let expectedEdges : List SourceSpecializationWorklist.CallEdge := [
    { caller := entryKey, occurrence := call.id, callee := wordKey },
    { caller := entryKey, occurrence := call.id, callee := boolKey }
  ]
  match ← runOrThrow "depth-three contextual local calls" program
      [monomorphicRequest nested] 3 with
  | .complete plan =>
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) = [entryKey, wordKey, boolKey] ∧
          plan.callEdges = expectedEdges ∧
          plan.callEdges.eraseDups.length = 2 ∧
          plan.referenceEdges = []))
        "depth-three recursion lost its Word/Bool identity instances"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"depth-three contextual plan failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"depth-three contextual calls: expected complete, found {reprStr outcome}")

private def testScopeAwareRecursiveContextualLocalPolymorphicCalls
    (program : CheckedProgram) : IO Unit := do
  let choose3 ← signatureNamed program "choose3"
  let nested ← signatureNamed program "scopeAwareRecursiveContextualLocal"
  let function ← functionFor program nested
  let inner ← match function.typedBody.nodes.findSome? fun
      | .statement { form := .letDecl binder (some _), .. } =>
          if binder.name == "inner" then some binder else none
      | _ => none with
    | some binder => pure binder
    | none => throw (IO.userError
        "scope-aware fixture lost its `inner` binder")
  let innerReference ← match function.typedBody.nodes.findSome? fun
      | .expression node@{ form := .reference _ (.local selected), .. } =>
          if selected == inner.id then some node else none
      | _ => none with
    | some reference => pure reference
    | none => throw (IO.userError
        "scope-aware fixture lost its `inner` reference")
  let (call, instantiation) ← match
      function.typedBody.nodes.findSome? fun
        | .expression node@{
            form := .call _ _ (.declaration instantiation), .. } =>
            if instantiation.declaration == choose3.id then
              some (node, instantiation)
            else
              none
        | _ => none with
    | some selected => pure selected
    | none => throw (IO.userError
        "scope-aware fixture lost its declaration call to choose3")
  let metadataVariables :=
    (instantiation.parameterSubstitution.flatMap fun entry =>
      entry.2.freeVariables).eraseDups
  assertTrue (decide (
      innerReference.rawType.freeVariables.length = 1 ∧
      metadataVariables.length = 3))
    "scope-aware fixture did not separate its reference type from helper metadata"
  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := nested.id
    arguments := []
  }
  let wordKey : SourceSpecialization.SpecializationKey := {
    declaration := choose3.id
    arguments := [.word, .word, .word]
  }
  let boolKey : SourceSpecialization.SpecializationKey := {
    declaration := choose3.id
    arguments := [.bool, .bool, .bool]
  }
  let expectedEdges : List SourceSpecializationWorklist.CallEdge := [
    { caller := entryKey, occurrence := call.id, callee := wordKey },
    { caller := entryKey, occurrence := call.id, callee := boolKey }
  ]
  match ← runOrThrow "scope-aware recursive contextual calls" program
      [monomorphicRequest nested] 3 with
  | .complete plan =>
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) = [entryKey, wordKey, boolKey] ∧
          plan.callEdges = expectedEdges ∧
          plan.callEdges.eraseDups.length = 2 ∧
          plan.referenceEdges = []))
        "scope-aware recursion lost its triple-ground helper instances"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"scope-aware contextual plan failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"scope-aware calls: expected a complete plan, found {reprStr outcome}")

private def testMixedScopeDepthThreeContextualLocalPolymorphicCalls
    (program : CheckedProgram) : IO Unit := do
  let identity ← signatureNamed program "identity"
  let nested ← signatureNamed program "mixedScopeDepthThreeContextualLocal"
  let function ← functionFor program nested
  let inner ← match function.typedBody.nodes.findSome? fun
      | .statement { form := .letDecl binder (some _), .. } =>
          if binder.name == "inner" then some binder else none
      | _ => none with
    | some binder => pure binder
    | none => throw (IO.userError
        "mixed-scope depth-three fixture lost its `inner` binder")
  let openReference ← match function.typedBody.nodes.findSome? fun
      | .expression node@{ form := .reference _ (.local selected), .. } =>
          if selected == inner.id && node.rawType.freeVariables.length == 2 then
            some node
          else
            none
      | _ => none with
    | some reference => pure reference
    | none => throw (IO.userError
        "mixed-scope depth-three fixture lost its two-variable inner reference")
  let expectedVariables := openReference.rawType.freeVariables
  assertTrue (expectedVariables.length == 2)
    "mixed-scope inner reference did not retain outer and middle variables"
  let call ← match function.typedBody.nodes.findSome? fun
      | .expression node@{
          form := .call _ _ (.declaration instantiation), .. } =>
          if instantiation.declaration == identity.id then some node else none
      | _ => none with
    | some call => pure call
    | none => throw (IO.userError
        "mixed-scope depth-three fixture lost its identity call")
  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := nested.id
    arguments := []
  }
  let wordProduct := Ty.product .word .word
  let boolProduct := Ty.product .bool .bool
  let wordKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [wordProduct]
  }
  let boolKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [boolProduct]
  }
  let expectedEdges : List SourceSpecializationWorklist.CallEdge := [
    { caller := entryKey, occurrence := call.id, callee := wordKey },
    { caller := entryKey, occurrence := call.id, callee := boolKey }
  ]
  match ← runOrThrow "mixed-scope depth-three calls" program
      [monomorphicRequest nested] 3 with
  | .complete plan =>
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) = [entryKey, wordKey, boolKey] ∧
          plan.callEdges = expectedEdges ∧
          plan.callEdges.eraseDups.length = 2 ∧
          plan.referenceEdges = []))
        "mixed-scope recursion lost its product identity instances"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"mixed-scope contextual plan failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"mixed-scope calls: expected a complete plan, found {reprStr outcome}")

private def testReusedBinderMixedScopeContextualLocalPolymorphicCalls
    (program : CheckedProgram) : IO Unit := do
  let identity ← signatureNamed program "identity"
  let nested ← signatureNamed program "reusedBinderMixedScopeContextualLocal"
  let function ← functionFor program nested
  let adapter ← match function.typedBody.nodes.findSome? fun
      | .statement { form := .letDecl binder (some _), .. } =>
          if binder.name == "adapter" then some binder else none
      | _ => none with
    | some binder => pure binder
    | none => throw (IO.userError
        "reused-binder fixture lost its `adapter` binder")
  let adapterReferences := function.typedBody.nodes.filterMap fun
    | .expression node@{ form := .reference _ (.local selected), .. } =>
        if selected == adapter.id then some node else none
    | _ => none
  let directReference ← match adapterReferences.find? fun node =>
      node.rawType.freeVariables.length == 1 with
    | some reference => pure reference
    | none => throw (IO.userError
        "reused-binder fixture lost its direct-child adapter reference")
  let mixedReference ← match adapterReferences.find? fun node =>
      node.rawType.freeVariables.length == 2 with
    | some reference => pure reference
    | none => throw (IO.userError
        "reused-binder fixture lost its mixed-scope adapter reference")
  assertTrue (directReference.id != mixedReference.id)
    "reused-binder fixture collapsed its distinct adapter occurrences"
  assertTrue (mixedReference.rawType.freeVariables.length == 2)
    "reused-binder mixed occurrence lost an enclosing variable"
  let call ← match function.typedBody.nodes.findSome? fun
      | .expression node@{
          form := .call _ _ (.declaration instantiation), .. } =>
          if instantiation.declaration == identity.id then some node else none
      | _ => none with
    | some call => pure call
    | none => throw (IO.userError
        "reused-binder fixture lost its identity call")
  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := nested.id
    arguments := []
  }
  let wordKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.word]
  }
  let boolKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.bool]
  }
  let wordProductKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.product .word .word]
  }
  let boolProductKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.product .bool .bool]
  }
  let expectedEdges : List SourceSpecializationWorklist.CallEdge := [
    { caller := entryKey, occurrence := call.id, callee := wordKey },
    { caller := entryKey, occurrence := call.id, callee := boolKey },
    { caller := entryKey, occurrence := call.id, callee := wordProductKey },
    { caller := entryKey, occurrence := call.id, callee := boolProductKey }
  ]
  match ← runOrThrow "reused-binder mixed-scope calls" program
      [monomorphicRequest nested] 5 with
  | .complete plan =>
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) =
            [entryKey, wordKey, boolKey, wordProductKey, boolProductKey] ∧
          plan.callEdges = expectedEdges ∧
          plan.callEdges.eraseDups.length = 4 ∧
          plan.referenceEdges = []))
        "reused binder lost a direct or mixed product identity instance"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"reused-binder contextual plan failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"reused-binder calls: expected a complete plan, found {reprStr outcome}")

private def testMonomorphicLambdaWrapperContextualLocal
    (program : CheckedProgram) : IO Unit := do
  let identity ← signatureNamed program "identity"
  let wrapper ← signatureNamed program "monomorphicLambdaWrapper"
  let function ← functionFor program wrapper
  let outer ← match function.typedBody.nodes.findSome? fun
      | .statement { form := .letDecl binder (some _), .. } =>
          if binder.name == "outer" then some binder else none
      | _ => none with
    | some binder => pure binder
    | none => throw (IO.userError
        "monomorphic-wrapper fixture lost its `outer` binder")
  let inner ← match function.typedBody.nodes.findSome? fun
      | .statement { form := .letDecl binder (some _), .. } =>
          if binder.name == "f" then some binder else none
      | _ => none with
    | some binder => pure binder
    | none => throw (IO.userError
        "monomorphic-wrapper fixture lost its `f` binder")
  assertTrue (outer.scheme.quantified.isEmpty &&
      inner.scheme.quantified.length == 1)
    "monomorphic-wrapper fixture did not retain its intended schemes"
  let call ← match function.typedBody.nodes.findSome? fun
      | .expression node@{
          form := .call _ _ (.declaration instantiation), .. } =>
          if instantiation.declaration == identity.id then some node else none
      | _ => none with
    | some call => pure call
    | none => throw (IO.userError
        "monomorphic-wrapper fixture lost its identity call")
  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := wrapper.id
    arguments := []
  }
  let wordKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.word]
  }
  let expectedEdge : SourceSpecializationWorklist.CallEdge := {
    caller := entryKey
    occurrence := call.id
    callee := wordKey
  }
  match ← runOrThrow "monomorphic lambda wrapper" program
      [monomorphicRequest wrapper] 2 with
  | .complete plan =>
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) = [entryKey, wordKey] ∧
          plan.callEdges = [expectedEdge] ∧
          plan.referenceEdges = []))
        "ground local use under a monomorphic lambda wrapper was not discovered"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"monomorphic-wrapper plan failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"monomorphic wrapper: expected a complete plan, found {reprStr outcome}")

private def testUnusedNestedContextualLocal
    (program : CheckedProgram) : IO Unit := do
  let unused ← signatureNamed program "unusedNestedContextualLocal"
  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := unused.id
    arguments := []
  }
  match ← runOrThrow "unused nested contextual local" program
      [monomorphicRequest unused] 1 with
  | .complete plan =>
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) = [entryKey] ∧
          plan.callEdges = [] ∧ plan.referenceEdges = []))
        "an unreachable nested polymorphic template was scanned or rejected"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"unused nested local plan failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"unused nested local: expected a complete plan, found {reprStr outcome}")

private def testDerivedCanonicalization (program : CheckedProgram) : IO Unit := do
  let pick ← signatureNamed program "pick"
  let select ← signatureNamed program "select"
  match ← runOrThrow "select" program [monomorphicRequest select] 2 with
  | .complete plan =>
      match plan.specializations with
      | [_, specializedPick] =>
          assertTrue (decide (specializedPick.declaration = pick.id ∧
              specializedPick.key.arguments = [.word, .bool]))
            "derived raw substitution was not canonicalized in signature order"
      | specializations => throw (IO.userError
          s!"select: expected two specializations, found {specializations.length}")
  | outcome => throw (IO.userError
      s!"select: expected a complete plan, found {reprStr outcome}")

private def testTypedNodeOrder (program : CheckedProgram) : IO Unit := do
  let first ← signatureNamed program "first"
  let second ← signatureNamed program "second"
  let nested ← signatureNamed program "nested"
  match ← runOrThrow "nested" program [monomorphicRequest nested] 3 with
  | .complete plan =>
      assertTrue (decide (plan.specializations.map (·.declaration) =
          [nested.id, second.id, first.id] ∧
          plan.callEdges.map (·.callee.declaration) =
            [second.id, first.id]))
        "nested direct calls did not follow deterministic typed-node order"
  | outcome => throw (IO.userError
      s!"nested: expected a complete plan, found {reprStr outcome}")

private def testRecursiveKeys (program : CheckedProgram) : IO Unit := do
  let loop ← signatureNamed program "loop"
  let loopRequest ← unaryRequest loop .word
  match ← runOrThrow "loop" program [loopRequest] 1 with
  | .complete plan =>
      match plan.callEdges with
      | [edge] =>
          assertTrue (decide (plan.specializations.length = 1 ∧
              edge.caller = edge.callee))
            "same-key self recursion consumed another specialization"
      | edges => throw (IO.userError
          s!"loop: expected one self edge, found {edges.length}")
  | outcome => throw (IO.userError
      s!"loop: expected a complete plan, found {reprStr outcome}")
  let cycleLeft ← signatureNamed program "cycleLeft"
  let cycleRight ← signatureNamed program "cycleRight"
  let cycleRequest ← unaryRequest cycleLeft .word
  match ← runOrThrow "mutual cycle" program [cycleRequest] 2 with
  | .complete plan =>
      assertTrue (decide (plan.specializations.map (·.declaration) =
          [cycleLeft.id, cycleRight.id] ∧
          plan.callEdges.map (fun edge =>
            (edge.caller.declaration, edge.callee.declaration)) =
            [(cycleLeft.id, cycleRight.id), (cycleRight.id, cycleLeft.id)]))
        "same-key mutual recursion did not close after two specializations"
  | outcome => throw (IO.userError
      s!"mutual cycle: expected a complete plan, found {reprStr outcome}")
  let grow ← signatureNamed program "grow"
  let growRequest ← unaryRequest grow .word
  match ← runOrThrow "grow" program [growRequest] 2 with
  | .budgetExhausted plan next _ =>
      let admitted := plan.specializations.map (·.key)
      assertTrue (decide (plan.specializations.length = 2 ∧
          plan.callEdges.length = 2 ∧ next.declaration = grow.id ∧
          next.arguments.length = 1) && !admitted.contains next)
        "type-growing recursion did not stop at the distinct-key budget"
  | outcome => throw (IO.userError
      s!"grow: expected exhaustion, found {reprStr outcome}")

private def testAssumptionPreservation (program : CheckedProgram) : IO Unit := do
  let keep ← signatureNamed program "keep"
  let constrained ← signatureNamed program "constrained"
  match ← runOrThrow "constrained" program
      [monomorphicRequest constrained] 2 with
  | .complete plan =>
      let specializedKeep := plan.specializations.find? fun specialized =>
        specialized.declaration == keep.id
      let specializedCaller := plan.specializations.find? fun specialized =>
        specialized.declaration == constrained.id
      match specializedKeep, specializedCaller with
      | some callee, some caller =>
          let hasImplementationEvidence :=
            caller.function.solvedRequirements.any fun requirement =>
              match requirement.evidence with
              | .implementation _ => true
              | .assumption _ => false
          assertTrue (decide (callee.key.arguments = [.word] ∧
              callee.assumptions.length = 1) && hasImplementationEvidence)
            "where predicate or solved caller evidence was consumed during discovery"
      | _, _ => throw (IO.userError
          "constrained: caller or keep<Word> specialization was not discovered")
  | outcome => throw (IO.userError
      s!"constrained: expected a complete plan, found {reprStr outcome}")

private def testContextualLocalProofCalls
    (program : CheckedProgram) : IO Unit := do
  let eq ← traitNamed program "Eq"
  let keepAs ← signatureNamed program "keepAs"
  let localProof ← signatureNamed program "localProof"
  let function ← functionFor program localProof
  let (call, instantiation) ← match
      function.typedBody.nodes.findSome? fun
        | .expression node@{
            form := .call _ _ (.declaration instantiation), .. } =>
            if instantiation.declaration == keepAs.id then
              some (node, instantiation)
            else
              none
        | _ => none with
    | some selected => pure selected
    | none => throw (IO.userError
        "localProof lost its declaration call to keepAs")
  let requirement ← match call.requirements with
    | [requirement] => pure requirement
    | requirements => throw (IO.userError
        s!"localProof keepAs call retained {requirements.length} requirements")
  let predicate : ProgramPredicate := {
    trait := eq.id
    subject := .word
    arguments := []
  }
  assertTrue (decide (instantiation.predicates = [predicate]))
    "localProof keepAs metadata lost its ground Eq<Word> predicate"

  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := localProof.id
    arguments := []
  }
  let wordKey : SourceSpecialization.SpecializationKey := {
    declaration := keepAs.id
    arguments := [.word, .word]
  }
  let boolKey : SourceSpecialization.SpecializationKey := {
    declaration := keepAs.id
    arguments := [.word, .bool]
  }
  let expectedEdges : List SourceSpecializationWorklist.CallEdge := [
    { caller := entryKey, occurrence := call.id, callee := wordKey },
    { caller := entryKey, occurrence := call.id, callee := boolKey }
  ]
  match ← runOrThrow "contextual local proof calls" program
      [monomorphicRequest localProof] 3 with
  | .complete plan =>
      let caller ← match plan.specializations.filter fun specialized =>
          decide (specialized.key = entryKey) with
        | [specialized] => pure specialized
        | specializations => throw (IO.userError
            s!"localProof retained {specializations.length} entry specializations")
      let callees := plan.specializations.filter fun specialized =>
        specialized.declaration == keepAs.id
      let solved ← match caller.function.solvedRequirements.filter fun solved =>
          solved.id == requirement with
        | [solved] => pure solved
        | solved => throw (IO.userError
            s!"localProof retained {solved.length} solutions for its Eq requirement")
      let implementationEvidence := match solved.evidence with
        | .implementation _ => true
        | .assumption _ => false
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) = [entryKey, wordKey, boolKey] ∧
          plan.callEdges = expectedEdges ∧
          plan.callEdges.eraseDups.length = 2 ∧
          plan.referenceEdges = [] ∧
          callees.length = 2 ∧
          (callees.all fun callee => callee.assumptions = [predicate]) ∧
          solved.predicate = predicate) && implementationEvidence)
        "local proof calls lost their assumptions, evidence, keys, or edges"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"contextual local proof plan failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"contextual local proof calls expected complete, found {reprStr outcome}")

private def testQualifiedLocalSchemeCalls
    (program : CheckedProgram) : IO Unit := do
  let keep ← signatureNamed program "keep"
  let qualifiedLocal ← signatureNamed program "qualifiedLocal"
  let function ← functionFor program qualifiedLocal
  let binder ← match function.typedBody.nodes.findSome? fun
      | .statement { form := .letDecl binder (some _), .. } =>
          if binder.name == "f" then some binder else none
      | _ => none with
    | some binder => pure binder
    | none => throw (IO.userError "qualifiedLocal lost its f binder")
  let template ← match binder.schemeRequirements with
    | [requirement] => pure requirement
    | requirements => throw (IO.userError
        s!"qualifiedLocal retained {requirements.length} scheme requirements")
  let (call, instantiation) ← match
      function.typedBody.nodes.findSome? fun
        | .expression node@{
            form := .call _ _ (.declaration instantiation), .. } =>
            if instantiation.declaration == keep.id then
              some (node, instantiation)
            else
              none
        | _ => none with
    | some selected => pure selected
    | none => throw (IO.userError "qualifiedLocal lost its keep call")
  assertTrue (decide (instantiation.predicates = [template.predicate] ∧
      call.requirements.contains template.templateRequirement))
    "qualifiedLocal detached its template predicate from the keep call"
  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := qualifiedLocal.id
    arguments := []
  }
  let wordKey : SourceSpecialization.SpecializationKey := {
    declaration := keep.id
    arguments := [.word]
  }
  let boolKey : SourceSpecialization.SpecializationKey := {
    declaration := keep.id
    arguments := [.bool]
  }
  let expectedEdges : List SourceSpecializationWorklist.CallEdge := [
    { caller := entryKey, occurrence := call.id, callee := wordKey },
    { caller := entryKey, occurrence := call.id, callee := boolKey }
  ]
  match ← runOrThrow "qualified local scheme calls" program
      [monomorphicRequest qualifiedLocal] 3 with
  | .complete plan =>
      let caller ← match plan.specializations.filter fun specialized =>
          decide (specialized.key = entryKey) with
        | [specialized] => pure specialized
        | specialized => throw (IO.userError
            s!"qualifiedLocal retained {specialized.length} entry specializations")
      let templateSolved ← match caller.function.solvedRequirements.filter
          fun solved => solved.id == template.templateRequirement with
        | [solved] => pure solved
        | solved => throw (IO.userError
            s!"qualifiedLocal retained {solved.length} template solutions")
      let templateAssumption := match templateSolved.evidence with
        | .assumption predicate => predicate == template.predicate
        | .implementation _ => false
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) = [entryKey, wordKey, boolKey] ∧
          plan.callEdges = expectedEdges ∧
          plan.referenceEdges = [] ∧
          templateSolved.predicate = template.predicate) && templateAssumption)
        "qualified local scheme calls lost template evidence, keys, or edges"
      match SourceCoreDirectLinking.validatePlan program plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"qualified local plan failed canonical replay: {reprStr error}")
  | outcome => throw (IO.userError
      s!"qualified local scheme calls expected complete, found {reprStr outcome}")

  let wrongPredicate := {
    template.predicate with arguments := [.word]
  }
  let malformedBinderFunction : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := setLocalBinderRequirements function.typedBody.nodes binder.id [{
        template with predicate := wrongPredicate
      }]
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction program malformedBinderFunction)
      [monomorphicRequest qualifiedLocal] 3 with
  | .error (.specialization declaration
      (.localSchemeRequirementPredicateMismatch actualBinder actualRequirement
        _ _)) =>
      assertTrue (decide (declaration = qualifiedLocal.id ∧
          actualBinder = binder.id ∧
          actualRequirement = template.templateRequirement))
        "qualified binder predicate tamper lost its owner or template identity"
  | result => throw (IO.userError
      s!"tampered qualified binder predicate was accepted: {reprStr result}")

  let detachedCallFunction : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := setExpressionRequirements function.typedBody.nodes call.id []
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction program detachedCallFunction)
      [monomorphicRequest qualifiedLocal] 3 with
  | .error (.localSchemeRequirementIdMultiplicity _ actualRequirement 0) =>
      assertTrue (actualRequirement == template.templateRequirement)
        "detached qualified requirement lost its template identity"
  | result => throw (IO.userError
      s!"detached qualified call requirement was accepted: {reprStr result}")

private def checkQualifiedLocalSchemeCallWithCoercion
    (program : CheckedProgram) (name label : String)
    (coercionBeforeSignature : Bool) : IO Unit := do
  let guarded ← signatureNamed program "guarded"
  let qualified ← signatureNamed program name
  let function ← functionFor program qualified
  let binder ← match function.typedBody.nodes.findSome? fun
      | .statement { form := .letDecl binder (some _), .. } =>
          if binder.name == "f" then some binder else none
      | _ => none with
    | some binder => pure binder
    | none => throw (IO.userError
        s!"{name} lost its f binder")
  let template ← match binder.schemeRequirements with
    | [requirement] => pure requirement
    | requirements => throw (IO.userError
        s!"{name} retained {requirements.length} scheme requirements")
  let (call, instantiation) ← match
      function.typedBody.nodes.findSome? fun
        | .expression node@{
            form := .call _ _ (.declaration instantiation), .. } =>
            if instantiation.declaration == guarded.id then
              some (node, instantiation)
            else
              none
        | _ => none with
    | some selected => pure selected
    | none => throw (IO.userError
        s!"{name} lost its guarded call")
  let coercionRequirements := call.coercions.flatMap (fun step =>
    step.requirements)
  let expectedRequirements := if coercionBeforeSignature then
    coercionRequirements ++ [template.templateRequirement]
  else
    [template.templateRequirement] ++ coercionRequirements
  assertTrue (decide (instantiation.predicates = [template.predicate] ∧
      call.coercions ≠ [] ∧
      call.requirements = expectedRequirements))
    s!"{name} did not retain its signature/coercion ledger order"
  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := qualified.id
    arguments := []
  }
  let wordKey : SourceSpecialization.SpecializationKey := {
    declaration := guarded.id
    arguments := [.word]
  }
  let boolKey : SourceSpecialization.SpecializationKey := {
    declaration := guarded.id
    arguments := [.bool]
  }
  let expectedEdges : List SourceSpecializationWorklist.CallEdge := [{
    caller := entryKey
    occurrence := call.id
    callee := wordKey
  }, {
    caller := entryKey
    occurrence := call.id
    callee := boolKey
  }]
  match ← runOrThrow label program
      [monomorphicRequest qualified] 8 with
  | .complete plan =>
      let actualEdges := plan.callEdges.filter fun edge => edge.occurrence == call.id
      assertTrue (decide (actualEdges = expectedEdges) &&
          (plan.specializations.any fun specialized => specialized.key == wordKey) &&
          (plan.specializations.any fun specialized => specialized.key == boolKey))
        s!"{label} lost its concrete calls"
  | outcome => throw (IO.userError
      s!"{label} expected complete, found {reprStr outcome}")

private def testQualifiedLocalSchemeCallsWithCoercions
    (program : CheckedProgram) : IO Unit := do
  checkQualifiedLocalSchemeCallWithCoercion program "qualifiedLocalCoerced"
    "qualified local contextual coercion" false
  checkQualifiedLocalSchemeCallWithCoercion program
    "qualifiedLocalResultCoerced" "qualified local result coercion" true

private def testDetachedSpecializationClosure
    (program : CheckedProgram) : IO Unit := do
  let identity ← signatureNamed program "identity"
  let helper ← signatureNamed program "coercionClosureHelper"
  let caller ← signatureNamed program "qualifiedLocalCoerced"
  let callerFunction ← functionFor program caller
  let coercionOccurrence ← match callerFunction.typedBody.nodes.findSome? fun
      | .expression expression =>
          if expression.coercions.isEmpty then none else some expression.id
      | .statement _ => none with
    | some occurrence => pure occurrence
    | none => throw (IO.userError
        "qualifiedLocalCoerced lost its coercion occurrence")
  let base ← match ← runOrThrow "detached method base" program
      [monomorphicRequest caller] 8 with
    | .complete plan => pure plan
    | outcome => throw (IO.userError
        s!"detached method base expected complete, found {reprStr outcome}")
  let coerce ← traitNamed program "Coerce"
  let implementation ← match program.signatures.implementations.filter
      fun implementation =>
        implementation.head.trait == .declaration coerce.id with
    | [implementation] => pure implementation
    | implementations => throw (IO.userError
        s!"expected one Coerce implementation, found {implementations.length}")
  let evidence ← match (TypedTraitResolution.resolve
      program.signatures.resolutionRules 32 implementation.head).outcome with
    | .success evidence => pure evidence
    | outcome => throw (IO.userError
        s!"Coerce implementation evidence did not resolve: {reprStr outcome}")
  let method ← match ExecutableImplMethods.checkMethodWithArity
      program evidence 2 "coerce" with
    | .ok method => pure method
    | .error error => throw (IO.userError
        s!"detached Coerce method did not specialize: {reprStr error}")
  let helperCall ← match
      method.specialized.function.typedBody.nodes.findSome? fun
        | .expression expression@{
            form := .call _ _ (.declaration instantiation), .. } =>
            if instantiation.declaration == helper.id then
              some expression.id
            else
              none
        | _ => none with
    | some occurrence => pure occurrence
    | none => throw (IO.userError
        "detached Coerce method lost its top-level helper call")
  let helperFunction ← functionFor program helper
  let identityReference ← match helperFunction.typedBody.nodes.findSome? fun
      | .expression expression@{
          form := .reference _ (.declaration instantiation), .. } =>
          if instantiation.declaration == identity.id then
            some expression.id
          else
            none
      | _ => none with
    | some occurrence => pure occurrence
    | none => throw (IO.userError
        "coercion closure helper lost its identity reference")
  let callerKey : SourceSpecialization.SpecializationKey := {
    declaration := caller.id
    arguments := []
  }
  let helperKey : SourceSpecialization.SpecializationKey := {
    declaration := helper.id
    arguments := []
  }
  let identityKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.word]
  }
  let outerEdge : SourceSpecializationWorklist.CallEdge := {
    caller := callerKey
    occurrence := coercionOccurrence
    callee := method.specialized.key
  }
  let helperEdge : SourceSpecializationWorklist.CallEdge := {
    caller := method.specialized.key
    occurrence := helperCall
    callee := helperKey
  }
  let identityEdge : SourceSpecializationWorklist.ReferenceEdge := {
    caller := helperKey
    occurrence := identityReference
    callee := identityKey
  }
  assertTrue (!(base.specializations.any fun specialized =>
      specialized.key == method.specialized.key) &&
      !(base.specializations.any fun specialized =>
        specialized.key == helperKey) &&
      !(base.specializations.any fun specialized =>
        specialized.key == identityKey))
    "detached method fixture was already reachable from the public seed"
  match SourceSpecializationWorklist.extendCompletePlan program base
      method.specialized outerEdge 0 with
  | .ok (.budgetExhausted partialPlan next pending) =>
      assertTrue ((partialPlan.specializations ==
          base.specializations ++ [method.specialized]) && decide (
          partialPlan.seedKeys = base.seedKeys ∧
          partialPlan.callEdges = base.callEdges ++ [outerEdge, helperEdge] ∧
          partialPlan.referenceEdges = base.referenceEdges ∧
          next = helperKey ∧
          pending.length = 1))
        "the pre-resolved root consumed helper budget or lost its outer edge"
  | result => throw (IO.userError
      s!"zero-budget detached method extension had the wrong outcome: {reprStr result}")
  let extended ← match SourceSpecializationWorklist.extendCompletePlan
      program base method.specialized outerEdge 2 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError
        s!"detached method closure did not complete: {reprStr result}")
  assertTrue (decide (
      extended.seedKeys = base.seedKeys ∧
      extended.specializations.map (fun specialized => specialized.key) =
        base.specializations.map (fun specialized => specialized.key) ++
          [method.specialized.key, helperKey, identityKey] ∧
      extended.callEdges = base.callEdges ++ [outerEdge, helperEdge] ∧
      extended.referenceEdges = base.referenceEdges ++ [identityEdge]))
    "detached method call/reference closure or original plan data changed"
  let duplicatedEdges : SourceSpecializationWorklist.Plan := {
    extended with
    callEdges := extended.callEdges ++ [outerEdge, helperEdge]
    referenceEdges := extended.referenceEdges ++ [identityEdge]
  }
  match SourceSpecializationWorklist.extendCompletePlan program duplicatedEdges
      method.specialized outerEdge 0 with
  | .ok (.complete repeated) =>
      assertTrue (repeated == extended)
        "re-extending an existing root did not normalize exact duplicate edges"
  | result => throw (IO.userError
      s!"idempotent detached method extension failed: {reprStr result}")
  let duplicateSpecialization : SourceSpecializationWorklist.Plan := {
    extended with
    specializations := extended.specializations ++ [method.specialized]
  }
  match SourceSpecializationWorklist.extendCompletePlan program
      duplicateSpecialization method.specialized outerEdge 0 with
  | .error (.duplicatePlanSpecializations key 2) =>
      assertTrue (key == method.specialized.key)
        "duplicate-plan rejection reported the wrong specialization key"
  | result => throw (IO.userError
      s!"duplicate plan specialization was accepted: {reprStr result}")
  let mismatchedRoot : SourceSpecialization.SpecializedFunction := {
    method.specialized with declaration := helper.id
  }
  match SourceSpecializationWorklist.extendCompletePlan program extended
      mismatchedRoot outerEdge 0 with
  | .error (.existingSpecializationMismatch key) =>
      assertTrue (key == method.specialized.key)
        "existing-root mismatch reported the wrong specialization key"
  | result => throw (IO.userError
      s!"mismatched existing root was accepted: {reprStr result}")
  let mismatchedEdge : SourceSpecializationWorklist.CallEdge := {
    outerEdge with callee := helperKey
  }
  match SourceSpecializationWorklist.extendCompletePlan program base
      method.specialized mismatchedEdge 2 with
  | .error (.outerEdgeCalleeMismatch expected actual) =>
      assertTrue (decide (expected = method.specialized.key ∧
          actual = helperKey))
        "outer-edge mismatch lost its expected or actual callee key"
  | result => throw (IO.userError
      s!"mismatched detached-root edge was accepted: {reprStr result}")

private def testQualifiedLocalSchemeReferences
    (program : CheckedProgram) : IO Unit := do
  let keep ← signatureNamed program "keep"
  let qualifiedLocal ← signatureNamed program "qualifiedLocal"
  let function ← functionFor program qualifiedLocal
  let binder ← match function.typedBody.nodes.findSome? fun
      | .statement { form := .letDecl binder (some _), .. } =>
          if binder.name == "f" then some binder else none
      | _ => none with
    | some binder => pure binder
    | none => throw (IO.userError "qualifiedLocal lost its f binder")
  let template ← match binder.schemeRequirements with
    | [requirement] => pure requirement
    | requirements => throw (IO.userError
        s!"qualifiedLocal retained {requirements.length} scheme requirements")
  let (call, callee, arguments, instantiation) ← match
      function.typedBody.nodes.findSome? fun
        | .expression node@{
            form := .call callee arguments (.declaration instantiation), .. } =>
            if instantiation.declaration == keep.id then
              some (node, callee, arguments, instantiation)
            else
              none
        | _ => none with
    | some selected => pure selected
    | none => throw (IO.userError "qualifiedLocal lost its keep call")
  let reference ← match function.typedBody.lookupExpression? callee with
    | some node@{ form := .reference _ (.declaration reference), .. } =>
        if reference == instantiation then pure node
        else throw (IO.userError
          "qualifiedLocal call and reference instantiations diverged")
    | _ => throw (IO.userError
        "qualifiedLocal keep call lost its declaration-reference child")
  let argumentTypes ← arguments.mapM fun argument =>
    match function.typedBody.lookupExpression? argument with
    | some node => pure node.type
    | none => throw (IO.userError
        "qualifiedLocal keep call lost an argument node")
  let parameterType ← match reference.type with
    | .function parameter _ => pure parameter
    | type => throw (IO.userError
        s!"qualifiedLocal keep reference is not a function: {reprStr type}")
  let metadata : IndirectCallResolution := {
    argumentCount := arguments.length
    argumentTypeBeforeCoercion := Ty.productMany argumentTypes
    argumentTypeAfterCoercion := parameterType
    argumentCoercions := []
  }
  let indirectNodes := setCallResolution function.typedBody.nodes call.id
    (.indirect metadata)
  let indirectNodes := setExpressionRequirements indirectNodes call.id []
  let indirectNodes := setExpressionRequirements indirectNodes callee
    [template.templateRequirement]
  let indirectFunction : CheckedFunction := {
    function with
    typedBody := { function.typedBody with nodes := indirectNodes }
  }
  let indirectProgram := replaceFunction program indirectFunction
  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := qualifiedLocal.id
    arguments := []
  }
  let wordKey : SourceSpecialization.SpecializationKey := {
    declaration := keep.id
    arguments := [.word]
  }
  let boolKey : SourceSpecialization.SpecializationKey := {
    declaration := keep.id
    arguments := [.bool]
  }
  let expectedEdges : List SourceSpecializationWorklist.ReferenceEdge := [{
    caller := entryKey
    occurrence := callee
    callee := wordKey
  }, {
    caller := entryKey
    occurrence := callee
    callee := boolKey
  }]
  match ← runOrThrow "qualified local scheme references" indirectProgram
      [monomorphicRequest qualifiedLocal] 3 with
  | .complete plan =>
      assertTrue (decide (
          plan.seedKeys = [entryKey] ∧
          plan.specializations.map (·.key) = [entryKey, wordKey, boolKey] ∧
          plan.callEdges = [] ∧
          plan.referenceEdges = expectedEdges ∧
          plan.referenceEdges.eraseDups.length = 2))
        "qualified local scheme reference lost its concrete keys or edges"
      match SourceCoreDirectLinking.validatePlan indirectProgram plan with
      | .ok () => pure ()
      | .error error => throw (IO.userError
          s!"qualified local reference plan failed replay validation: {reprStr error}")
  | outcome => throw (IO.userError
      s!"qualified local scheme references expected complete, found {reprStr outcome}")

  let detachedFunction : CheckedFunction := {
    indirectFunction with
    typedBody := {
      indirectFunction.typedBody with
      nodes := setExpressionRequirements indirectFunction.typedBody.nodes
        callee []
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction indirectProgram detachedFunction)
      [monomorphicRequest qualifiedLocal] 3 with
  | .error (.localSchemeRequirementIdMultiplicity _ actualRequirement 0) =>
      assertTrue (actualRequirement == template.templateRequirement)
        "detached qualified reference lost its template identity"
  | result => throw (IO.userError
      s!"detached qualified reference requirement was accepted: {reprStr result}")

private def testFunctionValueReference (program : CheckedProgram) : IO Unit := do
  let identity ← signatureNamed program "identity"
  let asValue ← signatureNamed program "asValue"
  let function ← functionFor program asValue
  let reference ← match function.typedBody.nodes.findSome? fun node =>
      match node with
      | .expression expression@{
          form := .reference _ (.declaration instantiation), .. } =>
          if instantiation.declaration == identity.id then some expression else none
      | _ => none with
    | some reference => pure reference
    | none => throw (IO.userError
        "asValue: standalone declaration reference metadata was absent")
  match ← runOrThrow "asValue" program [monomorphicRequest asValue] 2 with
  | .complete plan =>
      match plan.referenceEdges with
      | [edge] =>
          assertTrue (decide (plan.specializations.map (·.declaration) =
              [asValue.id, identity.id] ∧ plan.callEdges = [] ∧
              edge.caller.declaration = asValue.id ∧
              edge.occurrence = reference.id ∧
              edge.callee.declaration = identity.id ∧
              edge.callee.arguments = [.word]))
            "standalone function reference did not retain its canonical edge"
      | edges => throw (IO.userError
          s!"asValue: expected one reference edge, found {edges.length}")
      let malformed : SourceSpecializationWorklist.Plan := {
        plan with referenceEdges := []
      }
      match SourceCoreDirectLinking.validatePlan program malformed with
      | .error (.referenceEdgesMismatch expected []) =>
          assertTrue (decide (expected = plan.referenceEdges))
            "reference-ledger rejection lost the canonical edge"
      | result => throw (IO.userError
          s!"direct plan validation accepted a missing reference edge: {reprStr result}")
  | outcome => throw (IO.userError
      s!"asValue: expected a complete plan, found {reprStr outcome}")
  match ← runOrThrow "asValue budget" program
      [monomorphicRequest asValue] 1 with
  | .budgetExhausted plan next pending =>
      assertTrue (decide (plan.specializations.length = 1 ∧
          plan.callEdges = [] ∧ plan.referenceEdges.length = 1 ∧
          next.declaration = identity.id ∧ next.arguments = [.word] ∧
          pending.length = 1))
        "standalone function reference was absent from the FIFO frontier"
  | outcome => throw (IO.userError
      s!"asValue budget: expected exhaustion, found {reprStr outcome}")
  let malformedFunction : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := setExpressionType function.typedBody.nodes reference.id .bool
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction program malformedFunction)
      [monomorphicRequest asValue] 2 with
  | .error (.calleeNodeTypeMismatch actual .bool _) =>
      assertTrue (actual == reference.id)
        "standalone reference mismatch lost its occurrence identity"
  | result => throw (IO.userError
      s!"malformed standalone reference metadata was accepted: {reprStr result}")

private def testIndirectCallBoundary (program : CheckedProgram) : IO Unit := do
  let apply ← signatureNamed program "apply"
  let function ← functionFor program apply
  let (call, metadata) ← match firstIndirectCall? function.typedBody.nodes with
    | some call => pure call
    | none => throw (IO.userError "apply: indirect call metadata was absent")
  assertTrue (decide (call.type = .word ∧ call.coercions = [] ∧
      metadata.argumentTypeBeforeCoercion = .word ∧
      metadata.argumentTypeAfterCoercion = .word ∧
      metadata.argumentCoercions = [] ∧
      metadata.hasValidArgumentCoercionPath))
    "apply: exact indirect arguments produced malformed call metadata"
  match SourceSpecializationWorklist.run program
      [monomorphicRequest apply] 1 with
  | .ok (.complete plan) =>
      assertTrue (decide (plan.specializations.length = 1 ∧
          plan.callEdges = [] ∧ plan.referenceEdges = []))
        "well-typed indirect call added a static target edge"
  | result => throw (IO.userError
      s!"well-typed indirect call was not accepted: {reprStr result}")
  let malformedMetadata := {
    metadata with argumentTypeAfterCoercion := Ty.bool
  }
  let malformedFunction : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := setIndirectMetadata function.typedBody.nodes call.id
        malformedMetadata
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction program malformedFunction)
      [monomorphicRequest apply] 1 with
  | .error (.invalidIndirectArgumentCoercionPath actual metadata) =>
      assertTrue (actual == call.id && !metadata.hasValidArgumentCoercionPath)
        "invalid indirect metadata lost its call occurrence or path"
  | result => throw (IO.userError
      s!"malformed indirect coercion metadata was not rejected: {reprStr result}")
  let wrongBundleMetadata := {
    metadata with
    argumentTypeBeforeCoercion := Ty.bool
    argumentTypeAfterCoercion := Ty.bool
  }
  let wrongBundleFunction : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := setIndirectMetadata function.typedBody.nodes call.id
        wrongBundleMetadata
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction program wrongBundleFunction)
      [monomorphicRequest apply] 1 with
  | .error (.indirectArgumentBundleMismatch actual .word .bool) =>
      assertTrue (actual == call.id)
        "indirect bundle mismatch lost its call occurrence"
  | result => throw (IO.userError
      s!"indirect metadata detached from argument children was accepted: {reprStr result}")
  let wrongResultFunction : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := setExpressionType function.typedBody.nodes call.id .bool
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction program wrongResultFunction)
      [monomorphicRequest apply] 1 with
  | .error (.indirectResultTypeMismatch actual .word .bool) =>
      assertTrue (actual == call.id)
        "indirect result mismatch lost its call occurrence"
  | result => throw (IO.userError
      s!"indirect result metadata detached from the callee was accepted: {reprStr result}")

private def testIndirectArgumentCountCase (program : CheckedProgram)
    (name : String) (expected forged : Nat) : IO Unit := do
  let signature ← signatureNamed program name
  let function ← functionFor program signature
  let (call, metadata) ← match firstIndirectCall? function.typedBody.nodes with
    | some call => pure call
    | none => throw (IO.userError s!"{name}: indirect call metadata was absent")
  assertTrue (decide (metadata.argumentCount = expected ∧
      metadata.argumentTypeBeforeCoercion = .product .word .bool ∧
      metadata.argumentTypeAfterCoercion = .product .word .bool))
    s!"{name}: product bundle or source argument count was not retained"
  let forgedMetadata := { metadata with argumentCount := forged }
  let malformedFunction : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := setIndirectMetadata function.typedBody.nodes call.id
        forgedMetadata
    }
  }
  let malformedProgram := replaceFunction program malformedFunction
  match SourceSpecializationWorklist.run malformedProgram
      [monomorphicRequest signature] 1 with
  | .error (.indirectArgumentCountMismatch actual retained children) =>
      assertTrue (actual == call.id && retained == forged && children == expected)
        s!"{name}: worklist arity rejection lost its occurrence or counts"
  | result => throw (IO.userError
      s!"{name}: worklist accepted product-bundle arity tampering: {reprStr result}")
private def testIndirectArgumentCounts (program : CheckedProgram) : IO Unit := do
  testIndirectArgumentCountCase program "applyProduct" 1 2
  testIndirectArgumentCountCase program "applySplit" 2 1

private def testMalformedTypedMetadata (program : CheckedProgram) : IO Unit := do
  let select ← signatureNamed program "select"
  let function ← functionFor program select
  let (call, callee) ← match firstDirectCall? function.typedBody.nodes with
    | some edge => pure edge
    | none => throw (IO.userError "select: direct call metadata was absent")
  let wrongTypeFunction : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := setExpressionType function.typedBody.nodes callee .bool
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction program wrongTypeFunction)
      [monomorphicRequest select] 2 with
  | .error (.calleeNodeTypeMismatch actualCall .bool _) =>
      assertTrue (actualCall == call)
        "callee-node type mismatch lost the owning call occurrence"
  | result => throw (IO.userError
      s!"malformed callee-node type was not isolated: {reprStr result}")
  let invalidPath : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := setExpressionCoercions function.typedBody.nodes call [{
        requirement := ⟨99⟩
        source := .word
        target := .bool
      }]
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction program invalidPath)
      [monomorphicRequest select] 2 with
  | .error (.invalidExpressionCoercionPath actual .word .word [_]) =>
      assertTrue (actual == call)
        "invalid output coercion path lost its expression occurrence"
  | result => throw (IO.userError
      s!"an output coercion not ending at node.type was accepted: {reprStr result}")
  let wrongParameterComptime : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := setDirectInstantiationMarkers function.typedBody.nodes
        call callee [true, false] false
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction program wrongParameterComptime)
      [monomorphicRequest select] 2 with
  | .error (.specializedCalleeParameterComptimeMismatch
      actual [true, false] [false, false]) =>
      assertTrue (actual == call)
        "callee parameter-marker mismatch lost the owning call occurrence"
  | result => throw (IO.userError
      s!"tampered callee parameter markers were not rejected: {reprStr result}")
  let wrongReturnComptime : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := setDirectInstantiationMarkers function.typedBody.nodes
        call callee [false, false] true
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction program wrongReturnComptime)
      [monomorphicRequest select] 2 with
  | .error (.specializedCalleeReturnComptimeMismatch actual true false) =>
      assertTrue (actual == call)
        "callee result-marker mismatch lost the owning call occurrence"
  | result => throw (IO.userError
      s!"tampered callee result marker was not rejected: {reprStr result}")
  let missingNodeFunction : CheckedFunction := {
    function with
    typedBody := {
      function.typedBody with
      nodes := eraseExpression function.typedBody.nodes callee
    }
  }
  match SourceSpecializationWorklist.run
      (replaceFunction program missingNodeFunction)
      [monomorphicRequest select] 2 with
  | .error (.specialization declaration
      (.stageAnalysis (.missingNode actualCallee))) =>
      assertTrue (declaration == select.id && actualCallee == callee.occurrence)
        "stage-analysis missing-node error lost its declaration or callee identity"
  | result => throw (IO.userError
      s!"missing callee node was not rejected: {reprStr result}")
  let missingDeclarationProgram : CheckedProgram := {
    program with
    environment := {
      program.environment with
      declarations := program.environment.declarations.filter fun declaration =>
        declaration.id != select.id
    }
  }
  match SourceSpecializationWorklist.run missingDeclarationProgram
      [monomorphicRequest select] 2 with
  | .error (.missingDeclaration declaration) =>
      assertTrue (declaration == select.id)
        "missing-declaration error reported the wrong catalog identity"
  | result => throw (IO.userError
      s!"missing environment declaration was not rejected: {reprStr result}")

/-- Exercise canonical FIFO discovery, per-occurrence direct and function-value
edges, recursion deduplication, finite type-growing recursion, retained
assumptions/evidence, malformed catalog/metadata rejection, and indirect-call
validation from one checked raw workspace. -/
def testSourceSpecializationWorklist : IO Unit := do
  let program ← checkedProgram
  testBreadthFirstDiscovery program
  testContextualLocalPolymorphicCalls program
  testDepthTwoContextualLocalPolymorphicCalls program
  testGroundInnerUnderPolymorphicOuter program
  testSiblingContextualLocalPolymorphicCalls program
  testDepthThreeContextualLocalPolymorphicCalls program
  testScopeAwareRecursiveContextualLocalPolymorphicCalls program
  testMixedScopeDepthThreeContextualLocalPolymorphicCalls program
  testReusedBinderMixedScopeContextualLocalPolymorphicCalls program
  testMonomorphicLambdaWrapperContextualLocal program
  testUnusedNestedContextualLocal program
  testDerivedCanonicalization program
  testTypedNodeOrder program
  testRecursiveKeys program
  testAssumptionPreservation program
  testContextualLocalProofCalls program
  testQualifiedLocalSchemeCalls program
  testQualifiedLocalSchemeCallsWithCoercions program
  testDetachedSpecializationClosure program
  testQualifiedLocalSchemeReferences program
  testFunctionValueReference program
  testIndirectCallBoundary program
  testIndirectArgumentCounts program
  testMalformedTypedMetadata program

end Tests.SourceSpecializationWorklist
end

section
-- leanmerge: from Solcore.Test.SourceStageClassification
/-!
Executable regressions for scope-aware source-stage classification.

The fixture deliberately observes binders through their stable local IDs and
expressions through their occurrence IDs.  It therefore checks the semantic
sidecar without relying on the incidental order of the typed-source node table.
-/

set_option autoImplicit false

namespace Tests.SourceStageClassification

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.Frontend.SourceStageAnalysis

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def fixtureSource : String := String.intercalate "\n" [
  "function plain(value: Word) returns (Word) { return value; }",
  "function staged(comptime required: Bool, flexible: Word) returns (comptime<Word>) { return flexible; }",
  "function integerResult(value: Word) returns (integer) { return 1; }",
  "function classify(comptime fixed: Word, runtime: Word, flag: Bool) returns (Word) {",
  "  let ct = 1;",
  "  let ctAlias = fixed;",
  "  let runtimeAlias = runtime;",
  "  let runtimeAlias2 = runtimeAlias;",
  "  let deferred = plain(1);",
  "  let deferredAlias = deferred;",
  "  let stagedCt = staged(true, 2);",
  "  let stagedDeferred = staged(true, runtime);",
  "  let implicitCt = integerResult(ct);",
  "  let implicitDeferred = integerResult(runtime);",
  "  let groupRuntime: Word = (runtime);",
  "  let unaryCt: Word = ~ct;",
  "  let binaryCt: Word = ct + 1;",
  "  let binaryRuntime: Word = runtime + 1;",
  "  let tupleCt = (ct, stagedCt);",
  "  let tupleDeferred = (ct, deferred);",
  "  let tupleRuntime = (deferred, runtimeAlias);",
  "  let condCt = true ? ct : stagedCt;",
  "  let condDeferred = true ? ct : deferred;",
  "  let condRuntime = true ? ct : runtimeAlias;",
  "  let runtimeGuard = flag ? ct : stagedCt;",
  "  return runtimeAlias2;",
  "}",
  "function lambdaStages() returns (Word) {",
  "  let stagedLambda = lam(comptime value: Word) -> Word { return value; };",
  "  let runtimeLambda = lam(value: Word) -> Word { return value; };",
  "  return 0;",
  "}",
  "function matchStages(tag: Word, zero: Word, other: Word) returns (Word) {",
  "  match (tag) {",
  "    case 0 { return zero; }",
  "    case _ { return other; }",
  "  }",
  "}"
]

private def checkedProgram : IO CheckedProgram := do
  match checkProgram (workspace fixtureSource) with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"source-stage fixture failed checking: {reprStr errors}")

private def functionNamed (program : CheckedProgram) (name : String) :
    IO CheckedFunction := do
  let signatures := program.signatures.functions.filter fun signature =>
    signature.name == name
  let signature ← match signatures with
    | [signature] => pure signature
    | _ => throw (IO.userError
        s!"expected one signature named `{name}`, found {signatures.length}")
  let functions := program.functions.filter fun function =>
    function.declaration == signature.id
  match functions with
  | [function] => pure function
  | _ => throw (IO.userError
      s!"expected one checked body named `{name}`, found {functions.length}")

private def analyzeOrThrow (label : String) (function : CheckedFunction) :
    IO Analysis := do
  match analyzeFunction function with
  | .ok analysis => pure analysis
  | .error error => throw (IO.userError
      s!"{label}: source-stage analysis failed: {reprStr error}")

private def expectAnalysisError (label : String)
    (actual : Except SourceStageAnalysis.Error Analysis)
    (expected : SourceStageAnalysis.Error) : IO Unit :=
  match actual with
  | .ok analysis => throw (IO.userError
      s!"{label}: malformed typed source was accepted: {reprStr analysis}")
  | .error error =>
      assertTrue (decide (error = expected))
        s!"{label}: expected {reprStr expected}, found {reprStr error}"

private def inputNamed (function : CheckedFunction) (name : String) :
    IO TypedBinder :=
  match function.typedBody.inputs.filter fun binder => binder.name == name with
  | [binder] => pure binder
  | binders => throw (IO.userError
      s!"expected one input named `{name}`, found {binders.length}")

private def initializedLetNamed (function : CheckedFunction) (name : String) :
    IO (TypedBinder × ExpressionId) := do
  let bindings := function.typedBody.nodes.filterMap fun
    | .statement statement =>
        match statement.form with
        | .letDecl binder (some initializer) =>
            if binder.name == name then some (binder, initializer) else none
        | _ => none
    | .expression _ => none
  match bindings with
  | [binding] => pure binding
  | _ => throw (IO.userError
      s!"expected one initialized let named `{name}`, found {bindings.length}")

private def expectBinderStage (label : String) (analysis : Analysis)
    (binder : TypedBinder) (expected : Stage) : IO Unit :=
  assertTrue (analysis.binderStage? binder.id == some expected)
    s!"{label}: expected binder stage {reprStr expected}, found {reprStr (analysis.binderStage? binder.id)}"

private def expectExpressionStage (label : String) (analysis : Analysis)
    (expression : ExpressionId) (expected : Stage) : IO Unit :=
  assertTrue (analysis.expressionStage? expression == some expected)
    s!"{label}: expected expression stage {reprStr expected}, found {reprStr (analysis.expressionStage? expression)}"

private def expectInputStage (function : CheckedFunction) (analysis : Analysis)
    (name : String) (expected : Stage) : IO Unit := do
  let binder ← inputNamed function name
  expectBinderStage s!"input `{name}`" analysis binder expected

private def expectLetStage (function : CheckedFunction) (analysis : Analysis)
    (name : String) (expected : Stage) : IO Unit := do
  let (binder, initializer) ← initializedLetNamed function name
  expectBinderStage s!"let `{name}`" analysis binder expected
  expectExpressionStage s!"initializer of `{name}`" analysis initializer expected

private def expectCallCalleeDeferred (function : CheckedFunction)
    (analysis : Analysis) (name : String) : IO Unit := do
  let (_, initializer) ← initializedLetNamed function name
  let node ← match function.typedBody.lookupExpression? initializer with
    | some node => pure node
    | none => throw (IO.userError
        s!"initializer of `{name}` is absent from the typed source")
  let callee ← match node.form with
    | .call callee _ _ => pure callee
    | form => throw (IO.userError
        s!"initializer of `{name}` is not a call: {reprStr form}")
  expectExpressionStage s!"callee reference of `{name}`" analysis callee
    .deferred

private structure LambdaObservation where
  expression : ExpressionId
  parameter : TypedBinder
  returned : ExpressionId

private def lambdaLetNamed (function : CheckedFunction) (name : String) :
    IO LambdaObservation := do
  let (_, initializer) ← initializedLetNamed function name
  let node ← match function.typedBody.lookupExpression? initializer with
    | some node => pure node
    | none => throw (IO.userError
        s!"initializer of `{name}` is absent from the typed source")
  let (parameter, body) ← match node.form with
    | .lambda [parameter] _ body => pure (parameter, body)
    | form => throw (IO.userError
        s!"initializer of `{name}` is not a unary lambda: {reprStr form}")
  let returned ← match body with
    | [statement] =>
        match function.typedBody.lookupStatement? statement with
        | some { form := .returnStmt (some returned), .. } => pure returned
        | some statement => throw (IO.userError
            s!"body of `{name}` is not a value return: {reprStr statement.form}")
        | none => throw (IO.userError
            s!"body statement of `{name}` is absent from the typed source")
    | statements => throw (IO.userError
        s!"expected one body statement for `{name}`, found {statements.length}")
  pure { expression := initializer, parameter, returned }

private def testJoin : IO Unit := do
  assertTrue (Stage.join [] == .comptime)
    "the empty stage join was not comptime"
  assertTrue (Stage.join [.comptime, .comptime] == .comptime)
    "an all-comptime stage join was not comptime"
  assertTrue (Stage.join [.comptime, .deferred] == .deferred)
    "a mixed comptime/deferred stage join was not deferred"
  assertTrue (Stage.join [.deferred, .runtime] == .runtime)
    "a stage join containing runtime was not runtime"

private def testInputClassification (program : CheckedProgram) : IO Unit := do
  let plain ← functionNamed program "plain"
  let plainAnalysis ← analyzeOrThrow "plain" plain
  expectInputStage plain plainAnalysis "value" .runtime

  let staged ← functionNamed program "staged"
  let stagedAnalysis ← analyzeOrThrow "staged" staged
  expectInputStage staged stagedAnalysis "required" .comptime
  expectInputStage staged stagedAnalysis "flexible" .comptime

  let integerResult ← functionNamed program "integerResult"
  let integerResultAnalysis ← analyzeOrThrow "integerResult" integerResult
  expectInputStage integerResult integerResultAnalysis "value" .comptime

  let classify ← functionNamed program "classify"
  let classifyAnalysis ← analyzeOrThrow "classify" classify
  expectInputStage classify classifyAnalysis "fixed" .comptime
  expectInputStage classify classifyAnalysis "runtime" .runtime
  expectInputStage classify classifyAnalysis "flag" .runtime

private def testLetAndCallClassification
    (program : CheckedProgram) : IO Unit := do
  let function ← functionNamed program "classify"
  let analysis ← analyzeOrThrow "classify" function

  expectLetStage function analysis "ct" .comptime
  expectLetStage function analysis "ctAlias" .comptime
  expectLetStage function analysis "runtimeAlias" .runtime
  expectLetStage function analysis "runtimeAlias2" .runtime
  expectLetStage function analysis "deferred" .deferred
  expectLetStage function analysis "deferredAlias" .deferred

  expectLetStage function analysis "stagedCt" .comptime
  expectLetStage function analysis "stagedDeferred" .deferred
  expectLetStage function analysis "implicitCt" .comptime
  expectLetStage function analysis "implicitDeferred" .deferred
  expectLetStage function analysis "groupRuntime" .runtime
  expectLetStage function analysis "unaryCt" .comptime
  expectLetStage function analysis "binaryCt" .comptime
  expectLetStage function analysis "binaryRuntime" .runtime
  expectCallCalleeDeferred function analysis "deferred"
  expectCallCalleeDeferred function analysis "stagedCt"
  expectCallCalleeDeferred function analysis "stagedDeferred"
  expectCallCalleeDeferred function analysis "implicitCt"

private def testJoinClassification (program : CheckedProgram) : IO Unit := do
  let function ← functionNamed program "classify"
  let analysis ← analyzeOrThrow "classify" function

  expectLetStage function analysis "tupleCt" .comptime
  expectLetStage function analysis "tupleDeferred" .deferred
  expectLetStage function analysis "tupleRuntime" .runtime
  expectLetStage function analysis "condCt" .comptime
  expectLetStage function analysis "condDeferred" .deferred
  expectLetStage function analysis "condRuntime" .runtime
  expectLetStage function analysis "runtimeGuard" .runtime

private def testLambdaClassification (program : CheckedProgram) : IO Unit := do
  let function ← functionNamed program "lambdaStages"
  let analysis ← analyzeOrThrow "lambdaStages" function
  let staged ← lambdaLetNamed function "stagedLambda"
  let runtime ← lambdaLetNamed function "runtimeLambda"

  assertTrue staged.parameter.comptime
    "an explicit comptime lambda marker was not retained on its typed binder"
  assertTrue (!runtime.parameter.comptime)
    "an ordinary lambda parameter unexpectedly retained a comptime marker"
  expectBinderStage "comptime lambda parameter" analysis staged.parameter
    .comptime
  expectExpressionStage "comptime lambda body reference" analysis
    staged.returned .comptime
  expectExpressionStage "comptime lambda expression" analysis
    staged.expression .deferred
  expectBinderStage "runtime lambda parameter" analysis runtime.parameter
    .runtime
  expectExpressionStage "runtime lambda body reference" analysis
    runtime.returned .runtime
  expectExpressionStage "runtime lambda expression" analysis
    runtime.expression .deferred

private def testHiddenMatchBinderIsNotLexical
    (program : CheckedProgram) : IO Unit := do
  let function ← functionNamed program "matchStages"
  let _ ← analyzeOrThrow "matchStages" function
  let resolution ← match function.typedBody.roots with
    | [.statement root] =>
        match function.typedBody.lookupStatement? root with
        | some { form := .matchWith resolution, .. } => pure resolution
        | _ => throw (IO.userError "matchStages lost its match root")
    | roots => throw (IO.userError
        s!"matchStages retained {roots.length} roots")
  let returned ← match resolution.cases with
    | first :: _ =>
        match first.body with
        | [statement] =>
            match function.typedBody.lookupStatement? statement with
            | some { form := .returnStmt (some expression), .. } =>
                pure expression
            | _ => throw (IO.userError
                "matchStages first arm lost its value return")
        | body => throw (IO.userError
            s!"matchStages first arm retained {body.length} statements")
    | [] => throw (IO.userError "matchStages retained no match cases")
  let forged : CheckedFunction := {
    function with typedBody := {
      function.typedBody with
      nodes := function.typedBody.nodes.map fun
        | .expression node =>
            if node.id = returned then
              .expression { node with
                form := .reference "hidden" (.local resolution.hiddenScrutinee)
              }
            else
              .expression node
        | .statement node => .statement node
    }
  }
  expectAnalysisError "hidden match binder visibility"
    (analyzeFunction forged)
    (.unknownLocal returned resolution.hiddenScrutinee)

private def testMalformedCarriers (program : CheckedProgram) : IO Unit := do
  let function ← functionNamed program "classify"
  let other ← functionNamed program "plain"

  let wrongOwner : CheckedFunction := {
    function with typedBody := {
      function.typedBody with owner := other.declaration
    }
  }
  expectAnalysisError "typed-source owner mismatch"
    (analyzeFunction wrongOwner)
    (.sourceOwnerMismatch function.declaration other.declaration)

  match function.typedBody.nodes with
  | [] => throw (IO.userError
      "classify unexpectedly retained an empty typed-source table")
  | node :: _ =>
      let duplicated : CheckedFunction := {
        function with typedBody := {
          function.typedBody with nodes := node :: function.typedBody.nodes
        }
      }
      expectAnalysisError "duplicate occurrence"
        (analyzeFunction duplicated)
        (.duplicateOccurrence node.occurrenceId)

  match function.typedBody.inputs with
  | [] => throw (IO.userError "classify unexpectedly retained no inputs")
  | input :: _ =>
      let duplicated : CheckedFunction := {
        function with typedBody := {
          function.typedBody with
          inputs := input :: function.typedBody.inputs
        }
      }
      expectAnalysisError "duplicate binder"
        (analyzeFunction duplicated)
        (.duplicateBinder input.id)

/-- Exercise the public join and scope-aware function analysis over a checked
source fixture containing all three source stages. -/
def testSourceStageClassification : IO Unit := do
  testJoin
  let program ← checkedProgram
  testInputClassification program
  testLetAndCallClassification program
  testJoinClassification program
  testLambdaClassification program
  testHiddenMatchBinderIsNotLexical program
  testMalformedCarriers program

end Tests.SourceStageClassification
end

section
-- leanmerge: from Solcore.Test.SourceStructuralExpressions
/-! End-to-end source inference for proxy values and mapping indexing. -/

set_option autoImplicit false

namespace Tests.SourceStructuralExpressions

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def check (content : String) :
    IO (List SourceInference.CheckedFunction) := do
  match SourceInference.loadAndCheckProgram (workspace content) with
  | .ok checked => pure checked
  | .error errors =>
      throw (IO.userError s!"structural expression checking failed: {reprStr errors}")

private def hasBodyError (content : String)
    (accepts : SourceInference.Error → Bool) : IO Bool :=
  match SourceInference.loadAndCheckProgram (workspace content) with
  | .error errors => pure <| errors.any fun error => match error with
      | .body functionError => accepts functionError.error
      | _ => false
  | .ok _ => pure false

private def testProxyValuesResolveSourceTypes : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "function concrete() returns (@Word) { return @Word; }",
    "function generic<T>() returns (@T) { return @T; }"
  ])
  match checked with
  | [concrete, generic] =>
      assertTrue (decide (concrete.inferredBodyType = .proxy .word))
        "a proxy value did not retain its resolved builtin type"
      assertTrue (match generic.inferredBodyType with
        | .proxy (.parameter parameter) =>
            decide (parameter.owner = generic.declaration) && parameter.index == 0
        | _ => false)
        "a proxy value did not retain its declaration-owned generic parameter"
  | _ => throw (IO.userError "proxy fixture lost a checked function")

private def testMappingIndexInfersValue : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "function read(values: mapping(Word => Bool), key: Word) returns (Bool) {",
    "  return values[key];",
    "}",
    "function readLiteral(values: mapping(Word => Bool)) returns (Bool) {",
    "  return values[1];",
    "}"
  ])
  match checked with
  | [read, readLiteral] =>
      assertTrue (decide (read.inferredBodyType = .bool ∧
          read.solvedRequirements = []))
        "ordinary mapping indexing acquired unrelated evidence"
      assertTrue (decide (readLiteral.inferredBodyType = .bool ∧
          readLiteral.predicates = [
            ProgramSignatures.builtinIntPredicate .word
          ]))
        "literal mapping key lost its sole builtin Int<Word> obligation"
  | functions => throw (IO.userError
      s!"mapping fixture checked {functions.length} functions")

private def testMappingKeyUsesCoercion : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "impl Coerce<Bool, Word> {}",
    "function read(values: mapping(Word => Bool), key: Bool) returns (Bool) {",
    "  return values[key];",
    "}"
  ])
  match checked.getLast? with
  | some function =>
      assertTrue (function.predicates.length == 1 &&
          function.evidence.any fun evidence => match evidence with
            | .implementation _ => true
            | .assumption _ => false)
        "a mapping key coercion lost its predicate or implementation evidence"
  | none => throw (IO.userError "mapping coercion fixture checked no function")

private def testNonMappingBaseIsRejected : IO Unit := do
  let rejected ← hasBodyError
    "function bad(value: Word) returns (Word) { return value[0]; }"
    fun error => match error with
      | .unification (.mismatch _ (.mapping _ _)) => true
      | _ => false
  assertTrue rejected "indexing a non-mapping value did not report a type mismatch"

private def testWrongMappingKeyIsRejected : IO Unit := do
  let rejected ← hasBodyError (String.intercalate "\n" [
    "function bad(values: mapping(Word => Bool)) returns (Bool) {",
    "  return values[true];",
    "}"
  ]) fun error => match error with
    | .unification (.mismatch .bool .word) => true
    | .unification (.mismatch .word .bool) => true
    | _ => false
  assertTrue rejected "a mapping index with the wrong key type was accepted"

private def testUnknownProxyTypeIsRejected : IO Unit := do
  let rejected ← hasBodyError
    "function bad() returns (@Word) { return @Missing; }"
    fun error => match error with
      | .typeResolution (.unknownTypeName ["Missing"]) => true
      | _ => false
  assertTrue rejected "an unknown type in a proxy value was accepted"

/-- Exercise source type resolution, unification and coercion through the first
advanced structural expression forms. -/
def testSourceStructuralExpressions : IO Unit := do
  testProxyValuesResolveSourceTypes
  testMappingIndexInfersValue
  testMappingKeyUsesCoercion
  testNonMappingBaseIsRejected
  testWrongMappingKeyIsRejected
  testUnknownProxyTypeIsRejected

end Tests.SourceStructuralExpressions
end
