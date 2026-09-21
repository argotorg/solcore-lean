import Solcore.Frontend.SourceInference

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
  testIrrelevantAmbiguousBranchDoesNotBlock
  testAssumptionEdgeRetainsEvidence
  testGenericEdgeSolvesWherePredicate
  testMethodPredicateFailureFallsBackToTwoSteps
  testAmbiguousDirectPathDoesNotFallBack
  testEqualLengthPathsAreAmbiguous
  testCycleTerminates
  testDepthBoundaryIsExplicit

end Tests.SourceMultiStepCoercion
