import Solcore.Frontend.SourceInference

/-! Focused parsed-source regressions for the source inference slice. -/

set_option autoImplicit false

namespace Tests.SourceInference

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

private def load (content : String) : IO LoadedProgram := do
  match loadProgram (workspace content) with
  | .ok loaded => pure loaded
  | .error errors =>
      throw (IO.userError s!"source inference loading failed: {reprStr errors}")

private def checkedNamed (environment : ProgramEnvironment)
    (checked : List SourceInference.CheckedFunction) (name : String) :
    IO SourceInference.CheckedFunction :=
  match checked.find? fun function =>
      (environment.declaration? function.declaration).any fun declaration =>
        declaration.name == some name with
  | some function => pure function
  | none => throw (IO.userError s!"checked function `{name}` was not found")

private def traitNameOf (environment : ProgramEnvironment)
    (predicate : ProgramPredicate) : Option String := do
  let trait ← predicate.trait.declaration?
  let declaration ← environment.declaration? trait
  declaration.name

private def testLambdaLetTupleConditional : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "function polymorphic(flag: Bool) returns (Word, Bool) {",
    "  let id = lam(value) { return value; };",
    "  return (id(((1))), id(flag ? flag : !flag));",
    "}",
    "function expected(flag: Bool) returns (function(Word) returns (Word)) {",
    "  return lam(value) { return flag ? value + 1 : value; };",
    "}",
    "function empty() { return (); }"
  ])
  assertTrue (decide (checked.length = 3))
    "lambda/let/tuple fixture lost a checked function"
  match checked with
  | first :: second :: third :: [] =>
      assertTrue (decide (first.inferredBodyType =
          TypeSystem.Ty.product .word .bool))
        "let-polymorphic tuple did not infer Word × Bool"
      assertTrue (decide (second.inferredBodyType =
          TypeSystem.Ty.function .word .word))
        "expected function type did not guide an inferred lambda"
      assertTrue (decide (third.inferredBodyType = .unit))
        "empty tuple did not check as Unit"
  | _ => throw (IO.userError "checked function order changed")

private def testAmbiguousOverload : IO Unit := do
  let source := String.intercalate "\n" [
    "function choose(value: Word) returns (Word) { return value; }",
    "function choose(other: Word) returns (Word) { return other + 1; }",
    "function run() returns (Word) { return choose(1); }"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .ambiguousOverload "choose" candidates, .. } =>
            candidates.length == 2
        | _ => false) "ambiguous overload was not reported explicitly"
  | .ok _ => throw (IO.userError "ambiguous overload was selected")

private def testNumericExpectedType : IO Unit := do
  let source := "function bad() returns (Bool) { return 1; }"
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .nonNumericLiteral .bool, .. } => true
        | _ => false) "a numeric literal silently checked as Bool"
  | .ok _ => throw (IO.userError "a numeric literal checked as Bool")

private def testTraitBackedLiteral : IO Unit := do
  let source := String.intercalate "\n" [
    "trait FromLiteral<T> {}",
    "enum Box { Only }",
    "impl FromLiteral<Box> {}",
    "function literal() returns (Box) { return 1; }"
  ]
  let checked ← check source
  match checked with
  | [function] =>
      assertTrue (decide (function.predicates.length = 1) &&
          function.evidence.any fun evidence => match evidence with
            | .implementation _ => true
            | .assumption _ => false)
        "trait-backed non-Word literal lost its predicate or evidence"
  | _ => throw (IO.userError "literal fixture lost its checked function")

private def testUnsupportedStatement : IO Unit := do
  let source :=
    "function loop(flag: Bool) { while (flag) { return; } }"
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .unsupportedStatement "while loop", .. } => true
        | _ => false) "deferred while inference was not explicit"
  | .ok _ => throw (IO.userError "deferred while inference was accepted")

private def testTraitBackedCoercion : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "impl Coerce<Word, Box> {}",
    "function accept(value: Box) returns (Box) { return value; }",
    "function convert(value: Word) returns (Box) { return accept(value); }"
  ]
  let checked ← check source
  match checked.find? fun function =>
      function.evidence.any fun evidence => match evidence with
        | .implementation _ => true
        | .assumption _ => false with
  | some function =>
      assertTrue (decide (function.predicates.length = 1))
        "coercion evidence lost its Coerce predicate"
  | none => throw (IO.userError "trait-backed coercion produced no evidence")

private def testMissingCoercion : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "function accept(value: Box) returns (Box) { return value; }",
    "function reject(value: Word) returns (Box) { return accept(value); }"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            predicate.arguments.length == 1
        | _ => false) "missing coercion implementation was accepted"
  | .ok _ => throw (IO.userError "missing coercion implementation was accepted")

private def testInconclusiveCoercion : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "impl Coerce<Word, Box> {}",
    "impl Coerce<Word, Box> {}",
    "function accept(value: Box) returns (Box) { return value; }",
    "function reject(value: Word) returns (Box) { return accept(value); }"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .inconclusiveTrait (.ambiguous _ _ _), .. } => true
        | _ => false) "overlapping coercion implementations lost ambiguity"
  | .ok _ => throw (IO.userError "ambiguous coercion implementation was selected")

private def testUnsolvedCoercionMethodPredicate : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Eq<T> {}",
    "trait Coerce<From, To> {",
    "  function coerce(value: From) returns (To) where From: Eq;",
    "}",
    "function acceptWord(value: Word) returns (Word) { return value; }",
    "function reject<T>(value: T) returns (Word) where T: Coerce<Word> {",
    "  return acceptWord(value);",
    "}"
  ]
  let loaded ← load source
  let eq ← match loaded.environment.traitsNamed "Eq" with
    | [declaration] => pure declaration.id
    | declarations => throw (IO.userError
        s!"expected one Eq trait, found {declarations.length}")
  match SourceInference.checkLoadedProgram loaded with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            decide (predicate.trait = eq) && predicate.arguments.isEmpty
        | _ => false)
        "a coercion method predicate was accepted without Eq<T>"
  | .ok _ => throw (IO.userError
      "a coercion method predicate was accepted without Eq<T>")

private def testConstrainedLetDoesNotGeneralizeAwayEvidence : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Eq<T> {}",
    "impl Eq<Word> {}",
    "function keep<T>(value: T) returns (T) where T: Eq { return value; }",
    "function reject() returns (Bool) {",
    "  let f = lam(value) { return keep(value); };",
    "  return f(true);",
    "}"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            predicate.subject == TypeSystem.Ty.bool
        | _ => false)
        "a constrained let detached its predicate from the instantiated type"
  | .ok _ => throw (IO.userError "Eq<Word> evidence was reused for Bool")

private def testOperatorMethodPredicates : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Eq<T> {}",
    "trait Noise<T> {}",
    "trait Add<T> {",
    "  function tag(value: T) returns (T) where T: Noise;",
    "  function add(left: T, right: T) returns (T) where T: Eq;",
    "}",
    "trait BitNot<T> {",
    "  function bnot(value: T) returns (T) where T: Eq;",
    "}",
    "function addWithMethodEvidence<T>(left: T, right: T) returns (T)",
    "    where T: Add, T: Eq {",
    "  return left + right;",
    "}",
    "function bitNotWithMethodEvidence<T>(value: T) returns (T)",
    "    where T: BitNot, T: Eq {",
    "  return ~value;",
    "}"
  ]
  let loaded ← load source
  let checked ← match SourceInference.checkLoadedProgram loaded with
    | .ok checked => pure checked
    | .error errors => throw (IO.userError
        s!"operator method predicates were rejected: {reprStr errors}")
  let addition ← checkedNamed loaded.environment checked
    "addWithMethodEvidence"
  let bitNot ← checkedNamed loaded.environment checked
    "bitNotWithMethodEvidence"
  let names (function : SourceInference.CheckedFunction) :=
    function.solvedRequirements.map fun solved =>
      traitNameOf loaded.environment solved.predicate
  let assumptionEvidence (function : SourceInference.CheckedFunction) :=
    function.solvedRequirements.all fun solved =>
      match solved.evidence with
      | .assumption predicate => predicate == solved.predicate
      | .implementation _ => false
  assertTrue (decide (names addition = [some "Add", some "Eq"]) &&
      assumptionEvidence addition)
    "binary inference did not retain Add<T>, Eq<T> in declaration order"
  assertTrue (decide (names bitNot = [some "BitNot", some "Eq"]) &&
      assumptionEvidence bitNot)
    "unary inference did not retain BitNot<T>, Eq<T> in declaration order"

private def testUnsolvedOperatorMethodPredicates : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Eq<T> {}",
    "trait Add<T> {",
    "  function add(left: T, right: T) returns (T) where T: Eq;",
    "}",
    "trait BitNot<T> {",
    "  function bnot(value: T) returns (T) where T: Eq;",
    "}",
    "function rejectAdd<T>(left: T, right: T) returns (T) where T: Add {",
    "  return left + right;",
    "}",
    "function rejectBitNot<T>(value: T) returns (T) where T: BitNot {",
    "  return ~value;",
    "}"
  ]
  let loaded ← load source
  let eq ← match loaded.environment.traitsNamed "Eq" with
    | [declaration] => pure declaration.id
    | declarations => throw (IO.userError
        s!"expected one Eq trait, found {declarations.length}")
  match SourceInference.checkLoadedProgram loaded with
  | .error errors =>
      let unsolved := errors.filter fun error => match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            decide (predicate.trait = eq)
        | _ => false
      assertTrue (unsolved.length == 2)
        "a binary or unary method predicate was accepted without Eq<T>"
  | .ok _ => throw (IO.userError
      "operator method predicates were accepted without Eq<T>")

private def testOperatorMethodCatalogDiagnostics : IO Unit := do
  let missingSource := String.intercalate "\n" [
    "trait Add<T> {",
    "  function tag(value: T) returns (T);",
    "}",
    "function reject<T>(left: T, right: T) returns (T) where T: Add {",
    "  return left + right;",
    "}"
  ]
  match SourceInference.loadAndCheckProgram (workspace missingSource) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .missingOperatorTraitMethod _ "add", .. } => true
        | _ => false)
        "a trait catalog without the named add method lost its diagnostic"
  | .ok _ => throw (IO.userError
      "a trait catalog without the named add method was accepted")

  let malformedSource := String.intercalate "\n" [
    "trait Add<T> {",
    "  function add(value: T) returns (Bool);",
    "}",
    "function reject<T>(left: T, right: T) returns (T) where T: Add {",
    "  return left + right;",
    "}"
  ]
  match SourceInference.loadAndCheckProgram (workspace malformedSource) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := (.operatorTraitMethodSignatureMismatch _ "add"
            expectedParameters actualParameters expectedReturns actualReturns),
            .. } => decide (expectedParameters.length = 2 ∧
              actualParameters.length = 1 ∧ expectedReturns.length = 1 ∧
              actualReturns = [.bool])
        | _ => false)
        "a malformed add method lost its operator-signature diagnostic"
  | .ok _ => throw (IO.userError
      "a malformed add method was accepted as binary operator semantics")

  let duplicateSource := String.intercalate "\n" [
    "trait Add<T> {",
    "  function add(left: T, right: T) returns (T);",
    "}",
    "function reject<T>(left: T, right: T) returns (T) where T: Add {",
    "  return left + right;",
    "}"
  ]
  let loaded ← load duplicateSource
  let signatures ← match buildProgramSignatures loaded.environment with
    | .ok signatures => pure signatures
    | .error errors => throw (IO.userError
        s!"operator catalog fixture failed: {reprStr errors}")
  let add ← match signatures.traits.filter fun trait => trait.name == "Add" with
    | [trait] => pure trait
    | traits => throw (IO.userError
        s!"expected one Add catalog, found {traits.length}")
  let method ← match add.methods with
    | [method] => pure method
    | methods => throw (IO.userError
        s!"expected one Add method, found {methods.length}")
  let duplicate := {
    method with id := { method.id with methodIndex := method.id.methodIndex + 1 }
  }
  let tampered := {
    signatures with
    traits := signatures.traits.map fun trait =>
      if trait.id = add.id then { trait with methods := trait.methods ++ [duplicate] }
      else trait
  }
  match SourceInference.checkFunctionBodies loaded.environment tampered with
  | .error errors =>
      assertTrue (errors.any fun error => match error.error with
        | .duplicateOperatorTraitMethod trait "add" 2 => trait == add.id
        | _ => false)
        "a duplicate named operator method lost its defensive diagnostic"
  | .ok _ => throw (IO.userError
      "a duplicate named operator method was selected silently")

private def testAmbiguousCoercionTrait : IO Unit := do
  let raw : Workspace.RawWorkspace := {
    entry := "main.solc"
    mainSources := [
      { path := "left.solc", content := "trait Coerce<From, To> {}" },
      { path := "right.solc", content := "trait Coerce<From, To> {}" },
      {
        path := "main.solc"
        content := String.intercalate "\n" [
          "function accept(value: Bool) returns (Bool) { return value; }",
          "function reject(value: Word) returns (Bool) { return accept(value); }"
        ]
      }
    ]
    externalLibraries := []
  }
  match SourceInference.loadAndCheckProgram raw with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .ambiguousOperatorTrait "Coerce" candidates, .. } =>
            candidates.length == 2
        | _ => false) "ambiguous Coerce declarations lost their diagnostic"
  | .ok _ => throw (IO.userError "ambiguous Coerce declaration was selected")

/-- Exercise parsed lambdas, local schemes, tuples, grouping, conditionals,
operators, numeric expected/default behavior, and explicit deferrals. -/
def testSourceInference : IO Unit := do
  testLambdaLetTupleConditional
  testAmbiguousOverload
  testNumericExpectedType
  testTraitBackedLiteral
  testUnsupportedStatement
  testTraitBackedCoercion
  testMissingCoercion
  testInconclusiveCoercion
  testUnsolvedCoercionMethodPredicate
  testConstrainedLetDoesNotGeneralizeAwayEvidence
  testOperatorMethodPredicates
  testUnsolvedOperatorMethodPredicates
  testOperatorMethodCatalogDiagnostics
  testAmbiguousCoercionTrait

end Tests.SourceInference
