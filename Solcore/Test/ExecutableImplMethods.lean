import Solcore.Frontend.ExecutableImplMethods
import Solcore.Frontend.SourceCoreElaboration

/-! Executable regressions for checked monomorphic implementation methods. -/

set_option autoImplicit false

namespace Tests.ExecutableImplMethods

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def singleSourceWorkspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def checkedProgramOf (content : String) : IO CheckedProgram := do
  match checkProgram (singleSourceWorkspace content) with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"implementation-method fixture failed checking: {reprStr errors}")

private def onlyImplementation (program : CheckedProgram) :
    IO ProgramImplementationSignature := do
  match program.signatures.implementations with
  | [implementation] => pure implementation
  | implementations => throw (IO.userError
      s!"expected one implementation, found {implementations.length}")

private def evidenceFor (implementation : ProgramImplementationSignature) :
    TypedTraitResolution.Evidence :=
  .byImpl implementation.head implementation.id []

private def successSource : String := String.intercalate "\n" [
  "trait Add<T> {",
  "  function add(left: T, right: T) returns (T);",
  "}",
  "impl Add<Word> {",
  "  function add(left: Word, right: Word) returns (Word) {",
  "    return left - right;",
  "  }",
  "}"
]

private def coerceSource : String := String.intercalate "\n" [
  "trait Coerce<From, To> {",
  "  function coerce(value: From) returns (To);",
  "}",
  "impl Coerce<Word, Bool> {",
  "  function coerce(value: Word) returns (Bool) {",
  "    return true;",
  "  }",
  "}"
]

private def testSuccessfulMethodCheck : IO Unit := do
  let program ← checkedProgramOf successSource
  let implementation ← onlyImplementation program
  let catalogMethod ← match implementation.methods with
    | [catalogMethod] => pure catalogMethod
    | methods => throw (IO.userError
        s!"expected one implementation method, found {methods.length}")
  let method ← match ExecutableImplMethods.checkMonomorphicPremiseFreeMethod
      program (evidenceFor implementation) "add" with
    | .ok method => pure method
    | .error error => throw (IO.userError
        s!"executable add method was rejected: {reprStr error}")
  assertTrue (decide (method.id.implementation = implementation.id ∧
      method.id.methodIndex = 0 ∧
      method.traitMethod.id = catalogMethod.traitMethod ∧
      method.synthetic.parameterTypes = [.word, .word] ∧
      method.synthetic.returnTypes = [.word] ∧
      method.synthetic.scheme.parameters = [] ∧
      method.synthetic.scheme.predicates = [] ∧
      method.checked.declaration = implementation.id ∧
      method.checked.type = .function (.product .word .word) .word ∧
      method.checked.inferredBodyType = .word ∧
      method.checked.solvedRequirements = []))
    "checked implementation method lost its catalog or inferred type facts"
  let elaborated ← match SourceCoreElaboration.elaborateFunction method.checked with
    | .ok elaborated => pure elaborated
    | .error error => throw (IO.userError
        s!"checked add method did not lower to Core: {reprStr error}")
  assertTrue (decide (elaborated.inputs.values = [.word, .word] ∧
      elaborated.returnType = .word ∧
      Core.infer? elaborated.inputs.values elaborated.core = some .word))
    "checked add method did not retain Word inputs and a Word result"

private def testTwoParameterTraitMethodCheck : IO Unit := do
  let program ← checkedProgramOf coerceSource
  let implementation ← onlyImplementation program
  let method ← match ExecutableImplMethods.checkMonomorphicPremiseFreeMethodWithArity
      program (evidenceFor implementation) 2 "coerce" with
    | .ok method => pure method
    | .error error => throw (IO.userError
        s!"executable Coerce method was rejected: {reprStr error}")
  assertTrue (decide (implementation.head.subject = .word ∧
      implementation.head.arguments = [.bool] ∧
      method.synthetic.parameterTypes = [.word] ∧
      method.synthetic.returnTypes = [.bool] ∧
      method.checked.type = .function .word .bool ∧
      method.checked.inferredBodyType = .bool ∧
      method.checked.solvedRequirements = []))
    "checked Coerce method lost its two-parameter trait or method types"
  let elaborated ← match SourceCoreElaboration.elaborateFunction method.checked with
    | .ok elaborated => pure elaborated
    | .error error => throw (IO.userError
        s!"checked Coerce method did not lower to Core: {reprStr error}")
  assertTrue (decide (elaborated.inputs.values = [.word] ∧
      elaborated.returnType = .bool ∧
      Core.infer? elaborated.inputs.values elaborated.core = some .bool))
    "checked Coerce method did not retain a Word input and Bool result"

private def testTraitPredicateInstantiation : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Eq<T> {}",
    "trait Ord<T> where T: Eq {",
    "  function gt(left: T, right: T) returns (Bool);",
    "}",
    "impl Ord<Word> {",
    "  function gt(left: Word, right: Word) returns (Bool) { return true; }",
    "}"
  ])
  let implementation ← onlyImplementation program
  let eq ← match program.signatures.traits.filter fun trait =>
      trait.name == "Eq" with
    | [trait] => pure trait
    | traits => throw (IO.userError
        s!"expected one Eq trait, found {traits.length}")
  let ord ← match program.signatures.traits.filter fun trait =>
      trait.name == "Ord" with
    | [trait] => pure trait
    | traits => throw (IO.userError
        s!"expected one Ord trait, found {traits.length}")
  let eqWord : ProgramPredicate := {
    trait := eq.id
    subject := .word
    arguments := []
  }
  let method ← match ExecutableImplMethods.checkMonomorphicPremiseFreeMethodWithArity
      program (evidenceFor implementation) 1 "gt" with
    | .ok method => pure method
    | .error error => throw (IO.userError
        s!"trait-constrained Ord.gt method was rejected: {reprStr error}")
  assertTrue (decide (implementation.head.trait = ord.id ∧
      implementation.head.subject = .word ∧
      implementation.wherePredicates = [] ∧
      method.synthetic.scheme.parameters = [] ∧
      method.synthetic.scheme.predicates = [eqWord] ∧
      method.synthetic.parameterTypes = [.word, .word] ∧
      method.synthetic.returnTypes = [.bool] ∧
      method.checked.type = .function (.product .word .word) .bool ∧
      method.checked.inferredBodyType = .bool ∧
      method.checked.solvedRequirements = []))
    "Ord.gt did not retain the instantiated Eq<Word> static assumption"
  let elaborated ← match SourceCoreElaboration.elaborateFunction method.checked with
    | .ok elaborated => pure elaborated
    | .error error => throw (IO.userError
        s!"requirement-free Ord.gt body did not lower to Core: {reprStr error}")
  assertTrue (decide (elaborated.inputs.values = [.word, .word] ∧
      elaborated.returnType = .bool ∧
      Core.infer? elaborated.inputs.values elaborated.core = some .bool))
    "trait predicate assumptions changed the closed Ord.gt runtime body"

private def testTraitPredicateParameterOrder : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Rel<Left, Right> {}",
    "trait Route<From, To> where From: Rel<To> {",
    "  function route(value: From) returns (To);",
    "}",
    "impl Route<Word, Bool> {",
    "  function route(value: Word) returns (Bool) { return true; }",
    "}"
  ])
  let implementation ← onlyImplementation program
  let rel ← match program.signatures.traits.filter fun trait =>
      trait.name == "Rel" with
    | [trait] => pure trait
    | traits => throw (IO.userError
        s!"expected one Rel trait, found {traits.length}")
  let relWordBool : ProgramPredicate := {
    trait := rel.id
    subject := .word
    arguments := [.bool]
  }
  let method ← match ExecutableImplMethods.checkMonomorphicPremiseFreeMethodWithArity
      program (evidenceFor implementation) 2 "route" with
    | .ok method => pure method
    | .error error => throw (IO.userError
        s!"two-parameter trait predicate was rejected: {reprStr error}")
  assertTrue (decide (implementation.head.subject = .word ∧
      implementation.head.arguments = [.bool] ∧
      method.synthetic.scheme.predicates = [relWordBool]))
    "trait subject and argument parameters were instantiated out of order"

private def testUnclosedTraitPredicateRejection : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Eq<T> {}",
    "trait Ord<T> where T: Eq {",
    "  function gt(left: T, right: T) returns (Bool);",
    "}",
    "impl Ord<Word> {",
    "  function gt(left: Word, right: Word) returns (Bool) { return true; }",
    "}"
  ])
  let implementation ← onlyImplementation program
  let ord ← match program.signatures.traits.filter fun trait =>
      trait.name == "Ord" with
    | [trait] => pure trait
    | traits => throw (IO.userError
        s!"expected one Ord trait, found {traits.length}")
  let foreignParameter : TypeSystem.TypeParameterId := {
    owner := ord.id
    index := ord.parameters.length + 7
  }
  let openPredicate ← match ord.wherePredicates with
    | [predicate] => pure { predicate with subject := .parameter foreignParameter }
    | predicates => throw (IO.userError
        s!"expected one Ord trait predicate, found {predicates.length}")
  let tamperedOrd := { ord with wherePredicates := [openPredicate] }
  let tamperedProgram : CheckedProgram := {
    program with
    signatures := {
      program.signatures with
      traits := program.signatures.traits.map fun trait =>
        if trait.id = ord.id then tamperedOrd else trait
    }
  }
  match ExecutableImplMethods.checkMonomorphicPremiseFreeMethodWithArity
      tamperedProgram (evidenceFor implementation) 1 "gt" with
  | .error (.traitPredicateNotClosed trait predicate (.rigid parameter)) =>
      assertTrue (decide (trait = ord.id ∧ predicate = openPredicate ∧
          parameter = foreignParameter))
        "unclosed trait-predicate rejection lost its trait or rigid parameter"
  | .error error => throw (IO.userError
      s!"unclosed trait predicate had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError
      "unclosed trait predicate crossed the executable-method boundary")

private def testEmptyMarkerRejection : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Marker<T> {}",
    "impl Marker<Word> {}"
  ])
  let implementation ← onlyImplementation program
  match ExecutableImplMethods.checkMonomorphicPremiseFreeMethodWithArity program
      (evidenceFor implementation) 1 "mark" with
  | .error (.missingImplementationMethod id "mark") =>
      assertTrue (decide (id = implementation.id))
        "marker rejection named the wrong implementation"
  | .error error => throw (IO.userError
      s!"empty marker had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError
      "empty marker implementation invented a runtime method")

private def testDefensiveProfileRejections : IO Unit := do
  let program ← checkedProgramOf successSource
  let implementation ← onlyImplementation program
  let premise := evidenceFor implementation
  let evidence : TypedTraitResolution.Evidence :=
    .byImpl implementation.head implementation.id [premise]
  match ExecutableImplMethods.checkMonomorphicPremiseFreeMethodWithArity program evidence
      1 "add" with
  | .error (.evidencePremisesPresent id 1) =>
      assertTrue (decide (id = implementation.id))
        "premise rejection named the wrong implementation"
  | .error error => throw (IO.userError
      s!"premise-bearing evidence had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError "premise-bearing evidence was executable")
  let duplicateProgram : CheckedProgram := {
    program with
    signatures := {
      program.signatures with
      implementations := program.signatures.implementations ++ [implementation]
    }
  }
  match ExecutableImplMethods.checkMonomorphicPremiseFreeMethodWithArity
      duplicateProgram (evidenceFor implementation) 1 "add" with
  | .error (.duplicateImplementations id 2) =>
      assertTrue (decide (id = implementation.id))
        "duplicate rejection named the wrong implementation"
  | .error error => throw (IO.userError
      s!"duplicate implementation had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError "duplicate implementation catalog was accepted")
  match ExecutableImplMethods.checkMonomorphicPremiseFreeMethodWithArity program
      (evidenceFor implementation) 1 "sum" with
  | .error (.implementationMethodNameMismatch _ "sum" "add") => pure ()
  | .error error => throw (IO.userError
      s!"wrong method name had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError "wrong expected method name was accepted")
  match ExecutableImplMethods.checkMonomorphicPremiseFreeMethodWithArity program
      (evidenceFor implementation) 2 "add" with
  | .error (.evidenceGoalArityMismatch trait 2 1) =>
      assertTrue (decide (trait = implementation.head.trait))
        "evidence-goal arity rejection named the wrong trait"
  | .error error => throw (IO.userError
      s!"wrong evidence-goal arity had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError "wrong evidence-goal arity was accepted")
  let openGoal : ProgramPredicate := {
    implementation.head with
    subject := .variable ⟨17⟩
  }
  let openEvidence : TypedTraitResolution.Evidence :=
    .byImpl openGoal implementation.id []
  match ExecutableImplMethods.checkMonomorphicPremiseFreeMethodWithArity program
      openEvidence 1 "add" with
  | .error (.evidenceGoalNotClosed goal (.flexible metavariable)) =>
      assertTrue (decide (goal = openGoal ∧ metavariable.index = 17))
        "non-closed evidence rejection lost its goal or flexible variable"
  | .error error => throw (IO.userError
      s!"non-closed evidence goal had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError "non-closed evidence goal was accepted")

private def testGenericImplementationRejection : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Identity<T> { function identity(value: T) returns (T); }",
    "impl<T> Identity<T> {",
    "  function identity(value: T) returns (T) { return value; }",
    "}"
  ])
  let implementation ← onlyImplementation program
  match ExecutableImplMethods.checkMonomorphicPremiseFreeMethodWithArity program
      (evidenceFor implementation) 1 "identity" with
  | .error (.implementationParametersPresent id [_]) =>
      assertTrue (decide (id = implementation.id))
        "generic rejection named the wrong implementation"
  | .error error => throw (IO.userError
      s!"generic implementation had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError "generic implementation was executable")

private def testWherePredicateRejection : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Eq<T> {}",
    "trait Add<T> { function add(left: T, right: T) returns (T); }",
    "impl Add<Word> where Word: Eq {",
    "  function add(left: Word, right: Word) returns (Word) { return left; }",
    "}"
  ])
  let implementation ← onlyImplementation program
  match ExecutableImplMethods.checkMonomorphicPremiseFreeMethodWithArity program
      (evidenceFor implementation) 1 "add" with
  | .error (.implementationPredicatesPresent id [_]) =>
      assertTrue (decide (id = implementation.id))
        "where-predicate rejection named the wrong implementation"
  | .error error => throw (IO.userError
      s!"where-constrained implementation had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError
      "where-constrained implementation was executable")

private def testMethodPredicateRejections : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Eq<T> {}",
    "trait Guard<T> {",
    "  function guard(value: T) returns (T) where T: Eq;",
    "}",
    "impl Guard<Word> {",
    "  function guard(value: Word) returns (Word) where Word: Eq { return value; }",
    "}"
  ])
  let implementation ← onlyImplementation program
  let implementationMethod ← match implementation.methods with
    | [method] => pure method
    | methods => throw (IO.userError
        s!"expected one Guard implementation method, found {methods.length}")
  match ExecutableImplMethods.checkMonomorphicPremiseFreeMethodWithArity program
      (evidenceFor implementation) 1 "guard" with
  | .error (.implementationMethodPredicatesPresent id [_]) =>
      assertTrue (decide (id = implementationMethod.id))
        "method-predicate rejection named the wrong implementation method"
  | .error error => throw (IO.userError
      s!"where-constrained implementation method had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError
      "where-constrained implementation method was executable")
  let strippedImplementation : ProgramImplementationSignature := {
    implementation with
    methods := implementation.methods.map fun method => {
      method with wherePredicates := []
    }
  }
  let strippedProgram : CheckedProgram := {
    program with
    signatures := {
      program.signatures with
      implementations := [strippedImplementation]
    }
  }
  match ExecutableImplMethods.checkMonomorphicPremiseFreeMethodWithArity
      strippedProgram (evidenceFor strippedImplementation) 1 "guard" with
  | .error (.traitMethodPredicatesPresent id [_]) =>
      assertTrue (decide (id = implementationMethod.traitMethod))
        "method-predicate rejection named the wrong trait method"
  | .error error => throw (IO.userError
      s!"where-constrained trait method had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError
      "where-constrained trait method was executable")

private def testBodyIsActuallyChecked : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Add<T> { function add(left: T, right: T) returns (T); }",
    "impl Add<Word> {",
    "  function add(left: Word, right: Word) returns (Word) {",
    "    return missing;",
    "  }",
    "}"
  ])
  let implementation ← onlyImplementation program
  match ExecutableImplMethods.checkMonomorphicPremiseFreeMethodWithArity program
      (evidenceFor implementation) 1 "add" with
  | .error (.sourceInference (.unknownVariable "missing")) => pure ()
  | .error error => throw (IO.userError
      s!"invalid method body had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError
      "invalid implementation method body bypassed source checking")

/-- Exercise executable method selection, body checking, Core lowering, and
the first profile's explicit staged boundaries. -/
def testExecutableImplMethods : IO Unit := do
  testSuccessfulMethodCheck
  testTwoParameterTraitMethodCheck
  testTraitPredicateInstantiation
  testTraitPredicateParameterOrder
  testUnclosedTraitPredicateRejection
  testEmptyMarkerRejection
  testDefensiveProfileRejections
  testGenericImplementationRejection
  testWherePredicateRejection
  testMethodPredicateRejections
  testBodyIsActuallyChecked

end Tests.ExecutableImplMethods
