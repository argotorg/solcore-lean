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
  testEmptyMarkerRejection
  testDefensiveProfileRejections
  testGenericImplementationRejection
  testWherePredicateRejection
  testBodyIsActuallyChecked

end Tests.ExecutableImplMethods
