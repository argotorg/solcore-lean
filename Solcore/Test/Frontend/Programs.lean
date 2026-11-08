import Solcore.Frontend.ExecutableImplMethods
import Solcore.Frontend.SourceCoreElaboration
import Solcore.Frontend.ProgramChecking
import Solcore.Syntax.Parser
import Solcore.Frontend.ProgramTypeResolution
import Solcore.Frontend.TraitResolution
import Solcore.Frontend.ProgramInterfaces
import Solcore.Frontend.Internal.CheckingProperties
import Solcore.Frontend.ProgramSignatures

/-!
# Whole program tests

Program loading and checking: imports, interfaces, signatures, type aliases, trait resolution and
executable implementation methods.
-/

section
-- leanmerge: from Solcore.Test.ExecutableImplMethods
/-! Executable regressions for checked and ground-specialized implementation methods. -/

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

private def implementationForTrait (program : CheckedProgram)
    (name : String) : IO ProgramImplementationSignature := do
  let trait ← match program.signatures.traits.filter fun trait =>
      trait.name == name with
    | [trait] => pure trait
    | traits => throw (IO.userError
        s!"expected one {name} trait, found {traits.length}")
  match program.signatures.implementations.filter fun implementation =>
      decide (implementation.head.trait = ProgramTraitId.declaration trait.id) with
  | [implementation] => pure implementation
  | implementations => throw (IO.userError
      s!"expected one {name} implementation, found {implementations.length}")

private def selectedEvidenceFor (program : CheckedProgram)
    (implementation : ProgramImplementationSignature) :
    IO TypedTraitResolution.Evidence := do
  match (TypedTraitResolution.resolve program.signatures.resolutionRules 32
      implementation.head).outcome with
  | .success evidence => pure evidence
  | outcome => throw (IO.userError
      s!"implementation evidence was unavailable: {reprStr outcome}")

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

private def stagedSource : String := String.intercalate "\n" [
  "trait Stage<T> {",
  "  function stage(comptime value: T) returns (comptime<T>);",
  "}",
  "impl Stage<Word> {",
  "  function stage(comptime value: Word) returns (comptime<Word>) {",
  "    return value;",
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

private def testComptimeMarkerValidation : IO Unit := do
  let program ← checkedProgramOf stagedSource
  let implementation ← onlyImplementation program
  let implementationMethod ← match implementation.methods with
    | [method] => pure method
    | methods => throw (IO.userError
        s!"expected one Stage implementation method, found {methods.length}")
  let trait ← match program.signatures.traits with
    | [trait] => pure trait
    | traits => throw (IO.userError
        s!"expected one Stage trait, found {traits.length}")
  let traitMethod ← match trait.methods with
    | [method] => pure method
    | methods => throw (IO.userError
        s!"expected one Stage trait method, found {methods.length}")
  let checked ← match ExecutableImplMethods.checkMethodWithArity program
      (evidenceFor implementation) 1 "stage" with
    | .ok checked => pure checked
    | .error error => throw (IO.userError
        s!"matching comptime method markers were rejected: {reprStr error}")
  assertTrue (decide (checked.traitMethod.parameterComptime = [true] ∧
      checked.traitMethod.returnComptime ∧
      checked.synthetic.parameterComptime = [true] ∧
      checked.synthetic.returnComptime))
    "executable method lost its validated comptime markers"
  let parameterTamperedMethod := {
    implementationMethod with
    parameters := implementationMethod.parameters.map fun parameter => {
      parameter with comptime := false
    }
  }
  let parameterTamperedImplementation := {
    implementation with methods := [parameterTamperedMethod]
  }
  let parameterTamperedProgram : CheckedProgram := {
    program with
    signatures := {
      program.signatures with
      implementations := [parameterTamperedImplementation]
    }
  }
  match ExecutableImplMethods.checkMethodWithArity parameterTamperedProgram
      (evidenceFor implementation) 1 "stage" with
  | .error (.methodComptimeMismatch method expectedTraitMethod
      [true] [false] true true) =>
      assertTrue (decide (method = implementationMethod.id ∧
          expectedTraitMethod = traitMethod.id))
        "parameter-marker rejection lost the method association"
  | .error error => throw (IO.userError
      s!"tampered parameter marker had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError
      "tampered implementation-method parameter marker was executable")
  let returnTamperedMethod := {
    implementationMethod with returnComptime := false
  }
  let returnTamperedImplementation := {
    implementation with methods := [returnTamperedMethod]
  }
  let returnTamperedProgram : CheckedProgram := {
    program with
    signatures := {
      program.signatures with implementations := [returnTamperedImplementation]
    }
  }
  match ExecutableImplMethods.checkMethodWithArity returnTamperedProgram
      (evidenceFor implementation) 1 "stage" with
  | .error (.methodComptimeMismatch method expectedTraitMethod
      [true] [true] true false) =>
      assertTrue (decide (method = implementationMethod.id ∧
          expectedTraitMethod = traitMethod.id))
        "return-marker rejection lost the method association"
  | .error error => throw (IO.userError
      s!"tampered return marker had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError
      "tampered implementation-method return marker was executable")

private def testMultiMethodSelection : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Add<T> {",
    "  function add(left: T, right: T) returns (T);",
    "  function tag(value: T) returns (Bool);",
    "}",
    "impl Add<Word> {",
    "  function add(left: Word, right: Word) returns (Word) { return left; }",
    "  function tag(value: Word) returns (Bool) { return true; }",
    "}"
  ])
  let implementation ← onlyImplementation program
  let evidence := evidenceFor implementation
  let add ← match ExecutableImplMethods.checkMethodWithArity program evidence
      1 "add" with
    | .ok method => pure method
    | .error error => throw (IO.userError
        s!"named add selection failed: {reprStr error}")
  let tag ← match ExecutableImplMethods.checkMethodWithArity program evidence
      1 "tag" with
    | .ok method => pure method
    | .error error => throw (IO.userError
        s!"named tag selection failed: {reprStr error}")
  assertTrue (decide (
      add.id.methodIndex = 0 ∧ add.traitMethod.id.methodIndex = 0 ∧
      add.synthetic.parameterTypes = [.word, .word] ∧
      add.synthetic.returnTypes = [.word] ∧
      tag.id.methodIndex = 1 ∧ tag.traitMethod.id.methodIndex = 1 ∧
      tag.synthetic.parameterTypes = [.word] ∧
      tag.synthetic.returnTypes = [.bool]))
    "multi-method selection lost the requested method identity or type"
  let implementationMethods ← match implementation.methods with
    | [addMethod, tagMethod] => pure (addMethod, tagMethod)
    | methods => throw (IO.userError
        s!"expected two implementation methods, found {methods.length}")
  let duplicatedImplementation := {
    implementation with
    methods := implementation.methods ++ [implementationMethods.1]
  }
  let duplicatedImplementationProgram : CheckedProgram := {
    program with
    signatures := {
      program.signatures with
      implementations := [duplicatedImplementation]
    }
  }
  match ExecutableImplMethods.checkMethodWithArity
      duplicatedImplementationProgram evidence 1 "add" with
  | .error (.multipleImplementationMethods id 2) =>
      assertTrue (decide (id = implementation.id))
        "duplicate named impl-method rejection named the wrong implementation"
  | .error error => throw (IO.userError
      s!"duplicate named impl methods had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError
      "duplicate implementation methods with one name were selected")
  let trait ← match program.signatures.traits with
    | [trait] => pure trait
    | traits => throw (IO.userError
        s!"expected one trait, found {traits.length}")
  let traitMethods ← match trait.methods with
    | [addMethod, tagMethod] => pure (addMethod, tagMethod)
    | methods => throw (IO.userError
        s!"expected two trait methods, found {methods.length}")
  let missingNamedTrait := { trait with methods := [traitMethods.2] }
  let missingNamedTraitProgram : CheckedProgram := {
    program with
    signatures := {
      program.signatures with
      traits := [missingNamedTrait]
    }
  }
  match ExecutableImplMethods.checkMethodWithArity missingNamedTraitProgram
      evidence 1 "add" with
  | .error (.missingTraitMethod id "add") =>
      assertTrue (decide (id = trait.id))
        "missing named trait-method rejection named the wrong trait"
  | .error error => throw (IO.userError
      s!"missing named trait method had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError
      "missing named trait method was selected")
  let duplicatedTrait := {
    trait with
    methods := trait.methods ++ [traitMethods.1]
  }
  let duplicatedTraitProgram : CheckedProgram := {
    program with
    signatures := {
      program.signatures with
      traits := [duplicatedTrait]
    }
  }
  match ExecutableImplMethods.checkMethodWithArity duplicatedTraitProgram
      evidence 1 "add" with
  | .error (.multipleTraitMethods id 2) =>
      assertTrue (decide (id = trait.id))
        "duplicate named trait-method rejection named the wrong trait"
  | .error error => throw (IO.userError
      s!"duplicate named trait methods had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError
      "duplicate trait methods with one name were selected")

private def testTraitPredicateInstantiation : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Eq<T> {}",
    "trait Ord<T> where T: Eq {",
    "  function gt(left: T, right: T) returns (Bool);",
    "}",
    "impl Eq<Word> {}",
    "impl Ord<Word> where Word: Eq {",
    "  function gt(left: Word, right: Word) returns (Bool) { return true; }",
    "}"
  ])
  let implementation ← implementationForTrait program "Ord"
  let evidence ← selectedEvidenceFor program implementation
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
      program evidence 1 "gt" with
    | .ok method => pure method
    | .error error => throw (IO.userError
        s!"trait-constrained Ord.gt method was rejected: {reprStr error}")
  assertTrue (decide (implementation.head.trait = ord.id ∧
      implementation.head.subject = .word ∧
      implementation.wherePredicates = [eqWord] ∧
      method.synthetic.scheme.parameters = [] ∧
      method.synthetic.scheme.predicates = [eqWord, eqWord] ∧
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
    "impl Rel<Word, Bool> {}",
    "impl Route<Word, Bool> where Word: Rel<Bool> {",
    "  function route(value: Word) returns (Bool) { return true; }",
    "}"
  ])
  let implementation ← implementationForTrait program "Route"
  let evidence ← selectedEvidenceFor program implementation
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
      program evidence 2 "route" with
    | .ok method => pure method
    | .error error => throw (IO.userError
        s!"two-parameter trait predicate was rejected: {reprStr error}")
  assertTrue (decide (implementation.head.subject = .word ∧
      implementation.head.arguments = [.bool] ∧
      method.synthetic.scheme.predicates = [relWordBool, relWordBool]))
    "trait subject and argument parameters were instantiated out of order"

private def testUnclosedTraitPredicateRejection : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Eq<T> {}",
    "trait Ord<T> where T: Eq {",
    "  function gt(left: T, right: T) returns (Bool);",
    "}",
    "impl Eq<Word> {}",
    "impl Ord<Word> where Word: Eq {",
    "  function gt(left: Word, right: Word) returns (Bool) { return true; }",
    "}"
  ])
  let implementation ← implementationForTrait program "Ord"
  let evidence ← selectedEvidenceFor program implementation
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
      tamperedProgram evidence 1 "gt" with
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
  | .error (.evidencePremiseCountMismatch id 0 1) =>
      assertTrue (decide (id = implementation.id))
        "unexpected-premise rejection named the wrong implementation"
  | .error error => throw (IO.userError
      s!"unexpected evidence premise had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError "an evidence premise without a predicate was executable")
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
  | .error (.missingImplementationMethod id "sum") =>
      assertTrue (decide (id = implementation.id))
        "missing named method rejection named the wrong implementation"
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

private def testAmbiguousEvidenceRejection : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Add<T> { function add(left: T, right: T) returns (T); }",
    "impl Add<Word> {",
    "  function add(left: Word, right: Word) returns (Word) { return left; }",
    "}",
    "impl Add<Word> {",
    "  function add(left: Word, right: Word) returns (Word) { return right; }",
    "}"
  ])
  let (first, second) ← match program.signatures.implementations with
    | [first, second] => pure (first, second)
    | implementations => throw (IO.userError
        s!"expected two overlapping implementations, found {implementations.length}")
  let forged : TypedTraitResolution.Evidence :=
    .byImpl first.head first.id []
  match ExecutableImplMethods.checkMethodWithArity program forged 1 "add" with
  | .error (.evidenceResolutionInconclusive
      (.ambiguous goal firstId secondId)) =>
      assertTrue (decide (goal = first.head ∧ firstId = first.id ∧
          secondId = second.id))
        "ambiguous evidence rejection lost its goal or implementation order"
  | .error error => throw (IO.userError
      s!"forged overlapping evidence had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError
      "forged evidence bypassed an ambiguous implementation catalog")

private def testGenericImplementationSpecialization : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Identity<T> { function identity(value: T) returns (T); }",
    "impl<T> Identity<T> {",
    "  function identity(value: T) returns (T) { return value; }",
    "}"
  ])
  let implementation ← onlyImplementation program
  let identity ← match program.signatures.traits.filter fun trait =>
      trait.name == "Identity" with
    | [trait] => pure trait
    | traits => throw (IO.userError
        s!"expected one Identity trait, found {traits.length}")
  let goal : ProgramPredicate := {
    trait := identity.id
    subject := .word
    arguments := []
  }
  let evidence ← match (TypedTraitResolution.resolve
      program.signatures.resolutionRules 32 goal).outcome with
    | .success evidence => pure evidence
    | outcome => throw (IO.userError
        s!"generic Identity<Word> did not resolve: {reprStr outcome}")
  let method ← match ExecutableImplMethods.checkMethodWithArity program evidence
      1 "identity" with
    | .ok method => pure method
    | .error error => throw (IO.userError
        s!"ground generic implementation was rejected: {reprStr error}")
  let parameter ← match implementation.parameters with
    | [parameter] => pure parameter
    | parameters => throw (IO.userError
        s!"expected one implementation parameter, found {parameters.length}")
  assertTrue (decide (
      method.specialized.parameterSubstitution = [(parameter, .word)] ∧
      method.specialized.key.declaration = implementation.id ∧
      method.specialized.key.arguments = [.word] ∧
      method.specialized.assumptions = [] ∧
      method.synthetic.scheme.parameters = [] ∧
      method.synthetic.parameterTypes = [.word] ∧
      method.synthetic.returnTypes = [.word] ∧
      method.checked.type = .function .word .word ∧
      method.checked.inferredBodyType = .word))
    "generic implementation did not close at its evidence goal"
  let elaborated ← match SourceCoreElaboration.elaborateFunction method.checked with
    | .ok elaborated => pure elaborated
    | .error error => throw (IO.userError
        s!"specialized generic Identity method did not lower: {reprStr error}")
  assertTrue (decide (elaborated.inputs.values = [.word] ∧
      elaborated.returnType = .word ∧
      Core.infer? elaborated.inputs.values elaborated.core = some .word))
    "specialized generic Identity method lost its closed Core type"

private def testUndeterminedImplementationParameterRejection : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Identity<T> { function identity(value: T) returns (T); }",
    "impl<T> Identity<T> {",
    "  function identity(value: T) returns (T) { return value; }",
    "}"
  ])
  let implementation ← onlyImplementation program
  let phantom : TypeSystem.TypeParameterId := {
    owner := implementation.id
    index := 1
  }
  let forgedImplementation := {
    implementation with
    parameters := implementation.parameters ++ [phantom]
  }
  let forgedProgram := {
    program with
    signatures := {
      program.signatures with
      implementations := [forgedImplementation]
    }
  }
  let identity ← match program.signatures.traits.filter fun trait =>
      trait.name == "Identity" with
    | [trait] => pure trait
    | traits => throw (IO.userError
        s!"expected one Identity trait, found {traits.length}")
  let goal : ProgramPredicate := {
    trait := identity.id
    subject := .word
    arguments := []
  }
  let evidence ← match (TypedTraitResolution.resolve
      program.signatures.resolutionRules 32 goal).outcome with
    | .success evidence => pure evidence
    | outcome => throw (IO.userError
        s!"phantom Identity<Word> head did not resolve: {reprStr outcome}")
  match ExecutableImplMethods.checkMethodWithArity forgedProgram evidence 1
      "identity" with
  | .error (.implementationParameterNotDetermined id parameter (.flexible _)) =>
      assertTrue (decide (id = implementation.id ∧ parameter = phantom))
        "undetermined-parameter rejection lost the implementation or phantom"
  | .error error => throw (IO.userError
      s!"phantom implementation had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError
      "an implementation parameter absent from its evidence was invented")

private def testImplementationPredicateEvidence : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Eq<T> {}",
    "trait Add<T> { function add(left: T, right: T) returns (T); }",
    "impl Eq<Word> {}",
    "impl Add<Word> where Word: Eq {",
    "  function add(left: Word, right: Word) returns (Word) { return left; }",
    "}"
  ])
  let add ← match program.signatures.traits.filter fun trait =>
      trait.name == "Add" with
    | [trait] => pure trait
    | traits => throw (IO.userError
        s!"expected one Add trait, found {traits.length}")
  let implementation ← match program.signatures.implementations.filter
      fun implementation =>
        implementation.head.trait == ProgramTraitId.declaration add.id with
    | [implementation] => pure implementation
    | implementations => throw (IO.userError
        s!"expected one Add implementation, found {implementations.length}")
  let evidence ← match (TypedTraitResolution.resolve
      program.signatures.resolutionRules 32 implementation.head).outcome with
    | .success evidence => pure evidence
    | outcome => throw (IO.userError
        s!"Add implementation evidence did not resolve: {reprStr outcome}")
  let method ← match ExecutableImplMethods.checkMonomorphicMethodWithArity
      program evidence 1 "add" with
    | .ok method => pure method
    | .error error => throw (IO.userError
        s!"closed implementation predicate was rejected: {reprStr error}")
  let premiseMatches := match implementation.wherePredicates,
      method.implementationPremises with
    | [expected], [.byImpl actual _ []] => expected == actual
    | _, _ => false
  assertTrue (premiseMatches && decide (
      method.traitPredicates = [] ∧
      method.implementationPredicates = implementation.wherePredicates ∧
      method.synthetic.scheme.predicates = implementation.wherePredicates ∧
      method.checked.solvedRequirements = []))
    "implementation premise was not retained in exact predicate order"
  match SourceCoreElaboration.elaborateFunction method.checked with
  | .ok _ => pure ()
  | .error error => throw (IO.userError
      s!"unused closed implementation premise blocked lowering: {reprStr error}")
  let expectedPremise ← match implementation.wherePredicates with
    | [predicate] => pure predicate
    | predicates => throw (IO.userError
        s!"expected one Add implementation predicate, found {predicates.length}")
  let wrongGoal := implementation.head
  let wrongEvidence : TypedTraitResolution.Evidence :=
    .byImpl implementation.head implementation.id [
      .byImpl wrongGoal implementation.id []
    ]
  match ExecutableImplMethods.checkMonomorphicMethodWithArity program
      wrongEvidence 1 "add" with
  | .error (.evidencePremiseGoalMismatch id 0 expected actual) =>
      assertTrue (decide (id = implementation.id ∧
          expected = expectedPremise ∧
          actual = wrongGoal))
        "premise-goal rejection lost its exact predicate position"
  | .error error => throw (IO.userError
      s!"wrong implementation premise had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError
      "mismatched implementation premise evidence was executable")

private def testMethodPredicateEvidence : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Eq<T> { function eq(left: T, right: T) returns (Bool); }",
    "trait Mark<T> {}",
    "trait Guard<T> {",
    "  function guard(value: T) returns (T) where T: Eq, T: Mark;",
    "}",
    "impl Eq<Word> {",
    "  function eq(left: Word, right: Word) returns (Bool) { return true; }",
    "}",
    "impl Mark<Word> {}",
    "impl<T> Guard<T> {",
    "  function guard(value: T) returns (T) where T: Eq, T: Mark {",
    "    value == value;",
    "    return value;",
    "  }",
    "}"
  ])
  let eq ← match program.signatures.traits.filter fun trait =>
      trait.name == "Eq" with
    | [trait] => pure trait
    | traits => throw (IO.userError
        s!"expected one Eq trait, found {traits.length}")
  let mark ← match program.signatures.traits.filter fun trait =>
      trait.name == "Mark" with
    | [trait] => pure trait
    | traits => throw (IO.userError
        s!"expected one Mark trait, found {traits.length}")
  let guard ← match program.signatures.traits.filter fun trait =>
      trait.name == "Guard" with
    | [trait] => pure trait
    | traits => throw (IO.userError
        s!"expected one Guard trait, found {traits.length}")
  let implementation ← match program.signatures.implementations.filter
      fun implementation =>
        implementation.head.trait == ProgramTraitId.declaration guard.id with
    | [implementation] => pure implementation
    | implementations => throw (IO.userError
        s!"expected one Guard implementation, found {implementations.length}")
  let implementationMethod ← match implementation.methods with
    | [method] => pure method
    | methods => throw (IO.userError
        s!"expected one Guard implementation method, found {methods.length}")
  let eqWord : ProgramPredicate := {
    trait := eq.id
    subject := .word
    arguments := []
  }
  let markWord : ProgramPredicate := {
    trait := mark.id
    subject := .word
    arguments := []
  }
  let guardWord : ProgramPredicate := {
    trait := guard.id
    subject := .word
    arguments := []
  }
  let primaryEvidence ← match (TypedTraitResolution.resolve
      program.signatures.resolutionRules 32 guardWord).outcome with
    | .success evidence => pure evidence
    | outcome => throw (IO.userError
        s!"Guard<Word> evidence did not resolve: {reprStr outcome}")
  let eqEvidence ← match (TypedTraitResolution.resolve
      program.signatures.resolutionRules 32 eqWord).outcome with
    | .success evidence => pure evidence
    | outcome => throw (IO.userError
        s!"Eq<Word> evidence did not resolve: {reprStr outcome}")
  let markEvidence ← match (TypedTraitResolution.resolve
      program.signatures.resolutionRules 32 markWord).outcome with
    | .success evidence => pure evidence
    | outcome => throw (IO.userError
        s!"Mark<Word> evidence did not resolve: {reprStr outcome}")
  let method ← match
      ExecutableImplMethods.checkMethodWithEvidenceAndArity program
        primaryEvidence [eqEvidence, markEvidence] 1 "guard" with
    | .ok method => pure method
    | .error error => throw (IO.userError
        s!"caller-owned method evidence was rejected: {reprStr error}")
  let methodEvidenceMatches := match method.methodPremises with
    | [first, second] => first == eqEvidence && second == markEvidence
    | _ => false
  assertTrue (methodEvidenceMatches && decide (
      method.methodPredicates = [eqWord, markWord] ∧
      method.traitPredicates = [] ∧
      method.implementationPredicates = [] ∧
      method.synthetic.scheme.predicates = [eqWord, markWord] ∧
      method.specialized.assumptions = [eqWord, markWord] ∧
      method.synthetic.parameterTypes = [.word] ∧
      method.synthetic.returnTypes = [.word] ∧
      method.checked.solvedRequirements.map (·.predicate) = [eqWord]))
    "method predicates or their caller-owned evidence lost source order"
  match ExecutableImplMethods.checkMethodWithArity program primaryEvidence
      1 "guard" with
  | .error (.methodEvidenceCountMismatch id 2 0) =>
      assertTrue (decide (id = implementationMethod.id))
        "compatibility-entry rejection named the wrong implementation method"
  | .error error => throw (IO.userError
      s!"missing method evidence had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError
      "the empty-evidence compatibility entry discharged method predicates")
  match ExecutableImplMethods.checkMethodWithEvidenceAndArity program
      primaryEvidence [eqEvidence] 1 "guard" with
  | .error (.methodEvidenceCountMismatch id 2 1) =>
      assertTrue (decide (id = implementationMethod.id))
        "method-evidence count rejection named the wrong method"
  | .error error => throw (IO.userError
      s!"short method evidence had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError "short method evidence was accepted")
  match ExecutableImplMethods.checkMethodWithEvidenceAndArity program
      primaryEvidence [markEvidence, eqEvidence] 1 "guard" with
  | .error (.methodEvidenceGoalMismatch id 0 expected actual) =>
      assertTrue (decide (id = implementationMethod.id ∧ expected = eqWord ∧
          actual = markWord))
        "method-evidence order rejection lost its first expected goal"
  | .error error => throw (IO.userError
      s!"reordered method evidence had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError "reordered method evidence was accepted")
  let forgedEqEvidence : TypedTraitResolution.Evidence :=
    .byImpl eqWord implementation.id []
  match ExecutableImplMethods.checkMethodWithEvidenceAndArity program
      primaryEvidence [forgedEqEvidence, markEvidence] 1 "guard" with
  | .error (.methodEvidenceNotSelected id 0 goal) =>
      assertTrue (decide (id = implementationMethod.id ∧ goal = eqWord))
        "noncanonical method-evidence rejection lost its method or goal"
  | .error error => throw (IO.userError
      s!"forged method evidence had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError "forged method evidence was accepted")
  let reversedImplementation : ProgramImplementationSignature := {
    implementation with
    methods := implementation.methods.map fun method => {
      method with wherePredicates := method.wherePredicates.reverse
    }
  }
  let reversedProgram : CheckedProgram := {
    program with
    signatures := {
      program.signatures with
      implementations := program.signatures.implementations.map fun candidate =>
        if candidate.id = implementation.id then reversedImplementation
        else candidate
    }
  }
  match ExecutableImplMethods.checkMethodWithEvidenceAndArity reversedProgram
      primaryEvidence [eqEvidence, markEvidence] 1 "guard" with
  | .error (.methodPredicateMismatch id traitMethod expected actual) =>
      assertTrue (decide (id = implementationMethod.id ∧
          traitMethod = implementationMethod.traitMethod ∧
          expected = implementationMethod.wherePredicates ∧
          actual = implementationMethod.wherePredicates.reverse))
        "generic method-predicate mismatch lost its ordered catalogs"
  | .error error => throw (IO.userError
      s!"tampered generic method predicates had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError
      "tampered generic method predicates were executable")
  let foreignParameter : TypeSystem.TypeParameterId := {
    owner := guard.id
    index := guard.parameters.length + 11
  }
  let openPredicate := { eqWord with subject := .parameter foreignParameter }
  let openTraitMethod ← match guard.methods with
    | [method] => pure { method with wherePredicates := [openPredicate] }
    | methods => throw (IO.userError
        s!"expected one Guard trait method, found {methods.length}")
  let openImplementationMethod := {
    implementationMethod with wherePredicates := [openPredicate]
  }
  let openGuard := { guard with methods := [openTraitMethod] }
  let openImplementation := {
    implementation with methods := [openImplementationMethod]
  }
  let openProgram : CheckedProgram := {
    program with
    signatures := {
      program.signatures with
      traits := program.signatures.traits.map fun candidate =>
        if candidate.id = guard.id then openGuard else candidate
      implementations := program.signatures.implementations.map fun candidate =>
        if candidate.id = implementation.id then openImplementation else candidate
    }
  }
  match ExecutableImplMethods.checkMethodWithEvidenceAndArity openProgram
      primaryEvidence [eqEvidence] 1 "guard" with
  | .error (.methodPredicateNotClosed id predicate (.rigid parameter)) =>
      assertTrue (decide (id = implementationMethod.id ∧
          predicate = openPredicate ∧ parameter = foreignParameter))
        "open method-predicate rejection lost its method or rigid parameter"
  | .error error => throw (IO.userError
      s!"open method predicate had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError "an open method predicate was executable")

private def testBodyIsActuallyChecked : IO Unit := do
  let raw := singleSourceWorkspace (String.intercalate "\n" [
    "trait Add<T> { function add(left: T, right: T) returns (T); }",
    "impl Add<Word> {",
    "  function add(left: Word, right: Word) returns (Word) {",
    "    return missing;",
    "  }",
    "}"
  ])
  let loaded ← match loadProgram raw with
    | .ok loaded => pure loaded
    | .error errors => throw (IO.userError
        s!"invalid-method defense fixture failed loading: {reprStr errors}")
  let signatures ← match buildProgramSignatures loaded.environment with
    | .ok signatures => pure signatures
    | .error errors => throw (IO.userError
        s!"invalid-method defense fixture failed cataloging: {reprStr errors}")
  /- `checkProgram` now rejects this body eagerly.  Forge the public carrier
  from the independently loaded catalog to retain the executable boundary's
  defense-in-depth regression. -/
  let program : CheckedProgram := {
    environment := loaded.environment
    signatures
    functions := []
  }
  let implementation ← onlyImplementation program
  match ExecutableImplMethods.checkMonomorphicPremiseFreeMethodWithArity program
      (evidenceFor implementation) 1 "add" with
  | .error (.sourceInference (.unknownVariable "missing")) => pure ()
  | .error error => throw (IO.userError
      s!"invalid method body had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError
      "invalid implementation method body bypassed source checking")

private def testBuiltinIdentityRejection : IO Unit := do
  let program ← checkedProgramOf successSource
  let implementation ← onlyImplementation program
  let builtinImplementationEvidence : TypedTraitResolution.Evidence :=
    .byImpl implementation.head (.builtin .intWord) []
  match ExecutableImplMethods.checkMethodWithArity program
      builtinImplementationEvidence 1 "add" with
  | .error (.builtinImplementationNotExecutable .intWord) => pure ()
  | .error error => throw (IO.userError
      s!"builtin implementation had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError
      "a builtin implementation entered the source method catalog")
  let builtinGoal : ProgramPredicate := {
    implementation.head with trait := .builtin .int
  }
  let builtinTraitEvidence : TypedTraitResolution.Evidence :=
    .byImpl builtinGoal implementation.id []
  match ExecutableImplMethods.checkMethodWithArity program
      builtinTraitEvidence 1 "add" with
  | .error (.builtinTraitNotExecutable .int) => pure ()
  | .error error => throw (IO.userError
      s!"builtin trait had the wrong rejection: {reprStr error}")
  | .ok _ => throw (IO.userError
      "a builtin trait entered the source trait catalog")

/-- Exercise executable method selection, body checking, Core lowering, and
the first profile's explicit staged boundaries. -/
def testExecutableImplMethods : IO Unit := do
  testSuccessfulMethodCheck
  testTwoParameterTraitMethodCheck
  testComptimeMarkerValidation
  testMultiMethodSelection
  testTraitPredicateInstantiation
  testTraitPredicateParameterOrder
  testUnclosedTraitPredicateRejection
  testEmptyMarkerRejection
  testDefensiveProfileRejections
  testAmbiguousEvidenceRejection
  testGenericImplementationSpecialization
  testUndeterminedImplementationParameterRejection
  testImplementationPredicateEvidence
  testMethodPredicateEvidence
  testBodyIsActuallyChecked
  testBuiltinIdentityRejection

end Tests.ExecutableImplMethods
end

section
-- leanmerge: from Solcore.Test.ProgramChecking
/-! End-to-end executable whole-program checking regressions. -/

set_option autoImplicit false

namespace Tests.ProgramChecking

open Solcore Solcore.Frontend

example
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : SourceInference.CheckedFunction}
    (success : SourceInference.checkFunctionBody environment signatures signature
      fuel = .ok checked) :
    checked.declaration = signature.id :=
  SourceInference.checkFunctionBody_success_declaration success

example
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : SourceInference.CheckedFunction}
    (success : SourceInference.checkFunctionBody environment signatures signature
      fuel = .ok checked) :
    ∃ declaration body finalState result,
      environment.declaration? signature.id = some declaration ∧
        SourceInference.Detail.inferStatementsFuel fuel
            {
              environment
              signatures
              scope := .ofDeclaration declaration
              typeParameters := signature.scheme.parameters
              assumptions := signature.scheme.predicates
            }
            signature.source.value.body.value
            (TypeSystem.Ty.productMany signature.returnTypes)
            (SourceInference.State.initial declaration.id
              ((signature.parameterNames.zip signature.parameterTypes).map
                fun parameter =>
                  (parameter.1, TypeSystem.Scheme.mono parameter.2))
              signature.parameterComptime) = .ok body ∧
          SourceInference.Detail.unify body.state body.type
              (TypeSystem.Ty.productMany signature.returnTypes) =
            .ok finalState ∧
            SourceInference.Detail.finalize
                {
                  environment
                  signatures
                  scope := .ofDeclaration declaration
                  typeParameters := signature.scheme.parameters
                  assumptions := signature.scheme.predicates
                }
                (TypeSystem.Ty.productMany signature.returnTypes) finalState
                (body.statements.map SourceInference.NodeId.statement) =
              .ok result ∧
              checked.inferredBodyType = result.type := by
  obtain ⟨declaration, body, finalState, result, declarationEq, bodyEq,
    unifyEq, finalizeEq, checkedEq⟩ :=
    SourceInference.checkFunctionBody_success_witness success
  refine ⟨declaration, body, finalState, result, declarationEq, bodyEq,
    unifyEq, finalizeEq, ?_⟩
  simp [checkedEq]

example
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {fuel : Nat}
    {functions : List SourceInference.CheckedFunction}
    (success : SourceInference.checkFunctionBodies environment signatures fuel =
      .ok functions) :
    functions.map (fun function => function.declaration) =
      signatures.functions.map (fun signature => signature.id) :=
  SourceInference.checkFunctionBodies_success_declaration_ids success

example
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {fuel : Nat}
    {methods : List CheckedImplementationMethod}
    (success : checkImplementationMethodBodies environment signatures fuel =
      .ok methods) :
    methods.map (fun method => method.id) =
      signatures.implementations.flatMap fun implementation =>
        implementation.methods.map (fun method => method.id) :=
  checkImplementationMethodBodies_success_ids success

example
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkLoadedProgram loaded fuel = .ok checked) :
    checked.functions.map (fun function => function.declaration) =
        checked.signatures.functions.map (fun signature => signature.id) ∧
      checked.methods.map (fun method => method.id) =
        checked.signatures.implementations.flatMap fun implementation =>
          implementation.methods.map (fun method => method.id) :=
  checkLoadedProgram_success_ids success

example
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkLoadedProgram loaded fuel = .ok checked) :
    checked.environment = loaded.environment :=
  checkLoadedProgram_success_environment success

example
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkLoadedProgram loaded fuel = .ok checked) :
    buildProgramSignatures loaded.environment = .ok checked.signatures :=
  checkLoadedProgram_success_signatures success

example
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkLoadedProgram loaded fuel = .ok checked) :
    ProgramSignatureFormationValidated checked.signatures :=
  checkLoadedProgram_success_signature_formation success

example
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkLoadedProgram loaded fuel = .ok checked) :
    ProgramSignatureParametersWellFormed checked.signatures :=
  checkLoadedProgram_success_signature_parameters_wellFormed success

example
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkProgram raw fuel = .ok checked) :
    checked.functions.map (fun function => function.declaration) =
        checked.signatures.functions.map (fun signature => signature.id) ∧
      checked.methods.map (fun method => method.id) =
        checked.signatures.implementations.flatMap fun implementation =>
          implementation.methods.map (fun method => method.id) :=
  checkProgram_success_ids success

example
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkProgram raw fuel = .ok checked) :
    ∃ loaded,
      loadProgram raw = .ok loaded ∧
        checkLoadedProgram loaded fuel = .ok checked :=
  checkProgram_success_load success

example
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkProgram raw fuel = .ok checked) :
    (checked.environment.declarations.map (·.id)).Nodup :=
  checkProgram_success_declarations_nodup success

example
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkProgram raw fuel = .ok checked) :
    ((checked.signatures.functions.map fun signature => signature.id) ++
      (checked.signatures.dataTypes.map fun signature => signature.id) ++
      (checked.signatures.traits.map fun signature => signature.id) ++
      (checked.signatures.implementations.map fun signature => signature.id) ++
      (checked.signatures.contracts.map fun signature => signature.id)).Nodup :=
  checkProgram_success_signature_declaration_ids_nodup success

example
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkProgram raw fuel = .ok checked) :
    ProgramSignatureParametersWellFormed checked.signatures :=
  checkProgram_success_signature_parameters_wellFormed success

example
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkProgram raw fuel = .ok checked) :
    ProgramSignatureFormationValidated checked.signatures :=
  checkProgram_success_signature_formation success

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def successfulWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [
    {
      path := "traits.solc"
      content := String.intercalate "\n" [
        "export {Eq};",
        "trait Eq<T> {}",
        "impl Eq<Word> {}"
      ]
    },
    {
      path := "functions.solc"
      content := String.intercalate "\n" [
        "import {Eq} from traits;",
        "export {keep, choose};",
        "function keep<T>(value: T) returns (T) where T: Eq { return value; }",
        "function choose(value: Bool) returns (Bool) { return value; }",
        "function choose(value: Word) returns (Word) { return value + 1; }"
      ]
    },
    {
      path := "main.solc"
      content := String.intercalate "\n" [
        "import {keep, choose} from functions;",
        "function run() returns (Word) { return choose(keep(41)); }"
      ]
    }
  ]
  externalLibraries := []
}

private def testSuccessfulProgram : IO Unit := do
  let checked ← match checkProgram successfulWorkspace with
    | .ok checked => pure checked
    | .error errors => throw (IO.userError
        s!"whole-program success fixture failed: {reprStr errors}")
  assertTrue (decide (checked.environment.modules.length = 3 ∧
      checked.signatures.functions.length = 4 ∧
      checked.signatures.implRules.length = 1 ∧
      checked.functions.length = 4 ∧ checked.methods.isEmpty))
    "whole-program summary omitted modules, overloads, impls, or bodies"
  assertTrue (decide (checked.functions.map (·.declaration) =
      checked.signatures.functions.map (·.id)))
    "checked functions did not preserve declaration order"
  let paired := checked.signatures.functions.zip checked.functions
  match paired.find? fun pair => pair.1.name == "run" with
  | none => throw (IO.userError "checked run function was not retained")
  | some (_, function) =>
      let equality ← match checked.environment.traitsNamed "Eq" with
        | [declaration] => pure declaration.id
        | declarations => throw (IO.userError
            s!"expected one Eq trait, found {declarations.length}")
      let equalityPredicate : ProgramPredicate := {
        trait := equality
        subject := .word
        arguments := []
      }
      let integerPredicate :=
        ProgramSignatures.builtinIntPredicate TypeSystem.Ty.word
      assertTrue (decide (function.inferredBodyType = TypeSystem.Ty.word))
        "overload selection or integer-literal resolution changed run's type"
      assertTrue (function.solvedRequirements.any fun solved =>
          solved.predicate == equalityPredicate &&
            match solved.evidence with
            | .implementation
                (.byImpl goal (.declaration _) premises) =>
                goal == equalityPredicate && premises.isEmpty
            | _ => false)
        "generic where predicate did not retain implementation evidence"
      assertTrue (function.solvedRequirements.any fun solved =>
          solved.predicate == integerPredicate &&
            match solved.evidence with
            | .implementation (.byImpl goal (.builtin .intWord) premises) =>
                goal == integerPredicate && premises.isEmpty
            | _ => false)
        "nested literal did not retain builtin Int<Word> evidence"

private def testSignatureFormationRejectsFlexibleReturn : IO Unit := do
  let checked ← match checkProgram successfulWorkspace with
    | .ok checked => pure checked
    | .error errors => throw (IO.userError
        s!"formation rejection fixture failed before mutation: {reprStr errors}")
  match checked.signatures.functions with
  | [] => throw (IO.userError "formation rejection fixture lost its function")
  | signature :: rest =>
      let malformedFunction := {
        signature with
        returnTypes := [.variable ⟨0⟩]
      }
      let malformed := {
        checked.signatures with
        functions := malformedFunction :: rest
      }
      match validateProgramSignatureFormation malformed with
      | .error [.flexibleVariable owner metavariable] =>
          assertTrue (decide (owner = signature.id ∧ metavariable.index = 0))
            "formation rejection lost its declaration or metavariable identity"
      | .error errors => throw (IO.userError
          s!"flexible signature type had the wrong error: {reprStr errors}")
      | .ok () => throw (IO.userError
          "flexible type in a resolved signature was accepted")

private def importedTypeWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [
    {
      path := "models.solc"
      content := "export {*}; enum Box { Only }"
    },
    {
      path := "main.solc"
      content := String.intercalate "\n" [
        "import * from models;",
        "function echo(value: Box) returns (Box) { return value; }"
      ]
    }
  ]
  externalLibraries := []
}

private def testImportedTypeProgram : IO Unit := do
  let checked ← match checkProgram importedTypeWorkspace with
    | .ok checked => pure checked
    | .error errors => throw (IO.userError
        s!"imported whole-program fixture failed: {reprStr errors}")
  match checked.signatures.functions with
  | [signature] =>
      assertTrue (decide (signature.parameterTypes = signature.returnTypes))
        "imported type resolved inconsistently across a function signature"
  | _ => throw (IO.userError "imported fixture lost its function signature")

private def unsolvedTraitWorkspace : Workspace.RawWorkspace := {
  entry := "broken.solc"
  mainSources := [{
    path := "broken.solc"
    content := String.intercalate "\n" [
      "trait Add<T> {",
      "  function add(left: T, right: T) returns (T);",
      "}",
      "enum Box { Only }",
      "function broken(value: Box) returns (Box) { return value + value; }"
    ]
  }]
  externalLibraries := []
}

private def testNoSolution : IO Unit := do
  match checkProgram unsolvedTraitWorkspace with
  | .error [.noSolution _ predicate] =>
      assertTrue (predicate.arguments.isEmpty)
        "unary operator-trait goal unexpectedly acquired arguments"
  | .error errors => throw (IO.userError
      s!"missing implementation had the wrong failure class: {reprStr errors}")
  | .ok _ => throw (IO.userError "missing Add implementation was accepted")

private def inconclusiveTraitWorkspace : Workspace.RawWorkspace := {
  entry := "ambiguous.solc"
  mainSources := [{
    path := "ambiguous.solc"
    content := String.intercalate "\n" [
      "trait Add<T> {",
      "  function add(left: T, right: T) returns (T);",
      "}",
      "enum Box { Only }",
      "impl Add<Box> {",
      "  function add(left: Box, right: Box) returns (Box) { return left; }",
      "}",
      "impl Add<Box> {",
      "  function add(left: Box, right: Box) returns (Box) { return right; }",
      "}",
      "function ambiguous(value: Box) returns (Box) { return value + value; }"
    ]
  }]
  externalLibraries := []
}

private def testInconclusive : IO Unit := do
  match checkProgram inconclusiveTraitWorkspace with
  | .error [.inconclusive _ (.ambiguous _ _ _)] => pure ()
  | .error errors => throw (IO.userError
      s!"overlapping impls had the wrong failure class: {reprStr errors}")
  | .ok _ => throw (IO.userError "overlapping Add implementations were selected")

private def defaultImplementationWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{
    path := "main.solc"
    content := String.intercalate "\n" [
      "trait Ready<T> {}",
      "trait Select<T> {}",
      "default impl<T> Select<T> {}",
      "impl Select<Word> {}",
      "impl Select<Bool> where Bool: Ready {}",
      "function select<T>(value: T) returns (T) where T: Select { return value; }",
      "function selectWord(value: Word) returns (Word) { return select(value); }",
      "function selectBool(value: Bool) returns (Bool) { return select(value); }"
    ]
  }]
  externalLibraries := []
}

private def testDefaultImplementationPriority : IO Unit := do
  let checked ← match checkProgram defaultImplementationWorkspace with
    | .ok checked => pure checked
    | .error errors => throw (IO.userError
        s!"default implementation program failed: {reprStr errors}")
  let fallback ← match checked.signatures.implementations.find? fun implementation =>
      implementation.isDefault with
    | some implementation => pure implementation
    | none => throw (IO.userError "default implementation was not retained")
  let wordSpecific ← match checked.signatures.implementations.find? fun implementation =>
      !implementation.isDefault && implementation.head.subject == .word with
    | some implementation => pure implementation
    | none => throw (IO.userError "specific Word implementation was not retained")
  let failedBoolSpecific ← match checked.signatures.implementations.find?
      fun implementation =>
        !implementation.isDefault && implementation.head.subject == .bool with
    | some implementation => pure implementation
    | none => throw (IO.userError "conditional Bool implementation was not retained")
  let checkedNamed (name : String) := checked.functions.find? fun function =>
    match checked.environment.declaration? function.declaration with
    | some declaration => declaration.name == some name
    | none => false
  let wordFunction ← match checkedNamed "selectWord" with
    | some function => pure function
    | none => throw (IO.userError "selectWord was not checked")
  let boolFunction ← match checkedNamed "selectBool" with
    | some function => pure function
    | none => throw (IO.userError "selectBool was not checked")
  match wordFunction.solvedRequirements with
  | [{ evidence := .implementation
        (.byImpl _ (.declaration implementation) []), .. }] =>
      assertTrue (decide (implementation = wordSpecific.id))
        "a matching default implementation displaced the ordinary Word implementation"
  | requirements => throw (IO.userError
      s!"selectWord evidence changed: {reprStr requirements}")
  match boolFunction.solvedRequirements with
  | [{ evidence := .implementation
        (.byImpl _ (.declaration implementation) []), .. }] =>
      assertTrue (decide (implementation = fallback.id ∧
          implementation ≠ failedBoolSpecific.id))
        "default implementation was not selected after the ordinary candidate failed"
  | requirements => throw (IO.userError
      s!"selectBool evidence changed: {reprStr requirements}")

private def singleSourceWorkspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def testStageClassification : IO Unit := do
  let missingEntry := {
    singleSourceWorkspace "function ok() { return; }" with
    entry := "missing.solc"
  }
  match checkProgram missingEntry with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .loading _ => true
        | _ => false) "workspace failure was not classified as loading"
  | .ok _ => throw (IO.userError "missing entry reached source inference")
  match checkProgram (singleSourceWorkspace
      "function bad(value: Missing) { return; }") with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .signature _ => true
        | _ => false) "type-name failure was not classified as signature"
  | .ok _ => throw (IO.userError "unknown signature type was accepted")
  match checkProgram (singleSourceWorkspace
      "function bad() returns (Word) { return missing; }") with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .inference _ => true
        | _ => false) "ordinary body failure was not classified as inference"
  | .ok _ => throw (IO.userError "unknown body variable was accepted")

private def testPhantomImplementationParameterRejection : IO Unit := do
  match checkProgram (singleSourceWorkspace (String.intercalate "\n" [
      "trait Identity<T> {}",
      "impl<T, U> Identity<T> {}"
    ])) with
  | .error [.signature
        (.implementationParameterNotInHead implementation parameter)] =>
      assertTrue (decide (parameter.owner = implementation ∧ parameter.index = 1))
        "phantom-parameter rejection lost its stable implementation identity"
  | .error errors => throw (IO.userError
      s!"phantom implementation had the wrong pipeline error: {reprStr errors}")
  | .ok _ => throw (IO.userError
      "a phantom implementation parameter reached body checking")

private def testMissingImplementationTraitPredicateRejection : IO Unit := do
  match checkProgram (singleSourceWorkspace (String.intercalate "\n" [
      "trait Marker<T> {}",
      "trait Required<T> where T: Marker {}",
      "impl Required<Word> {}"
    ])) with
  | .error [.signature
        (.missingImplementationTraitPredicate implementation predicate)] =>
      match predicate.trait with
      | .declaration trait =>
          assertTrue (decide (
              implementation.declarationIndex = 2 ∧
              trait.declarationIndex = 0 ∧
              trait.moduleId = implementation.moduleId ∧
              predicate.subject = .word ∧ predicate.arguments = []))
            "missing trait predicate lost its instantiated stable identities"
      | .builtin _ => throw (IO.userError
          "source trait requirement was reported as a builtin predicate")
  | .error errors => throw (IO.userError
      s!"missing trait predicate had the wrong pipeline error: {reprStr errors}")
  | .ok _ => throw (IO.userError
      "an implementation missing a trait-level requirement reached body checking")

private def checkedMethodWorkspace : Workspace.RawWorkspace :=
  singleSourceWorkspace (String.intercalate "\n" [
    "trait TraitProof<T> {}",
    "trait ImplProof<T> {}",
    "trait MethodProof<T> {}",
    "trait Transform<T> where T: TraitProof {",
    "  function first(value: T) returns (T) where T: MethodProof;",
    "  function second(value: T) returns (T);",
    "}",
    "function useTrait<T>(value: T) returns (T) where T: TraitProof {",
    "  return value;",
    "}",
    "function useImpl<T>(value: T) returns (T) where T: ImplProof {",
    "  return value;",
    "}",
    "function useMethod<T>(value: T) returns (T) where T: MethodProof {",
    "  return value;",
    "}",
    "impl<T> Transform<T> where T: TraitProof, T: ImplProof {",
    "  function first(value: T) returns (T) where T: MethodProof {",
    "    return useMethod(useImpl(useTrait(value)));",
    "  }",
    "  function second(value: T) returns (T) {",
    "    return useImpl(useTrait(value));",
    "  }",
    "}"
  ])

private def testImplementationMethodsCheckedInSourceOrder : IO Unit := do
  let checked ← match checkProgram checkedMethodWorkspace with
    | .ok checked => pure checked
    | .error errors => throw (IO.userError
        s!"generic implementation methods failed eager checking: {reprStr errors}")
  let implementation ← match checked.signatures.implementations with
    | [implementation] => pure implementation
    | implementations => throw (IO.userError
        s!"expected one Transform implementation, found {implementations.length}")
  let trait ← match checked.signatures.traits.filter fun trait =>
      trait.name == "Transform" with
    | [trait] => pure trait
    | traits => throw (IO.userError
        s!"expected one Transform trait, found {traits.length}")
  let first ← match implementation.methods with
    | first :: _ => pure first
    | [] => throw (IO.userError "Transform implementation lost its methods")
  let synthetic := implementation.functionSignatureOfMethodWithTrait trait first
  let traitSubstitution : TypeSystem.ParameterSubstitution :=
    trait.parameters.zip
      (implementation.head.subject :: implementation.head.arguments)
  let traitPredicates := trait.wherePredicates.map
    (ProgramPredicate.applyParameters traitSubstitution)
  let expectedAssumptions := traitPredicates ++
    implementation.wherePredicates ++ first.wherePredicates
  assertTrue (decide (synthetic.scheme.predicates = expectedAssumptions ∧
      synthetic.scheme.predicates.length = 4 ∧
      synthetic.scheme.predicates[0]? = synthetic.scheme.predicates[1]?))
    "synthetic method assumptions diverged from source-semantics order"
  let expectedIds := checked.signatures.implementations.flatMap
    fun candidate => candidate.methods.map (fun method => method.id)
  assertTrue (decide (checked.methods.map (fun method => method.id) = expectedIds ∧
      checked.methods.length = 2 ∧
      checked.methods.map (fun method => method.checked.declaration) =
        [implementation.id, implementation.id] ∧
      checked.methods.map (fun method => method.id.methodIndex) = [0, 1]))
    "eager method checking lost implementation or method source order"
  let firstChecked ← match checked.methods with
    | firstChecked :: _ => pure firstChecked
    | [] => throw (IO.userError "checked method catalog was empty")
  let solvedPredicates := firstChecked.checked.solvedRequirements.map
    (fun requirement => requirement.predicate)
  let assumptionsOnly := firstChecked.checked.solvedRequirements.all
    fun requirement => match requirement.evidence with
      | .assumption _ => true
      | .implementation _ => false
  assertTrue (assumptionsOnly &&
      expectedAssumptions.all fun predicate => solvedPredicates.contains predicate)
    "trait-, implementation-, or method-level assumptions were unavailable"

private def testFunctionAndMethodErrorsAccumulate : IO Unit := do
  match checkProgram (singleSourceWorkspace (String.intercalate "\n" [
      "trait Broken<T> {",
      "  function first(value: T) returns (T);",
      "  function second(value: T) returns (T);",
      "}",
      "impl Broken<Word> {",
      "  function first(value: Word) returns (Word) { return missingFirst; }",
      "  function second(value: Word) returns (Word) { return missingSecond; }",
      "}",
      "function bad() returns (Word) { return missingTop; }"
    ])) with
  | .error [
      .inference {
        declaration := functionId
        error := .unknownVariable "missingTop"
      },
      .methodInference firstId (.unknownVariable "missingFirst"),
      .methodInference secondId (.unknownVariable "missingSecond")
    ] =>
      assertTrue (decide (functionId.declarationIndex = 2 ∧
          firstId.implementation.declarationIndex = 1 ∧
          secondId.implementation = firstId.implementation ∧
          firstId.methodIndex = 0 ∧ secondId.methodIndex = 1))
        "combined body errors lost function-first or method source order"
  | .error errors => throw (IO.userError
      s!"combined function/method failures changed: {reprStr errors}")
  | .ok _ => throw (IO.userError
      "invalid function and implementation methods passed eager checking")

private def testMethodNoSolution : IO Unit := do
  match checkProgram (singleSourceWorkspace (String.intercalate "\n" [
      "trait Add<T> {",
      "  function add(left: T, right: T) returns (T);",
      "}",
      "trait Use<T> {",
      "  function use(left: T, right: T) returns (T);",
      "}",
      "enum Box { Only }",
      "impl Use<Box> {",
      "  function use(left: Box, right: Box) returns (Box) {",
      "    return left + right;",
      "  }",
      "}"
    ])) with
  | .error [.methodNoSolution method predicate] =>
      match predicate.trait with
      | .declaration trait =>
          assertTrue (decide (method.implementation.declarationIndex = 3 ∧
              method.methodIndex = 0 ∧ trait.declarationIndex = 0 ∧
              predicate.arguments.isEmpty))
            "method no-solution lost its stable method or trait goal"
      | .builtin _ => throw (IO.userError
          "source Add method failure was reported for a builtin trait")
  | .error errors => throw (IO.userError
      s!"method no-solution had the wrong classification: {reprStr errors}")
  | .ok _ => throw (IO.userError
      "implementation method with missing Add evidence was accepted")

private def testMethodInconclusive : IO Unit := do
  match checkProgram (singleSourceWorkspace (String.intercalate "\n" [
      "trait Add<T> {",
      "  function add(left: T, right: T) returns (T);",
      "}",
      "trait Use<T> {",
      "  function use(left: T, right: T) returns (T);",
      "}",
      "enum Box { Only }",
      "impl Add<Box> {",
      "  function add(left: Box, right: Box) returns (Box) { return left; }",
      "}",
      "impl Add<Box> {",
      "  function add(left: Box, right: Box) returns (Box) { return right; }",
      "}",
      "impl Use<Box> {",
      "  function use(left: Box, right: Box) returns (Box) {",
      "    return left + right;",
      "  }",
      "}"
    ])) with
  | .error [.methodInconclusive method (.ambiguous _ _ _)] =>
      assertTrue (decide (method.implementation.declarationIndex = 5 ∧
          method.methodIndex = 0))
        "inconclusive method search lost the selected method identity"
  | .error errors => throw (IO.userError
      s!"ambiguous method obligation had the wrong classification: {reprStr errors}")
  | .ok _ => throw (IO.userError
      "ambiguous method trait obligation was selected")

/-- Exercise the complete raw-workspace pipeline, including generics,
overloads, calls, predicates, implementation evidence, and integer literals. -/
def testProgramChecking : IO Unit := do
  testSuccessfulProgram
  testSignatureFormationRejectsFlexibleReturn
  testImportedTypeProgram
  testNoSolution
  testInconclusive
  testDefaultImplementationPriority
  testStageClassification
  testPhantomImplementationParameterRejection
  testMissingImplementationTraitPredicateRejection
  testImplementationMethodsCheckedInSourceOrder
  testFunctionAndMethodErrorsAccumulate
  testMethodNoSolution
  testMethodInconclusive

end Tests.ProgramChecking
end

section
-- leanmerge: from Solcore.Test.ProgramEnvironmentAndTypeResolution
/-! Executable multi-file declaration and type-resolution smoke tests. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

namespace ProgramEnvironmentAndTypeResolution

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do
    throw (IO.userError label)

private def parsed (origin : Syntax.SourceOrigin) (path content : String) :
    IO Syntax.ParsedFile := do
  let file : Syntax.SourceFile := { id := { origin, path }, content }
  match Syntax.Parser.parse file with
  | .error error =>
      throw (IO.userError s!"{path}: parser invariant: {reprStr error}")
  | .ok output =>
      unless output.lexicalDiagnostics.isEmpty &&
          output.parseDiagnostics.isEmpty do
        throw (IO.userError
          s!"{path}: source diagnostics: {reprStr output.lexicalDiagnostics}; {reprStr output.parseDiagnostics}")
      pure output.parsed

private def build (sources : List Syntax.ParsedFile) : IO ProgramEnvironment := do
  match buildProgramEnvironment sources with
  | .ok environment => pure environment
  | .error errors =>
      throw (IO.userError s!"program environment failed: {reprStr errors}")

private def environment : IO ProgramEnvironment := do
  let types ← parsed .main "types.solc" (String.intercalate "\n" [
    "enum Box<T> { Wrap(T) }",
    "trait Show<T> {}",
    "type Identity(T) = T;",
    "type Applied(T) = T<Word>;",
    "type Local = Box<Word>;",
    "type Callable = function(Box<Word>) returns (Bool);",
    "type IntegerBuiltin = integer;",
    "type AppliedInteger = integer<Word>;",
    "export {Box};"
  ])
  let models ← parsed .main "models.solc" (String.intercalate "\n" [
    "import * as types from types;",
    "import {Box} from types;",
    "import * as dep from @dep.containers;",
    "type Qualified = types.Box<Bool>;",
    "type Imported = Box<word>;",
    "type External = dep.Remote;",
    "type Tupled = (unit, Bool, Word);",
    "type WrongArity = Box;",
    "type MissingAlias = Missing;",
    "type CapitalInteger = Integer;"
  ])
  let dependency ← parsed (.external "dep") "containers.solc"
    "export {*}; enum Remote { One }"
  build [types, models, dependency]

private def declaration (environment : ProgramEnvironment)
    (modulePath name : String) : IO ProgramDeclaration := do
  match environment.declarations.find? fun declaration =>
      declaration.name == some name &&
        declaration.id.moduleId.path.render == modulePath with
  | some declaration => pure declaration
  | none => throw (IO.userError s!"missing declaration {modulePath}.{name}")

private def aliasValue (declaration : ProgramDeclaration) : IO Syntax.TypeExpr := do
  match declaration.source.value with
  | .typeAlias alias => pure alias.value.value
  | _ => throw (IO.userError "selected declaration was not a type alias")

private def resolvedAlias (environment : ProgramEnvironment)
    (modulePath name : String) : IO TypeSystem.Ty := do
  let declaration ← declaration environment modulePath name
  let source ← aliasValue declaration
  match resolveProgramTypeExpr environment (.ofDeclaration declaration) source with
  | .ok type => pure type
  | .error error =>
      throw (IO.userError s!"{name} did not resolve: {reprStr error}")

private def testSuccessfulResolution : IO Unit := do
  let environment ← environment
  let box ← declaration environment "types" "Box"
  let remote ← declaration environment "containers" "Remote"
  let identity ← declaration environment "types" "Identity"
  assertTrue (decide (box.id.declarationIndex = 0 ∧
      identity.id.declarationIndex = 2))
    "top-item source order did not determine stable declaration IDs"
  assertTrue (decide ((environment.localTraitsNamed box.id.moduleId "Show").length = 1 ∧
      (environment.valuesNamed "unused").isEmpty = true))
    "trait/value namespace lookup changed"
  let identityType ← resolvedAlias environment "types" "Identity"
  assertTrue (decide (identityType =
      TypeSystem.Ty.parameter { owner := identity.id, index := 0 }))
    "generic parameter did not shadow program names"
  let localType ← resolvedAlias environment "types" "Local"
  assertTrue (decide (localType = TypeSystem.Ty.nominal box.id [.word]))
    "local nominal application did not resolve"
  let qualified ← resolvedAlias environment "models" "Qualified"
  assertTrue (decide (qualified = TypeSystem.Ty.nominal box.id [.bool]))
    "same-library qualified type did not resolve"
  let imported ← resolvedAlias environment "models" "Imported"
  assertTrue (decide (imported = TypeSystem.Ty.nominal box.id [.word]))
    "an explicitly imported type did not resolve"
  let external ← resolvedAlias environment "models" "External"
  assertTrue (decide (external = TypeSystem.Ty.nominal remote.id []))
    "external-library qualified type did not resolve"
  let tupled ← resolvedAlias environment "models" "Tupled"
  assertTrue (decide (tupled = .product .unit (.product .bool .word)))
    "tuple type did not resolve to a right-associated product"
  let callable ← resolvedAlias environment "types" "Callable"
  assertTrue (decide (callable = .function
      (TypeSystem.Ty.nominal box.id [.word]) .bool))
    "function type did not resolve structurally"
  let integer ← resolvedAlias environment "types" "IntegerBuiltin"
  assertTrue (decide (integer = TypeSystem.Ty.integer))
    "the lowercase integer intrinsic did not resolve"

private def expectResolutionFailures : IO Unit := do
  let environment ← environment
  let wrong ← declaration environment "models" "WrongArity"
  let wrongSource ← aliasValue wrong
  match resolveProgramTypeExpr environment (.ofDeclaration wrong) wrongSource with
  | .error (.typeArityMismatch ["Box"] 1 0) => pure ()
  | result => throw (IO.userError s!"wrong arity result changed: {reprStr result}")
  let missing ← declaration environment "models" "MissingAlias"
  let missingSource ← aliasValue missing
  match resolveProgramTypeExpr environment (.ofDeclaration missing) missingSource with
  | .error (.unknownTypeName ["Missing"]) => pure ()
  | result => throw (IO.userError s!"unknown type result changed: {reprStr result}")
  let applied ← declaration environment "types" "Applied"
  let appliedSource ← aliasValue applied
  match resolveProgramTypeExpr environment (.ofDeclaration applied) appliedSource with
  | .error (.typeParameterApplied "T" 0 1) => pure ()
  | result => throw (IO.userError
      s!"applied generic parameter result changed: {reprStr result}")
  let identity ← declaration environment "types" "Identity"
  let identitySource ← aliasValue identity
  let duplicateScope : ProgramTypeScope := {
    currentModule := identity.id.moduleId
    genericOwner := identity.id
    genericParameters := ["T", "T"]
  }
  match resolveProgramTypeExpr environment duplicateScope identitySource with
  | .error (.duplicateGenericParameter "T" 0 1) => pure ()
  | result => throw (IO.userError
      s!"duplicate generic result changed: {reprStr result}")
  let appliedInteger ← declaration environment "types" "AppliedInteger"
  let appliedIntegerSource ← aliasValue appliedInteger
  match resolveProgramTypeExpr environment (.ofDeclaration appliedInteger)
      appliedIntegerSource with
  | .error (.typeArityMismatch ["integer"] 0 1) => pure ()
  | result => throw (IO.userError
      s!"applied integer result changed: {reprStr result}")
  let capitalInteger ← declaration environment "models" "CapitalInteger"
  let capitalIntegerSource ← aliasValue capitalInteger
  match resolveProgramTypeExpr environment (.ofDeclaration capitalInteger)
      capitalIntegerSource with
  | .error (.unknownTypeName ["Integer"]) => pure ()
  | result => throw (IO.userError
      s!"uppercase Integer unexpectedly became intrinsic: {reprStr result}")

private def testIntegerFallbackPriority : IO Unit := do
  let localSource ← parsed .main "local_integer.solc"
    "enum integer { Only } type Use = integer;"
  let localEnvironment ← build [localSource]
  let localInteger ← declaration localEnvironment "local_integer" "integer"
  let localUse ← resolvedAlias localEnvironment "local_integer" "Use"
  assertTrue (decide (localUse = TypeSystem.Ty.nominal localInteger.id []))
    "a local integer declaration did not shadow the intrinsic"

  let exportedSource ← parsed .main "exported_integer.solc"
    "export {*}; enum integer { Only }"
  let importedConsumer ← parsed .main "imported_integer.solc"
    "import * from exported_integer; type Use = integer;"
  let importedEnvironment ← build [exportedSource, importedConsumer]
  let importedInteger ← declaration importedEnvironment
    "exported_integer" "integer"
  let importedUse ← resolvedAlias importedEnvironment
    "imported_integer" "Use"
  assertTrue (decide (importedUse = TypeSystem.Ty.nominal importedInteger.id []))
    "a visible imported integer declaration did not shadow the intrinsic"

  let globalSource ← parsed .main "global_integer.solc"
    "enum integer { Only }"
  let globalConsumer ← parsed .main "global_consumer.solc"
    "type Use = integer;"
  let globalEnvironment ← build [globalSource, globalConsumer]
  let globalUse ← resolvedAlias globalEnvironment "global_consumer" "Use"
  assertTrue (decide (globalUse = TypeSystem.Ty.integer))
    "an unimported global declaration hid the integer intrinsic"

  let unrelatedImport ← parsed .main "unrelated.solc"
    "export {*}; enum Visible { Only }"
  let isolatedConsumer ← parsed .main "isolated_integer.solc"
    "import * from unrelated; type Use = integer;"
  let isolatedEnvironment ← build
    [globalSource, unrelatedImport, isolatedConsumer]
  let isolatedUse ← resolvedAlias isolatedEnvironment
    "isolated_integer" "Use"
  assertTrue (decide (isolatedUse = TypeSystem.Ty.integer))
    "an unimported integer declaration incorrectly hid the intrinsic"

private def testStrictImportVisibility : IO Unit := do
  let provider ← parsed .main "provider.solc"
    "export {*}; enum Hidden { Only }"
  let unrelated ← parsed .main "unrelated.solc"
    "export {*}; enum Visible { Only }"
  let consumer ← parsed .main "consumer.solc" (String.intercalate "\n" [
    "import * from unrelated;",
    "type Unqualified = Hidden;",
    "type Canonical = provider.Hidden;"
  ])
  let environment ← build [provider, unrelated, consumer]
  for (name, expected) in [
      ("Unqualified", ProgramTypeResolutionError.unknownTypeName ["Hidden"]),
      ("Canonical", ProgramTypeResolutionError.unknownTypeName
        ["provider", "Hidden"])
    ] do
    let declaration ← declaration environment "consumer" name
    let source ← aliasValue declaration
    match resolveProgramTypeExpr environment (.ofDeclaration declaration) source with
    | .error actual =>
        assertTrue (decide (actual = expected))
          s!"{name} received the wrong strict-visibility diagnostic"
    | .ok type => throw (IO.userError
        s!"{name} reached an unimported declaration: {reprStr type}")

private def expectEnvironmentFailures : IO Unit := do
  let duplicate ← parsed .main "duplicate.solc"
    "enum Clash { One } type Clash = word;"
  match buildProgramEnvironment [duplicate] with
  | .error [.duplicateDeclaration _ .type "Clash" first second] =>
      assertTrue (decide (first.declarationIndex = 0 ∧
          second.declarationIndex = 1))
        "duplicate declaration IDs lost source order"
  | result => throw (IO.userError
      s!"duplicate declaration result changed: {reprStr result}")
  match buildProgramEnvironment [duplicate, duplicate] with
  | .error errors =>
      assertTrue (errors.any fun error =>
        match error with
        | .duplicateModule _ => true
        | _ => false) "duplicate module was not reported"
  | .ok _ => throw (IO.userError "duplicate module was accepted")
  let left ← parsed .main "left.solc" "export {*}; enum Shared { Left }"
  let right ← parsed .main "right.solc" "export {*}; enum Shared { Right }"
  let consumer ← parsed .main "consumer.solc" (String.intercalate "\n" [
    "import * from left;",
    "import * from right;",
    "type Use = Shared;"
  ])
  let ambiguousEnvironment ←
    match buildProgramEnvironment [left, right, consumer] with
    | .ok environment => pure environment
    | .error errors => throw (IO.userError
        s!"cross-module same names were rejected: {reprStr errors}")
  let use ← declaration ambiguousEnvironment "consumer" "Use"
  let useSource ← aliasValue use
  match resolveProgramTypeExpr ambiguousEnvironment (.ofDeclaration use) useSource with
  | .error (.ambiguousTypeName ["Shared"] candidates) =>
      assertTrue (decide (candidates.length = 2))
        "ambiguous type did not retain both candidates"
  | result => throw (IO.userError
      s!"ambiguous type result changed: {reprStr result}")

end ProgramEnvironmentAndTypeResolution

/-- Run the first executable whole-program static-semantics vertical slice. -/
def testProgramEnvironmentAndTypeResolution : IO Unit := do
  ProgramEnvironmentAndTypeResolution.testSuccessfulResolution
  ProgramEnvironmentAndTypeResolution.expectResolutionFailures
  ProgramEnvironmentAndTypeResolution.testIntegerFallbackPriority
  ProgramEnvironmentAndTypeResolution.testStrictImportVisibility
  ProgramEnvironmentAndTypeResolution.expectEnvironmentFailures

end Tests
end

section
-- leanmerge: from Solcore.Test.ProgramIdentity
/-! Regression tests for collision-free whole-program trait and impl identities. -/

set_option autoImplicit false

namespace Tests.ProgramIdentity

open Solcore
open Solcore.Frontend
open Solcore.Frontend.TypedTraitResolution
open Solcore.TypeSystem

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"program_identity", by decide⟩], by decide⟩⟩

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨moduleId, index⟩

private def sourceTraitDeclaration := declaration 0
private def sourceImplDeclaration := declaration 1

example : ((sourceTraitDeclaration : ProgramTraitId).declaration?) =
    some sourceTraitDeclaration := by
  rfl

example : (ProgramTraitId.builtin .int).declaration? = none := by
  rfl

example : ProgramTraitId.builtin .int ≠
    ProgramTraitId.declaration sourceTraitDeclaration := by
  decide

example {left right : Resolved.DeclarationId}
    (same : ProgramTraitId.declaration left = .declaration right) :
    left = right := by
  exact ProgramTraitId.declaration.inj same

example : ((sourceImplDeclaration : ProgramImplId).declaration?) =
    some sourceImplDeclaration := by
  rfl

example : (ProgramImplId.builtin .intWord).declaration? = none := by
  rfl

example : ProgramImplId.builtin .intWord ≠
    ProgramImplId.declaration sourceImplDeclaration := by
  decide

example {left right : Resolved.DeclarationId}
    (same : ProgramImplId.declaration left = .declaration right) :
    left = right := by
  exact ProgramImplId.declaration.inj same

private def sourceGoal : Predicate := {
  trait := sourceTraitDeclaration
  subject := .word
  arguments := []
}

private def builtinGoal : Predicate := {
  trait := .builtin .int
  subject := .word
  arguments := []
}

private def sourceRule : ImplRule := {
  id := sourceImplDeclaration
  head := sourceGoal
  wherePredicates := []
}

private def builtinRule : ImplRule := {
  id := .builtin .intWord
  head := builtinGoal
  wherePredicates := []
}

private def sourceResolutionPreservesTags : Bool :=
  match (resolve [builtinRule, sourceRule] 1 sourceGoal).outcome with
  | .success (.byImpl goal implementation []) =>
      decide (goal = sourceGoal ∧
        implementation = ProgramImplId.declaration sourceImplDeclaration)
  | _ => false

private def builtinResolutionPreservesTags : Bool :=
  match (resolve [sourceRule, builtinRule] 1 builtinGoal).outcome with
  | .success (.byImpl goal implementation []) =>
      decide (goal = builtinGoal ∧ implementation = .builtin .intWord)
  | _ => false

private def sourceRuleDoesNotMatchBuiltinGoal : Bool :=
  match (resolve [sourceRule] 1 builtinGoal).outcome with
  | .noSolution => true
  | _ => false

private def builtinRuleDoesNotMatchSourceGoal : Bool :=
  match (resolve [builtinRule] 1 sourceGoal).outcome with
  | .noSolution => true
  | _ => false

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

/-- Exercise disjoint source/builtin identities through typed class resolution. -/
def testProgramIdentity : IO Unit := do
  assertTrue sourceResolutionPreservesTags
    "source trait resolution lost its declaration-tagged implementation"
  assertTrue builtinResolutionPreservesTags
    "builtin trait resolution lost its builtin-tagged implementation"
  assertTrue sourceRuleDoesNotMatchBuiltinGoal
    "source trait identity collided with the builtin Int trait"
  assertTrue builtinRuleDoesNotMatchSourceGoal
    "builtin Int trait identity collided with a source trait declaration"

end Tests.ProgramIdentity
end

section
-- leanmerge: from Solcore.Test.ProgramImports
/-! Parsed multi-file regressions for active direct-import type visibility. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

namespace ProgramImports

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def parsed (origin : Syntax.SourceOrigin) (path content : String) :
    IO Syntax.ParsedFile := do
  let file : Syntax.SourceFile := { id := { origin, path }, content }
  match Syntax.Parser.parse file with
  | .error error => throw (IO.userError
      s!"{path}: parser invariant failed: {reprStr error}")
  | .ok output =>
      unless output.lexicalDiagnostics.isEmpty &&
          output.parseDiagnostics.isEmpty do
        throw (IO.userError
          s!"{path}: source diagnostics: {reprStr output.lexicalDiagnostics}; {reprStr output.parseDiagnostics}")
      pure output.parsed

private def build (sources : List Syntax.ParsedFile) : IO ProgramEnvironment := do
  match buildProgramEnvironment sources with
  | .ok environment => pure environment
  | .error errors => throw (IO.userError
      s!"program environment failed: {reprStr errors}")

private def declaration (environment : ProgramEnvironment)
    (modulePath name : String) : IO ProgramDeclaration := do
  match environment.declarations.find? fun declaration =>
      declaration.id.moduleId.path.render == modulePath &&
        declaration.name == some name with
  | some declaration => pure declaration
  | none => throw (IO.userError s!"missing {modulePath}.{name}")

private def aliasSource (declaration : ProgramDeclaration) : IO Syntax.TypeExpr := do
  match declaration.source.value with
  | .typeAlias alias => pure alias.value.value
  | _ => throw (IO.userError "selected declaration is not a type alias")

private def resolveAlias (environment : ProgramEnvironment)
    (modulePath name : String) : IO TypeSystem.Ty := do
  let declaration ← declaration environment modulePath name
  let source ← aliasSource declaration
  match resolveProgramTypeExpr environment (.ofDeclaration declaration) source with
  | .ok type => pure type
  | .error error => throw (IO.userError
      s!"{modulePath}.{name} failed: {reprStr error}")

private def importedEnvironment : IO ProgramEnvironment := do
  let source ← parsed .main "library/types.solc" (String.intercalate "\n" [
    "export {*};",
    "enum Public { P }",
    "enum Hidden { H }",
    "enum Renamed { R }",
    "trait Marker<T> {}",
    "trait HiddenTrait<T> {}",
    "function pick(value: Word) returns (Word) { return value; }",
    "function pick(value: Bool) returns (Bool) { return value; }",
    "function hiddenValue() returns (Word) { return 0; }"
  ])
  let external ← parsed (.external "dep") "external.solc"
    "export {*}; enum Remote { R }"
  let consumer ← parsed .main "consumer.solc" (String.intercalate "\n" [
    "import library.types;",
    "import * as Lib from library.types;",
    "import * from library.types hiding {Hidden, HiddenTrait, hiddenValue};",
    "import {Renamed as Alias, Hidden, Marker, Marker as ChosenTrait, pick, pick as chosen, HiddenTrait as HiddenMarker, hiddenValue as hidden} from library.types hiding {Hidden, HiddenTrait, hiddenValue};",
    "import @dep.external;",
    "import * as Ext from @dep.external;",
    "enum Public { Local }",
    "type PlainQualified = types.Renamed;",
    "type NamespaceQualified = Lib.Hidden;",
    "type Wildcard = Renamed;",
    "type SelectedAlias = Alias;",
    "type ExternalPlain = external.Remote;",
    "type ExternalNamespace = Ext.Remote;",
    "type LocalShadow = Public;",
    "type HiddenMissing = Hidden;"
  ])
  build [source, external, consumer]

private def testVisibilityConstruction : IO Unit := do
  let environment ← importedEnvironment
  let consumer ← declaration environment "consumer" "PlainQualified"
  match buildProgramImports environment consumer.id.moduleId with
  | .error errors => throw (IO.userError
      s!"valid imports failed: {reprStr errors}")
  | .ok visibility =>
      assertTrue (decide (visibility.hasImports = true ∧
          visibility.namespaces.length = 4 ∧
          visibility.types.length = 3 ∧
          visibility.traits.length = 3 ∧
          visibility.values.length = 6))
        "direct import visibility shape changed"
      assertTrue (decide ((visibility.modulesNamed "types").length = 1 ∧
          (visibility.modulesNamed "Lib").length = 1 ∧
          (visibility.modulesNamed "external").length = 1 ∧
          (visibility.modulesNamed "Ext").length = 1))
        "plain or explicit namespace aliases were not retained"
      assertTrue (decide ((visibility.typesNamed "Public").length = 1 ∧
          (visibility.typesNamed "Renamed").length = 1 ∧
          (visibility.typesNamed "Alias").length = 1 ∧
          (visibility.typesNamed "Hidden").isEmpty = true))
        "wildcard/selected/hiding visibility changed"
      assertTrue (decide (
          (visibility.traitsNamed "Marker").length = 1 ∧
          (visibility.traitsNamed "ChosenTrait").length = 1 ∧
          (visibility.traitsNamed "HiddenTrait").isEmpty = true ∧
          (visibility.traitsNamed "HiddenMarker").isEmpty = true))
        "trait wildcard/selected/alias/hiding/dedup visibility changed"
      assertTrue (decide (
          (visibility.valuesNamed "pick").length = 2 ∧
          (visibility.valuesNamed "chosen").length = 2 ∧
          (visibility.valuesNamed "hiddenValue").isEmpty = true ∧
          (visibility.valuesNamed "hidden").isEmpty = true))
        "value overload/selected/alias/hiding/dedup visibility changed"

private def testSuccessfulLookup : IO Unit := do
  let environment ← importedEnvironment
  let sourcePublic ← declaration environment "library/types" "Public"
  let sourceHidden ← declaration environment "library/types" "Hidden"
  let sourceRenamed ← declaration environment "library/types" "Renamed"
  let remote ← declaration environment "external" "Remote"
  let localPublic ← declaration environment "consumer" "Public"
  let plain ← resolveAlias environment "consumer" "PlainQualified"
  assertTrue (decide (plain = TypeSystem.Ty.nominal sourceRenamed.id []))
    "plain import did not expose its default namespace"
  let namespaced ← resolveAlias environment "consumer" "NamespaceQualified"
  assertTrue (decide (namespaced = TypeSystem.Ty.nominal sourceHidden.id []))
    "namespace import did not qualify the target type"
  let wildcard ← resolveAlias environment "consumer" "Wildcard"
  assertTrue (decide (wildcard = TypeSystem.Ty.nominal sourceRenamed.id []))
    "wildcard import did not expose an unqualified type"
  let selected ← resolveAlias environment "consumer" "SelectedAlias"
  assertTrue (decide (selected = TypeSystem.Ty.nominal sourceRenamed.id []))
    "selected import alias did not resolve"
  let externalPlain ← resolveAlias environment "consumer" "ExternalPlain"
  let externalNamespace ← resolveAlias environment "consumer" "ExternalNamespace"
  assertTrue (decide (externalPlain = TypeSystem.Ty.nominal remote.id [] ∧
      externalNamespace = TypeSystem.Ty.nominal remote.id []))
    "@external namespace resolution changed"
  let shadowed ← resolveAlias environment "consumer" "LocalShadow"
  assertTrue (decide (shadowed = TypeSystem.Ty.nominal localPublic.id [] ∧
      shadowed ≠ TypeSystem.Ty.nominal sourcePublic.id []))
    "local declaration did not shadow its imported namesake"

private def testHiddenAndAmbiguousLookup : IO Unit := do
  let environment ← importedEnvironment
  let hidden ← declaration environment "consumer" "HiddenMissing"
  let hiddenSource ← aliasSource hidden
  match resolveProgramTypeExpr environment (.ofDeclaration hidden) hiddenSource with
  | .error (.unknownTypeName ["Hidden"]) => pure ()
  | result => throw (IO.userError
      s!"hidden import remained visible: {reprStr result}")
  let left ← parsed .main "left.solc" (String.intercalate "\n" [
    "export {*};",
    "enum Shared { Left }",
    "trait Shared<T> {}",
    "function sharedValue(value: Word) returns (Word) { return value; }"
  ])
  let right ← parsed .main "right.solc" (String.intercalate "\n" [
    "export {*};",
    "enum Shared { Right }",
    "trait Shared<T> {}",
    "function sharedValue(value: Bool) returns (Bool) { return value; }"
  ])
  let consumer ← parsed .main "ambiguous.solc" (String.intercalate "\n" [
    "import * from left;",
    "import * from right;",
    "import * as Both from left;",
    "import * as Both from right;",
    "type Unqualified = Shared;",
    "type Qualified = Both.Shared;"
  ])
  let ambiguous ← build [left, right, consumer]
  let visibility ← match buildProgramImports ambiguous
      (← declaration ambiguous "ambiguous" "Unqualified").id.moduleId with
    | .ok visibility => pure visibility
    | .error errors => throw (IO.userError
        s!"ambiguous imports failed to build: {reprStr errors}")
  assertTrue (decide ((visibility.traitsNamed "Shared").length = 2 ∧
      (visibility.valuesNamed "sharedValue").length = 2))
    "imported trait/value ambiguity did not retain all candidates"
  for alias in ["Unqualified", "Qualified"] do
    let declaration ← declaration ambiguous "ambiguous" alias
    let source ← aliasSource declaration
    match resolveProgramTypeExpr ambiguous (.ofDeclaration declaration) source with
    | .error (.ambiguousTypeName _ candidates) =>
        assertTrue (decide (candidates.length = 2))
          s!"{alias}: import ambiguity lost a candidate"
    | result => throw (IO.userError
        s!"{alias}: expected import ambiguity, got {reprStr result}")

private def testImportErrors : IO Unit := do
  let source ← parsed .main "source.solc"
    "export {*}; enum Present { P } function value() {} trait Marker<T> {}"
  let deferred ← parsed .main "deferred.solc"
    "import {value, Marker} from source; type Kept = Word;"
  let deferredEnvironment ← build [source, deferred]
  let deferredOwner ← declaration deferredEnvironment "deferred" "Kept"
  match buildProgramImports deferredEnvironment deferredOwner.id.moduleId with
  | .ok visibility =>
      assertTrue (decide (visibility.types.isEmpty = true ∧
          (visibility.valuesNamed "value").length = 1 ∧
          (visibility.traitsNamed "Marker").length = 1))
        "selected value/trait visibility changed"
  | .error errors => throw (IO.userError
      s!"known deferred selector was rejected: {reprStr errors}")
  let badSelection ← parsed .main "bad_selection.solc"
    "import {Missing} from source; type Kept = Word; type Trigger = Present;"
  let selectionEnvironment ← build [source, badSelection]
  let selectionOwner ← declaration selectionEnvironment "bad_selection" "Kept"
  match buildProgramImports selectionEnvironment selectionOwner.id.moduleId with
  | .error [.publicInterface [.unknownImportName _ _ "Missing"]] => pure ()
  | result => throw (IO.userError
      s!"unknown selected import result changed: {reprStr result}")
  let trigger ← declaration selectionEnvironment "bad_selection" "Trigger"
  let triggerSource ← aliasSource trigger
  match resolveProgramTypeExpr selectionEnvironment (.ofDeclaration trigger)
      triggerSource with
  | .error (.importVisibility
      [.publicInterface [.unknownImportName _ _ "Missing"]]) => pure ()
  | result => throw (IO.userError
      s!"type resolver did not expose import failure: {reprStr result}")
  let badOperator ← parsed .main "bad_operator.solc"
    "import {(==) as eq} from source; type Kept = Word;"
  let operatorEnvironment ← build [source, badOperator]
  let operatorOwner ← declaration operatorEnvironment "bad_operator" "Kept"
  match buildProgramImports operatorEnvironment operatorOwner.id.moduleId with
  | .error [.publicInterface [.unknownImportName _ _ "=="]] => pure ()
  | result => throw (IO.userError
      s!"operator selector was ignored or lost its spelling: {reprStr result}")
  let badModule ← parsed .main "bad_module.solc"
    "import absent.module; type Kept = Word;"
  let moduleEnvironment ← build [badModule]
  let moduleOwner ← declaration moduleEnvironment "bad_module" "Kept"
  match buildProgramImports moduleEnvironment moduleOwner.id.moduleId with
  | .error [.publicInterface [.unknownModule _ ["absent", "module"]]] => pure ()
  | result => throw (IO.userError
      s!"unknown imported module result changed: {reprStr result}")

end ProgramImports

/-- Run direct-import visibility and resolution regressions. -/
def testProgramImports : IO Unit := do
  ProgramImports.testVisibilityConstruction
  ProgramImports.testSuccessfulLookup
  ProgramImports.testHiddenAndAmbiguousLookup
  ProgramImports.testImportErrors

end Tests
end

section
-- leanmerge: from Solcore.Test.ProgramInterfaces
/-! Executable regressions for explicit public interfaces and re-export closure. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

namespace ProgramInterfaces

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def parsed (path content : String) : IO Syntax.ParsedFile := do
  let file : Syntax.SourceFile := {
    id := { origin := .main, path }
    content
  }
  match Syntax.Parser.parse file with
  | .error error => throw (IO.userError
      s!"{path}: parser invariant failed: {reprStr error}")
  | .ok output =>
      unless output.lexicalDiagnostics.isEmpty &&
          output.parseDiagnostics.isEmpty do
        throw (IO.userError
          s!"{path}: source diagnostics: {reprStr output.lexicalDiagnostics}; {reprStr output.parseDiagnostics}")
      pure output.parsed

private def environment (sources : List Syntax.ParsedFile) :
    IO ProgramEnvironment := do
  match buildProgramEnvironment sources with
  | .ok environment => pure environment
  | .error errors => throw (IO.userError
      s!"program environment failed: {reprStr errors}")

private def interfaces (sources : List Syntax.ParsedFile) :
    IO (ProgramEnvironment × Solcore.Frontend.ProgramInterfaces) := do
  let environment ← environment sources
  match buildProgramInterfaces environment with
  | .ok interfaces => pure (environment, interfaces)
  | .error errors => throw (IO.userError
      s!"program interfaces failed: {reprStr errors}")

private def moduleId (environment : ProgramEnvironment)
    (path : String) : IO Workspace.ModuleId := do
  match environment.modules.find? fun module => module.id.path.render == path with
  | some module => pure module.id
  | none => throw (IO.userError s!"missing module {path}")

private def publicNames
    (interfaces : Solcore.Frontend.ProgramInterfaces)
    (moduleId : Workspace.ModuleId) : List String :=
  match interfaces.interface? moduleId with
  | none => []
  | some interface => interface.entities.map (·.publicName)

private def constructorVisibility?
    (interfaces : Solcore.Frontend.ProgramInterfaces)
    (moduleId : Workspace.ModuleId) (name : String) :
    Option ProgramConstructorVisibility := do
  let interface ← interfaces.interface? moduleId
  let entity ← interface.entities.find? fun entity =>
    entity.publicName == name && entity.declaration.nameSpace == some .type
  pure entity.constructors

private def testExplicitLocalInterfaces : IO Unit := do
  let implicit ← parsed "implicit.solc" <|
    "enum Private { Only } function hidden() returns (Word) { return 0; }"
  let declared ← parsed "declared.solc" (String.intercalate "\n" [
    "type Alias = Word;",
    "enum Choice { One }",
    "trait Marker<T> {}",
    "function over(value: Word) returns (Word) { return value; }",
    "function over(value: Bool) returns (Bool) { return value; }",
    "enum Hidden { Never }",
    "export {Alias, Choice, Marker, over};"
  ])
  let (environment, result) ← interfaces [implicit, declared]
  let implicitId ← moduleId environment "implicit"
  let declaredId ← moduleId environment "declared"
  assertTrue (decide ((result.interface? implicitId).map
      (·.entities.isEmpty) == some true))
    "a module without exports acquired an implicit interface"
  assertTrue (decide (
      (result.entitiesNamed declaredId .type "Alias").length = 1 ∧
      (result.entitiesNamed declaredId .type "Choice").length = 1 ∧
      (result.entitiesNamed declaredId .trait "Marker").length = 1 ∧
      (result.entitiesNamed declaredId .value "over").length = 2 ∧
      (result.declarationsNamed declaredId "Hidden").isEmpty = true))
    "local type/trait/value export or overload retention changed"
  assertTrue (publicNames result declaredId ==
      ["Alias", "Choice", "Marker", "over", "over"])
    "public entity order is no longer deterministic"

private def testImportedAliasAndHiding : IO Unit := do
  let provider ← parsed "provider.solc" (String.intercalate "\n" [
    "enum Public { P }",
    "enum Hidden { H }",
    "export {Public, Hidden};"
  ])
  let consumer ← parsed "consumer.solc" (String.intercalate "\n" [
    "import {Public as Renamed} from provider;",
    "import * from provider hiding {Hidden};",
    "export {Renamed, Public};"
  ])
  let (environment, result) ← interfaces [provider, consumer]
  let consumerId ← moduleId environment "consumer"
  let renamed := result.entitiesNamed consumerId .type "Renamed"
  let unaliased := result.entitiesNamed consumerId .type "Public"
  let sameDeclaration := match renamed, unaliased with
    | [left], [right] => decide (left.id = right.id)
    | _, _ => false
  assertTrue (sameDeclaration &&
      (result.declarationsNamed consumerId "Hidden").isEmpty)
    "import aliases or hiding were not reflected by a local named re-export"

private def testChainsAndCycles : IO Unit := do
  let c ← parsed "c.solc" "enum Seed { S } export {Seed};"
  let b ← parsed "b.solc" "export c.*;"
  let a ← parsed "a.solc" "export b.*;"
  let x ← parsed "x.solc"
    "enum Root { R } export {Root}; export y.*;"
  let y ← parsed "y.solc" "export x.*;"
  let p ← parsed "p.solc" "export q.*;"
  let q ← parsed "q.solc" "export p.*;"
  let (environment, result) ← interfaces [a, b, c, x, y, p, q]
  let aId ← moduleId environment "a"
  let xId ← moduleId environment "x"
  let yId ← moduleId environment "y"
  let pId ← moduleId environment "p"
  let qId ← moduleId environment "q"
  assertTrue (decide ((result.entitiesNamed aId .type "Seed").length = 1))
    "A-to-B-to-C wildcard re-export did not reach its fixed point"
  assertTrue (decide (
      (result.entitiesNamed xId .type "Root").length = 1 ∧
      (result.entitiesNamed yId .type "Root").length = 1))
    "a seeded positive cycle did not propagate its entity"
  assertTrue (decide (publicNames result pId = [] ∧ publicNames result qId = []))
    "a seedless positive cycle did not converge to the empty interface"

private def testWildcardBoundaries : IO Unit := do
  let provider ← parsed "origin.solc"
    "enum Imported { I } export {Imported};"
  let localSource ← parsed "local.solc" (String.intercalate "\n" [
    "import * from origin;",
    "enum Mine { M }",
    "export {*};"
  ])
  let copied ← parsed "copied.solc" "export {origin.*};"
  let (environment, result) ← interfaces [provider, localSource, copied]
  let localId ← moduleId environment "local"
  let copiedId ← moduleId environment "copied"
  assertTrue (decide (
      (result.entitiesNamed localId .type "Mine").length = 1 ∧
      (result.declarationsNamed localId "Imported").isEmpty = true))
    "local wildcard leaked an imported entity"
  assertTrue (decide (
      (result.entitiesNamed copiedId .type "Imported").length = 1))
    "local module wildcard did not copy the target public interface"

private def testModuleBindingsAndSelectionUnion : IO Unit := do
  let provider ← parsed "base.solc" (String.intercalate "\n" [
    "enum Alpha { A }",
    "enum Beta { B }",
    "export {Alpha, Beta};"
  ])
  let binding ← parsed "binding.solc" (String.intercalate "\n" [
    "export base;",
    "export base as B;"
  ])
  let selected ← parsed "selected.solc" (String.intercalate "\n" [
    "export base.{};",
    "export base.{*, Alpha};"
  ])
  let localMixed ← parsed "mixed.solc" (String.intercalate "\n" [
    "enum Left { L }",
    "enum Right { R }",
    "export {};",
    "export {*, Left};"
  ])
  let (environment, result) ← interfaces [provider, binding, selected, localMixed]
  let baseId ← moduleId environment "base"
  let bindingId ← moduleId environment "binding"
  let selectedId ← moduleId environment "selected"
  let mixedId ← moduleId environment "mixed"
  assertTrue (decide (
      result.modulesNamed bindingId "base" = [baseId] ∧
      result.modulesNamed bindingId "B" = [baseId]))
    "module/moduleAs did not create public namespace bindings"
  assertTrue (publicNames result selectedId == ["Alpha", "Beta"])
    "empty or mixed remote selection did not behave as union/no-op"
  assertTrue (publicNames result mixedId == ["Left", "Right"])
    "empty or mixed local selection did not behave as union/no-op"

private def testConstructorVisibility : IO Unit := do
  let localAll ← parsed "localAll.solc"
    "enum LocalAll { First, Second } export {LocalAll(*)};"
  let localSubset ← parsed "localSubset.solc"
    "enum LocalSubset { First, Second } export {LocalSubset(Second)};"
  let localBare ← parsed "localBare.solc"
    "enum LocalBare { First } export {LocalBare};"
  let localWildcard ← parsed "localWildcard.solc"
    "enum LocalWildcard { First } export {*};"
  let split ← parsed "split.solc" (String.intercalate "\n" [
    "enum Split { First, Second, Third }",
    "export {Split(Second)};",
    "export {Split(First)};"
  ])
  let provider ← parsed "provider.solc" (String.intercalate "\n" [
    "enum Remote { One, Two, Hidden }",
    "export {Remote(One, Two)};"
  ])
  let remoteWildcard ← parsed "remoteWildcard.solc" "export provider.*;"
  let remoteNamed ← parsed "remoteNamed.solc" "export provider.{Remote};"
  let remoteAll ← parsed "remoteAll.solc" "export provider.{Remote(*)};"
  let remoteSubset ← parsed "remoteSubset.solc"
    "export provider.{Remote(Two)};"
  let opaqueProvider ← parsed "opaqueProvider.solc"
    "enum Opaque { One } export {Opaque};"
  let opaqueAll ← parsed "opaqueAll.solc"
    "export opaqueProvider.{Opaque(*)};"
  let cycleA ← parsed "cycleA.solc" (String.intercalate "\n" [
    "export provider.{Remote(One)};",
    "export cycleB.*;"
  ])
  let cycleB ← parsed "cycleB.solc" (String.intercalate "\n" [
    "export provider.{Remote(Two)};",
    "export cycleA.*;"
  ])
  let sources := [localAll, localSubset, localBare, localWildcard, split,
    provider, remoteWildcard, remoteNamed, remoteAll, remoteSubset,
    opaqueProvider, opaqueAll, cycleA, cycleB]
  let (environment, result) ← interfaces sources
  let visibility (path name : String) : IO (Option ProgramConstructorVisibility) := do
    pure <| constructorVisibility? result (← moduleId environment path) name
  assertTrue (decide (
      (← visibility "localAll" "LocalAll") = some (.visible ["First", "Second"]) ∧
      (← visibility "localSubset" "LocalSubset") = some (.visible ["Second"]) ∧
      (← visibility "localBare" "LocalBare") = some .opaqueData ∧
      (← visibility "localWildcard" "LocalWildcard") = some .opaqueData ∧
      (← visibility "split" "Split") = some (.visible ["First", "Second"])))
    "local constructor selection, opacity, or deterministic union changed"
  assertTrue (decide (
      (← visibility "remoteWildcard" "Remote") =
        some (.visible ["One", "Two"]) ∧
      (← visibility "remoteNamed" "Remote") = some .opaqueData ∧
      (← visibility "remoteAll" "Remote") =
        some (.visible ["One", "Two"]) ∧
      (← visibility "remoteSubset" "Remote") = some (.visible ["Two"])))
    "remote wildcard preservation, named opacity, or bounded selection changed"
  assertTrue (decide ((← visibility "opaqueAll" "Opaque") = some .opaqueData))
    "an empty visible constructor selection was not normalized to opaque data"
  assertTrue (decide (
      (← visibility "cycleA" "Remote") = some (.visible ["One", "Two"]) ∧
      (← visibility "cycleB" "Remote") = some (.visible ["One", "Two"])))
    "constructor subsets did not union deterministically through a cycle"

private def testExplicitErrors : IO Unit := do
  let unsupported ← parsed "unsupported.solc" (String.intercalate "\n" [
    "enum Choice { One }",
    "type Alias = Word;",
    "export {Choice(Missing), Alias(*), (==)};"
  ])
  let unsupportedEnvironment ← environment [unsupported]
  let unsupportedId ← moduleId unsupportedEnvironment "unsupported"
  match buildProgramInterfaces unsupportedEnvironment with
  | .error errors =>
      assertTrue (decide (
          errors.contains (.unknownExportConstructor unsupportedId "Choice" "Missing") ∧
          errors.contains (.unknownExportName unsupportedId "Alias") ∧
          errors.contains (.unknownExportName unsupportedId "==")))
        "constructor validation or ordinary operator export lookup changed"
  | .ok _ => throw (IO.userError
      "invalid constructor/operator selectors were accepted")
  let provider ← parsed "bounded.solc"
    "enum Bounded { Public, Hidden } export {Bounded(Public)};"
  let revealing ← parsed "revealing.solc"
    "export bounded.{Bounded(Hidden)};"
  let revealingEnvironment ← environment [provider, revealing]
  let revealingId ← moduleId revealingEnvironment "revealing"
  match buildProgramInterfaces revealingEnvironment with
  | .error errors =>
      assertTrue (errors.contains
          (.unknownExportConstructor revealingId "Bounded" "Hidden"))
        "a named re-export revealed a constructor hidden by its provider"
  | .ok _ => throw (IO.userError
      "a hidden provider constructor was re-exported")
  let missing ← parsed "missing.solc" (String.intercalate "\n" [
    "import {Absent} from missingTarget;",
    "export absentModule.*;",
    "export {Unknown};"
  ])
  let missingTarget ← parsed "missingTarget.solc" "export {};"
  let missingEnvironment ← environment [missing, missingTarget]
  match buildProgramInterfaces missingEnvironment with
  | .error errors =>
      assertTrue (decide (
          errors.any (fun error => match error with
            | .unknownImportName _ _ "Absent" => true | _ => false) ∧
          errors.any (fun error => match error with
            | .unknownModule _ ["absentModule"] => true | _ => false) ∧
          errors.any (fun error => match error with
            | .unknownExportName _ "Unknown" => true | _ => false)))
        "missing module/name failures were not explicit"
  | .ok _ => throw (IO.userError "missing export references were accepted")

end ProgramInterfaces

/-- Run explicit-interface, re-export, and fixed-point regressions. -/
def testProgramInterfaces : IO Unit := do
  ProgramInterfaces.testExplicitLocalInterfaces
  ProgramInterfaces.testImportedAliasAndHiding
  ProgramInterfaces.testChainsAndCycles
  ProgramInterfaces.testWildcardBoundaries
  ProgramInterfaces.testModuleBindingsAndSelectionUnion
  ProgramInterfaces.testConstructorVisibility
  ProgramInterfaces.testExplicitErrors

end Tests
end

section
-- leanmerge: from Solcore.Test.ProgramLoading
/-! Executable raw-workspace to declaration-environment regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

example
    {workspace : Workspace.ValidatedUserWorkspace}
    {loaded : LoadedProgram}
    (success : loadValidatedProgram workspace = .ok loaded) :
    buildProgramEnvironment loaded.sources = .ok loaded.environment :=
  loadValidatedProgram_success_environment success

example
    {raw : Workspace.RawWorkspace}
    {loaded : LoadedProgram}
    (success : loadProgram raw = .ok loaded) :
    buildProgramEnvironment loaded.sources = .ok loaded.environment :=
  loadProgram_success_environment success

example
    {raw : Workspace.RawWorkspace}
    {loaded : LoadedProgram}
    (success : loadProgram raw = .ok loaded) :
    (loaded.environment.declarations.map (·.id)).Nodup :=
  loadProgram_success_declarations_nodup success

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do
    throw (IO.userError label)

private def validWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [
    { path := "main.solc", content := "type Main = lib.Remote;" },
    { path := "lib.solc", content := "enum Remote { Only }" }
  ]
  externalLibraries := []
}

private def testSuccessfulLoad : IO Unit := do
  match loadProgram validWorkspace with
  | .error errors =>
      throw (IO.userError s!"valid workspace failed to load: {reprStr errors}")
  | .ok loaded =>
      assertTrue (decide (loaded.sources.length = 2))
        "validated files were not all parsed"
      assertTrue (decide (loaded.environment.modules.length = 2 ∧
          loaded.environment.declarations.length = 2))
        "parsed files did not reach the declaration environment"
      assertTrue (decide (loaded.workspace.entry =
          { library := Workspace.LibraryId.main
            path := {modulePath := ⟨[⟨"main", by decide⟩], by decide⟩, extension := .solc} }))
        "validated entry identity changed while loading"

private def testWorkspaceFailure : IO Unit := do
  let invalid := { validWorkspace with entry := "missing.solc" }
  match loadProgram invalid with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .workspace (.missingEntry _) => true
        | _ => false) "missing entry was not retained"
  | .ok _ => throw (IO.userError "invalid workspace was loaded")

private def testSourceDiagnostics : IO Unit := do
  let malformed := {
    validWorkspace with
    mainSources := [{ path := "main.solc", content := "type = ;" }]
  }
  match loadProgram malformed with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .sourceDiagnostics _ _ parsing => !parsing.isEmpty
        | _ => false) "ordinary source diagnostics were not retained"
  | .ok _ => throw (IO.userError "diagnostic source was loaded")

/-- Exercise validation, parsing and declaration collection as one API. -/
def testProgramLoading : IO Unit := do
  testSuccessfulLoad
  testWorkspaceFailure
  testSourceDiagnostics

end Tests
end

section
-- leanmerge: from Solcore.Test.ProgramModuleResolution
/-! Executable regressions for canonical relative and rooted module paths. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

namespace ProgramModuleResolution

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def parsed (origin : Syntax.SourceOrigin) (path content : String) :
    IO Syntax.ParsedFile := do
  let file : Syntax.SourceFile := { id := { origin, path }, content }
  match Syntax.Parser.parse file with
  | .error error => throw (IO.userError
      s!"{path}: parser invariant failed: {reprStr error}")
  | .ok output =>
      unless output.lexicalDiagnostics.isEmpty &&
          output.parseDiagnostics.isEmpty do
        throw (IO.userError
          s!"{path}: source diagnostics: {reprStr output.lexicalDiagnostics}; {reprStr output.parseDiagnostics}")
      pure output.parsed

private def moduleId (environment : ProgramEnvironment)
    (library : Workspace.LibraryId) (path : String) : IO Workspace.ModuleId := do
  match environment.modules.find? fun module =>
      decide (module.id.library = library) && module.id.path.render == path with
  | some module => pure module.id
  | none => throw (IO.userError s!"missing module {path}")

private def importPaths (module : ProgramModule) : List Syntax.ModulePath :=
  module.source.items.filterMap fun item =>
    match item.value with
    | .importDecl declaration =>
        some <| match declaration.value with
          | .plain path | .namespace path _ | .wildcard path _
          | .selected _ path _ => path
    | _ => none

private def exportPaths (module : ProgramModule) : List Syntax.QualifiedName :=
  module.source.items.filterMap fun item =>
    match item.value with
    | .exportDecl declaration =>
        match declaration.value with
        | .module path | .moduleAs path _ | .itemsFrom path _ => some path
        | .local _ => none
    | _ => none

private def testCanonicalPaths : IO Unit := do
  let owner ← parsed .main "pkg/nested/main.solc" (String.intercalate "\n" [
    "import util;",
    "import lib.shared.util;",
    "import std.math;",
    "import std.local;",
    "import @dep.tools;",
    "import @dep;",
    "import lib;",
    "import std;",
    "export util;",
    "export lib.shared.util;",
    "export std.math;"
  ])
  let relative ← parsed .main "pkg/nested/util.solc" "export {};"
  let rooted ← parsed .main "shared/util.solc" "export {};"
  let localStdFallback ← parsed .main "pkg/nested/std/local.solc" "export {};"
  let relativeLib ← parsed .main "pkg/nested/lib.solc" "export {};"
  let relativeStd ← parsed .main "pkg/nested/std.solc" "export {};"
  let standard ← parsed .standard "math.solc" "export {};"
  let standardRoot ← parsed .standard "std.solc" "export {};"
  let external ← parsed (.external "dep") "tools.solc" "export {};"
  let externalRoot ← parsed (.external "dep") "dep.solc" "export {};"
  let environment ← match buildProgramEnvironment
      [owner, relative, rooted, localStdFallback, relativeLib, relativeStd,
        standard, standardRoot, external, externalRoot] with
    | .ok environment => pure environment
    | .error errors => throw (IO.userError
        s!"environment failed: {reprStr errors}")
  let ownerId ← moduleId environment .main "pkg/nested/main"
  let ownerModule := environment.modules.find? fun module =>
    decide (module.id = ownerId)
  let some ownerModule := ownerModule
    | throw (IO.userError "owner module disappeared")
  let relativeId ← moduleId environment .main "pkg/nested/util"
  let rootedId ← moduleId environment .main "shared/util"
  let standardId ← moduleId environment .standard "math"
  let localStdId ← moduleId environment .main "pkg/nested/std/local"
  let relativeLibId ← moduleId environment .main "pkg/nested/lib"
  let standardRootId ← moduleId environment .standard "std"
  let some dependency := Workspace.ExternalLibraryName.parse "dep"
    | throw (IO.userError "dependency name did not parse")
  let externalId ← moduleId environment (.external dependency) "tools"
  let externalRootId ← moduleId environment (.external dependency) "dep"
  let expectedImports : List Workspace.ModuleId :=
    [relativeId, rootedId, standardId, localStdId, externalId, externalRootId,
      relativeLibId, standardRootId]
  let resolvedImports := (importPaths ownerModule).map fun path =>
    resolveProgramModulePath? environment ownerId path
  assertTrue (resolvedImports == expectedImports.map some)
    "relative, lib, std, std-fallback, or external import resolution changed"
  let expectedExports := expectedImports.take 3
  let resolvedExports := (exportPaths ownerModule).map fun path =>
    resolveProgramExportPath? environment ownerId path
  assertTrue (resolvedExports == expectedExports.map some)
    "import and export paths no longer share canonical resolution"

private def testBareStdDoesNotUseLocalFallback : IO Unit := do
  let owner ← parsed .main "pkg/nested/main.solc" "import std;"
  let localStd ← parsed .main "pkg/nested/std.solc" "export {};"
  let environment ← match buildProgramEnvironment [owner, localStd] with
    | .ok environment => pure environment
    | .error errors => throw (IO.userError
        s!"bare std environment failed: {reprStr errors}")
  let ownerId ← moduleId environment .main "pkg/nested/main"
  let ownerModule ← match environment.modules.find? fun module =>
      decide (module.id = ownerId) with
    | some module => pure module
    | none => throw (IO.userError "bare std owner disappeared")
  match importPaths ownerModule with
  | [path] =>
      assertTrue ((resolveProgramModulePath? environment ownerId path).isNone)
        "bare std incorrectly used the nested local fallback"
  | paths => throw (IO.userError
      s!"bare std fixture retained {paths.length} import paths")

end ProgramModuleResolution

/-- Run canonical module-path resolution regressions. -/
def testProgramModuleResolution : IO Unit := do
  ProgramModuleResolution.testCanonicalPaths
  ProgramModuleResolution.testBareStdDoesNotUseLocalFallback

end Tests
end

section
-- leanmerge: from Solcore.Test.ProgramSignatureFormation
/-! Focused examples for flexible-variable bounds of formed signatures. -/

set_option autoImplicit false

namespace Tests.ProgramSignatureFormation

open Solcore Solcore.Frontend Solcore.TypeSystem

private def emptySignatures : ProgramSignatures := {
  functions := []
  implRules := []
  traits := []
  implementations := []
}

private def rangeDomain : TypeVarId := ⟨0⟩

private def rangeResidual : TypeVarId := ⟨1⟩

private def openRange : Substitution :=
  [(rangeDomain, .function (.variable rangeResidual) .word)]

/-- Final inference ranges may retain flexible variables when each replacement
is checked in its own complete free-variable scope. -/
example (owner : Resolved.DeclarationId) :
    validateInferenceSubstitutionRangeFormation emptySignatures owner []
      openRange = .ok () := by
  rfl

/-- Recovery types are rejected even in an otherwise open inference range. -/
example (owner : Resolved.DeclarationId) :
    validateInferenceSubstitutionRangeFormation emptySignatures owner []
        [(rangeDomain, .error)] =
      .error (.recoveryType owner) := by
  rfl

/-- An uncataloged nominal cannot enter a finalized substitution range. -/
example (owner nominal : Resolved.DeclarationId) :
    validateInferenceSubstitutionRangeFormation emptySignatures owner []
        [(rangeDomain, Ty.nominal nominal [])] =
      .error (.unknownNominal owner nominal) := by
  rfl

/-- Successful executable range validation exposes the pointwise open
formation witness used by source-semantics soundness. -/
example (owner : Resolved.DeclarationId) :
    InferenceSubstitutionRangeFormationValidated emptySignatures owner []
      openRange := by
  exact validateInferenceSubstitutionRangeFormation_success (by rfl)

example {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeParameterId}
    (next : Nat) :
    (Ty.function (Ty.product Ty.word Ty.bool) Ty.unit).VariablesBelow next := by
  have validated :
      SignatureTypeFormationValidated signatures owner parameters
        (.function (.product Ty.word Ty.bool) Ty.unit) :=
    .function (.product (.builtin .word) (.builtin .bool)) (.builtin .unit)
  exact validated.variablesBelow next

example {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeParameterId}
    {dataType : ProgramDataSignature}
    (cataloged : dataType ∈ signatures.dataTypes)
    (noParameters : dataType.parameters = [])
    (next : Nat) :
    (Ty.nominal dataType.id []).VariablesBelow next := by
  have validated :
      SignatureTypeFormationValidated signatures owner parameters
        (Ty.nominal dataType.id []) :=
    .dataNominal dataType [] cataloged (by simp [noParameters]) .nil
  exact validated.variablesBelow next

example {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeParameterId}
    {dataType : ProgramDataSignature}
    (cataloged : dataType ∈ signatures.dataTypes)
    (noParameters : dataType.parameters = [])
    (next : Nat) :
    ∀ type ∈ [Ty.nominal dataType.id [],
        .function (.product Ty.word Ty.bool) Ty.unit],
      type.VariablesBelow next := by
  have validated :
      SignatureTypesFormationValidated signatures owner parameters
        [Ty.nominal dataType.id [],
          .function (.product Ty.word Ty.bool) Ty.unit] :=
    .cons
      (.dataNominal dataType [] cataloged (by simp [noParameters]) .nil)
      (.cons
        (.function (.product (.builtin .word) (.builtin .bool))
          (.builtin .unit))
        .nil)
  exact validated.variablesBelow next

end Tests.ProgramSignatureFormation
end

section
-- leanmerge: from Solcore.Test.ProgramSignatures
/-! Executable source-to-signature and source-to-impl-rule regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

namespace ProgramSignatures

private def boundedGenericScheme (owner : Resolved.DeclarationId) :
    ConstrainedDeclarationScheme :=
  let first : TypeSystem.TypeParameterId := { owner, index := 0 }
  let second : TypeSystem.TypeParameterId := { owner, index := 1 }
  {
    parameters := [first, second]
    predicates := []
    body := .function (.parameter first)
      (.product (.parameter second) .word)
  }

example (owner : Resolved.DeclarationId) (next : Nat) :
    next ≤ ((boundedGenericScheme owner).instantiate next).next :=
  ConstrainedDeclarationScheme.instantiate_next_le _ _

example (owner : Resolved.DeclarationId) (next : Nat) :
    ∀ {parameter replacement},
      (parameter, replacement) ∈
          ((boundedGenericScheme owner).instantiate next).parameterSubstitution →
        replacement.VariablesBelow
          ((boundedGenericScheme owner).instantiate next).next :=
  ConstrainedDeclarationScheme.instantiate_parameterSubstitution_range_variablesBelow
    _ _

example (owner : Resolved.DeclarationId) (next : Nat) :
    ((boundedGenericScheme owner).instantiate next).body.VariablesBelow
      ((boundedGenericScheme owner).instantiate next).next := by
  apply ConstrainedDeclarationScheme.instantiate_body_variablesBelow
  simp [boundedGenericScheme, TypeSystem.Ty.word]

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do
    throw (IO.userError label)

private def parsed (path content : String) : IO Syntax.ParsedFile := do
  let file : Syntax.SourceFile := {
    id := { origin := .main, path }
    content
  }
  match Syntax.Parser.parse file with
  | .error error =>
      throw (IO.userError s!"{path}: parser invariant: {reprStr error}")
  | .ok output => pure output.parsed

private def catalog (sources : List Syntax.ParsedFile) : IO ProgramEnvironment := do
  match buildProgramEnvironment sources with
  | .ok environment => pure environment
  | .error errors =>
      throw (IO.userError s!"environment failure: {reprStr errors}")

private def declarationNamed (environment : ProgramEnvironment)
    (name : String) : IO ProgramDeclaration := do
  match environment.declarations.find? fun declaration =>
      declaration.name == some name with
  | some declaration => pure declaration
  | none => throw (IO.userError s!"missing declaration {name}")

private def testSuccessfulCollection : IO Unit := do
  let source ← parsed "signatures.solc" (String.intercalate "\n" [
    "trait Eq<T> {}",
    "trait Convert<Subject, Target> {}",
    "enum Box<T> { Wrap(T) }",
    "impl<T> Convert<Box<T>, Word> where T: Eq {}",
    "function choose<T>(left: T, right: T) returns (T) where T: Eq { left }"
  ])
  let environment ← catalog [source]
  let eqTrait ← declarationNamed environment "Eq"
  let convertTrait ← declarationNamed environment "Convert"
  let box ← declarationNamed environment "Box"
  let choose ← declarationNamed environment "choose"
  let signatures ← match buildProgramSignatures environment with
    | .ok signatures => pure signatures
    | .error errors =>
        throw (IO.userError s!"signature failure: {reprStr errors}")
  assertTrue (decide (signatures.functions.length = 1 ∧
      signatures.implRules.length = 1 ∧ signatures.dataTypes.length = 1))
    "function/impl source collection changed"
  assertTrue (decide ((signatures.functionsNamed "choose").length = 1 ∧
      (signatures.localFunctionsNamed choose.id.moduleId "choose").length = 1))
    "overload-preserving function lookup changed"
  match signatures.functions with
  | [signature] =>
      let parameter : TypeSystem.Ty :=
        .parameter { owner := choose.id, index := 0 }
      assertTrue (decide (signature.parameterNames = ["left", "right"] ∧
          signature.parameterTypes = [parameter, parameter] ∧
          signature.returnTypes = [parameter] ∧
          signature.scheme.parameters = [{ owner := choose.id, index := 0 }] ∧
          signature.scheme.body = .function (.product parameter parameter) parameter))
        "resolved generic function scheme changed"
      match signature.scheme.predicates with
      | [predicate] =>
          assertTrue (decide (predicate.trait = .declaration eqTrait.id ∧
              predicate.subject = parameter ∧ predicate.arguments = []))
            "function where predicate changed"
      | predicates => throw (IO.userError
          s!"function predicates changed: {reprStr predicates}")
      let instantiated := signature.scheme.instantiate 7
      assertTrue (decide (instantiated.parameterSubstitution =
          [({ owner := choose.id, index := 0 }, .variable ⟨7⟩)] ∧
          instantiated.body =
          .function (.product (.variable ⟨7⟩) (.variable ⟨7⟩))
            (.variable ⟨7⟩) ∧
          instantiated.predicates = [{
            trait := eqTrait.id
            subject := .variable ⟨7⟩
            arguments := []
          }] ∧ instantiated.next = 8))
        "scheme instantiation did not share fresh variables"
  | functions => throw (IO.userError
      s!"function signatures changed: {reprStr functions}")
  match signatures.implRules with
  | [rule] =>
      let some implementation := rule.id.declaration?
        | throw (IO.userError "source impl rule lost its declaration identity")
      let parameter : TypeSystem.Ty :=
        .parameter { owner := implementation, index := 0 }
      assertTrue (decide (rule.id = .declaration implementation ∧
          rule.head.trait = .declaration convertTrait.id ∧
          rule.head.subject = TypeSystem.Ty.nominal box.id [parameter] ∧
          rule.head.arguments = [.word] ∧
          rule.wherePredicates = [{
            trait := .declaration eqTrait.id
            subject := parameter
            arguments := []
          }]))
        "impl head/where predicate resolution changed"
  | rules => throw (IO.userError s!"impl rules changed: {reprStr rules}")
  let dataType ← match signatures.dataType? box.id with
    | some dataType => pure dataType
    | none => throw (IO.userError "missing Box data signature")
  let dataParameter : TypeSystem.Ty :=
    .parameter { owner := box.id, index := 0 }
  match dataType.constructors with
  | [constructor] =>
      assertTrue (decide (dataType.name = "Box" ∧
          dataType.parameters = [{ owner := box.id, index := 0 }] ∧
          constructor.id = { dataType := box.id, constructorIndex := 0 } ∧
          constructor.name = "Wrap" ∧
          constructor.payloadTypes = [dataParameter]))
        "generic data constructor catalog changed"
  | constructors => throw (IO.userError
      s!"Box constructor catalog changed: {reprStr constructors}")

private def testContractCatalog : IO Unit := do
  let source ← parsed "contracts.solc" (String.intercalate "\n" [
    "contract Vault<T> {",
    "  enum Inner { Empty }",
    "  function keep(value: T) {}",
    "}",
    "enum Outside { Only }",
    "contract Registry {}"
  ])
  let environment ← catalog [source]
  let vault ← declarationNamed environment "Vault"
  let outside ← declarationNamed environment "Outside"
  let registry ← declarationNamed environment "Registry"
  let signatures ← match buildProgramSignatures environment with
    | .ok signatures => pure signatures
    | .error errors => throw (IO.userError
        s!"contract signature failure: {reprStr errors}")
  match signatures.contracts with
  | [vaultSignature, registrySignature] =>
      assertTrue (decide (
          vaultSignature.id = vault.id ∧
          vaultSignature.name = "Vault" ∧
          vaultSignature.parameters = [{ owner := vault.id, index := 0 }] ∧
          vaultSignature.source.value.members.length = 2 ∧
          registrySignature.id = registry.id ∧
          registrySignature.name = "Registry" ∧
          registrySignature.parameters = []))
        "contract catalog lost source order, identity, or generic scope"
  | contracts => throw (IO.userError
      s!"contract catalog changed: {reprStr contracts}")
  let catalogedVault ← match signatures.contract? vault.id with
    | some signature => pure signature
    | none => throw (IO.userError "contract identity lookup lost Vault")
  assertTrue (decide (catalogedVault.id = vault.id ∧
      catalogedVault.name = "Vault"))
    "contract identity lookup returned the wrong signature"
  match signatures.dataTypes with
  | [dataType] =>
      assertTrue (decide (dataType.id = outside.id ∧
          dataType.name = "Outside" ∧ signatures.functions.length = 0))
        "contract members leaked into top-level function/data catalogs"
  | dataTypes => throw (IO.userError
      s!"contract declarations entered the data catalog: {reprStr dataTypes}")

private def testDefaultImplementationMarkerCollection : IO Unit := do
  let source ← parsed "default_implementations.solc" (String.intercalate "\n" [
    "trait Select<T> {}",
    "default impl<T> Select<T> {}",
    "impl Select<Word> {}"
  ])
  let environment ← catalog [source]
  let signatures ← match buildProgramSignatures environment with
    | .ok signatures => pure signatures
    | .error errors => throw (IO.userError
        s!"default implementation signature failure: {reprStr errors}")
  match signatures.implementations, signatures.implRules with
  | [fallback, specific], [fallbackRule, specificRule] =>
      assertTrue (decide (
          fallback.isDefault ∧ fallback.source.value.defaultMarker.isSome ∧
          fallbackRule.isDefault ∧ fallbackRule.id = fallback.id ∧
          !specific.isDefault ∧ specific.source.value.defaultMarker.isNone ∧
          !specificRule.isDefault ∧ specificRule.id = specific.id))
        "default impl marker was not preserved by the signature/rule projection"
  | implementations, rules => throw (IO.userError
      s!"default implementation catalog changed: {reprStr implementations}; {reprStr rules}")

private def testComptimeMarkerCollection : IO Unit := do
  let source ← parsed "comptime_signatures.solc" (String.intercalate "\n" [
    "trait Stage<T> {",
    "  function stage(comptime value: T) returns (comptime<T>);",
    "}",
    "impl Stage<Word> {",
    "  function stage(comptime value: Word) returns (comptime<Word>) {",
    "    return value;",
    "  }",
    "}",
    "function choose<T>(comptime value: T, other: Word) returns (comptime<T>) {",
    "  return value;",
    "}"
  ])
  let environment ← catalog [source]
  let stage ← declarationNamed environment "Stage"
  let choose ← declarationNamed environment "choose"
  let signatures ← match buildProgramSignatures environment with
    | .ok signatures => pure signatures
    | .error errors => throw (IO.userError
        s!"comptime signature failure: {reprStr errors}")
  let chooseSignature ← match signatures.functions with
    | [signature] => pure signature
    | functions => throw (IO.userError
        s!"comptime function catalog changed: {reprStr functions}")
  let parameter : TypeSystem.Ty :=
    .parameter { owner := choose.id, index := 0 }
  assertTrue (decide (chooseSignature.parameterNames = ["value", "other"] ∧
      chooseSignature.parameterTypes = [parameter, .word] ∧
      chooseSignature.parameterComptime = [true, false] ∧
      chooseSignature.returnTypes = [parameter] ∧
      chooseSignature.returnComptime ∧
      chooseSignature.scheme.body =
        .function (.product parameter .word) parameter))
    "function comptime markers were dropped or embedded in semantic types"
  let traitSignature ← match signatures.trait? stage.id with
    | some signature => pure signature
    | none => throw (IO.userError "missing staged trait signature")
  let traitMethod ← match traitSignature.methods with
    | [method] => pure method
    | methods => throw (IO.userError
        s!"staged trait method catalog changed: {reprStr methods}")
  let traitParameter : TypeSystem.Ty :=
    .parameter { owner := stage.id, index := 0 }
  assertTrue (decide (traitMethod.parameterTypes = [traitParameter] ∧
      traitMethod.parameterComptime = [true] ∧
      traitMethod.returnTypes = [traitParameter] ∧
      traitMethod.returnComptime))
    "trait method comptime markers were not normalized"
  let implementation ← match signatures.implementations with
    | [implementation] => pure implementation
    | implementations => throw (IO.userError
        s!"staged implementation catalog changed: {reprStr implementations}")
  let implMethod ← match implementation.methods with
    | [method] => pure method
    | methods => throw (IO.userError
        s!"staged implementation method catalog changed: {reprStr methods}")
  let synthetic := implementation.functionSignatureOfMethod implMethod
  assertTrue (decide (implMethod.parameterTypes = [.word] ∧
      implMethod.parameterComptime = [true] ∧
      implMethod.returnTypes = [.word] ∧ implMethod.returnComptime ∧
      synthetic.parameterComptime = [true] ∧
      synthetic.returnComptime ∧
      synthetic.scheme.body = .function .word .word))
    "implementation method comptime markers did not reach its function view"

private def testBuiltinIntResolutionProfile : IO Unit := do
  let source ← parsed "source_int.solc" (String.intercalate "\n" [
    "trait Int<T> {}",
    "impl Int<Bool> {}"
  ])
  let environment ← catalog [source]
  let sourceTrait ← declarationNamed environment "Int"
  let signatures ← match buildProgramSignatures environment with
    | .ok signatures => pure signatures
    | .error errors =>
        throw (IO.userError s!"builtin Int profile failed: {reprStr errors}")
  let sourceRule ← match signatures.implRules with
    | [rule] => pure rule
    | rules => throw (IO.userError
        s!"source Int catalog changed: {reprStr rules}")
  let some sourceImplementation := sourceRule.id.declaration?
    | throw (IO.userError "source Int rule lost its declaration identity")
  assertTrue (decide (signatures.resolutionRules =
      [ProgramSignatures.builtinIntWordRule,
        ProgramSignatures.builtinIntIntegerRule, sourceRule] ∧
      signatures.traits.length = 1 ∧
      signatures.implementations.length = 1 ∧
      signatures.implRules.length = 1 ∧
      signatures.resolutionRules.length = 3))
    "combined resolution rules lost builtin-first order or source-only counts"
  let builtinWord := ProgramSignatures.builtinIntPredicate .word
  let builtinInteger := ProgramSignatures.builtinIntPredicate .integer
  let builtinBool := ProgramSignatures.builtinIntPredicate .bool
  let builtinFlexible := ProgramSignatures.builtinIntPredicate (.variable ⟨0⟩)
  let builtinExtraArgument : ProgramPredicate := {
    ProgramSignatures.builtinIntPredicate .word with
    arguments := [.bool]
  }
  let sourceBool : ProgramPredicate := {
    trait := sourceTrait.id
    subject := .bool
    arguments := []
  }
  match (TypedTraitResolution.resolve signatures.resolutionRules 1
      builtinWord).outcome with
  | .success (.byImpl goal (.builtin .intWord) []) =>
      assertTrue (decide (goal = builtinWord))
        "builtin Word evidence retained the wrong goal"
  | outcome => throw (IO.userError
      s!"builtin Int<Word> resolution changed: {reprStr outcome}")
  match (TypedTraitResolution.resolve signatures.resolutionRules 1
      builtinInteger).outcome with
  | .success (.byImpl goal (.builtin .intInteger) []) =>
      assertTrue (decide (goal = builtinInteger))
        "builtin integer evidence retained the wrong goal"
  | outcome => throw (IO.userError
      s!"builtin Int<integer> resolution changed: {reprStr outcome}")
  match (TypedTraitResolution.resolve signatures.resolutionRules 1
      builtinBool).outcome with
  | .noSolution => pure ()
  | outcome => throw (IO.userError
      s!"builtin Int<Bool> unexpectedly crossed into source Int: {reprStr outcome}")
  match (TypedTraitResolution.resolve signatures.resolutionRules 1
      builtinFlexible).outcome with
  | .noSolution => pure ()
  | outcome => throw (IO.userError
      s!"builtin Int rules defaulted a caller-owned variable: {reprStr outcome}")
  match (TypedTraitResolution.resolve signatures.resolutionRules 1
      builtinExtraArgument).outcome with
  | .noSolution => pure ()
  | outcome => throw (IO.userError
      s!"builtin Int accepted an extra argument: {reprStr outcome}")
  match (TypedTraitResolution.resolve signatures.resolutionRules 1
      sourceBool).outcome with
  | .success (.byImpl goal (.declaration implementation) []) =>
      assertTrue (decide (goal = sourceBool ∧ implementation = sourceImplementation))
        "source Int evidence retained the wrong tagged goal or implementation"
  | outcome => throw (IO.userError
      s!"source trait named Int did not remain resolvable: {reprStr outcome}")

private def testMethodCatalog : IO Unit := do
  let source ← parsed "methods.solc" (String.intercalate "\n" [
    "trait Marker<T> {}",
    "trait Add<T> where T: Marker {",
    "  function add(left: T, right: T) returns (T) where T: Marker;",
    "}",
    "impl Add<Word> where Word: Marker {",
    "  function add(left: Word, right: Word) returns (Word) where Word: Marker {",
    "    return left - right;",
    "  }",
    "}"
  ])
  let environment ← catalog [source]
  let marker ← declarationNamed environment "Marker"
  let add ← declarationNamed environment "Add"
  let implementation ← match environment.declarations.find? fun declaration =>
      declaration.kind == ProgramDeclarationKind.implementation with
    | some declaration => pure declaration
    | none => throw (IO.userError "missing Add implementation")
  let signatures ← match buildProgramSignatures environment with
    | .ok signatures => pure signatures
    | .error errors =>
        throw (IO.userError s!"method signature failure: {reprStr errors}")
  assertTrue (decide (signatures.traits.length = 2 ∧
      signatures.implementations.length = 1 ∧
      signatures.implRules.length = 1))
    "trait/implementation catalog sizes changed"
  let some traitSignature := signatures.trait? add.id
    | throw (IO.userError "missing Add trait signature")
  let traitParameter : TypeSystem.Ty :=
    .parameter { owner := add.id, index := 0 }
  assertTrue (decide (traitSignature.parameters =
      [{ owner := add.id, index := 0 }] ∧
      traitSignature.wherePredicates = [{
        trait := marker.id
        subject := traitParameter
        arguments := []
      }]))
    "trait parameters or declaration predicates changed"
  let traitMethod ← match traitSignature.methods with
    | [method] => pure method
    | methods => throw (IO.userError
        s!"trait method catalog changed: {reprStr methods}")
  assertTrue (decide (traitMethod.id = {
        trait := add.id
        methodIndex := 0
      } ∧ traitMethod.name = "add" ∧
      traitMethod.parameterNames = ["left", "right"] ∧
      traitMethod.parameterTypes = [traitParameter, traitParameter] ∧
      traitMethod.returnTypes = [traitParameter] ∧
      traitMethod.wherePredicates = [{
        trait := marker.id
        subject := traitParameter
        arguments := []
      }]))
    "resolved trait method signature changed"
  let some implementationSignature := signatures.implementation? implementation.id
    | throw (IO.userError "missing Add implementation signature")
  assertTrue (decide (implementationSignature.parameters = [] ∧
      implementationSignature.head = {
        trait := add.id
        subject := .word
        arguments := []
      } ∧ implementationSignature.wherePredicates = [{
        trait := marker.id
        subject := .word
        arguments := []
      }]))
    "implementation head or declaration predicates changed"
  let implMethod ← match implementationSignature.methods with
    | [method] => pure method
    | methods => throw (IO.userError
        s!"implementation method catalog changed: {reprStr methods}")
  assertTrue (decide (implMethod.id = {
        implementation := implementation.id
        methodIndex := 0
      } ∧ implMethod.traitMethod = traitMethod.id ∧
      implMethod.name = "add" ∧
      implMethod.parameterNames = ["left", "right"] ∧
      implMethod.parameterTypes = [.word, .word] ∧
      implMethod.returnTypes = [.word] ∧
      implMethod.wherePredicates = [{
        trait := marker.id
        subject := .word
        arguments := []
      }]))
    "resolved implementation method signature changed"
  assertTrue (decide ((signatures.traitMethod? traitMethod.id).isSome ∧
      (signatures.implMethod? implMethod.id).isSome))
    "role-tagged method lookup changed"
  let synthetic := implementationSignature.functionSignatureOfMethod implMethod
  assertTrue (decide (synthetic.id = implementation.id ∧
      synthetic.name = "add" ∧
      synthetic.parameterNames = ["left", "right"] ∧
      synthetic.parameterTypes = [.word, .word] ∧
      synthetic.returnTypes = [.word] ∧
      synthetic.scheme.parameters = [] ∧
      synthetic.scheme.predicates =
        implementationSignature.wherePredicates ++ implMethod.wherePredicates ∧
      synthetic.scheme.body = .function (.product .word .word) .word))
    "implementation method function projection changed"

private def expectSingleError (content : String)
    (accept : ProgramSignatureError → Bool) : IO Unit := do
  let source ← parsed "failure.solc" content
  let environment ← catalog [source]
  match buildProgramSignatures environment with
  | .error [error] =>
      assertTrue (accept error) s!"unexpected signature error: {reprStr error}"
  | result => throw (IO.userError s!"unexpected signature result: {reprStr result}")

private def testFailures : IO Unit := do
  expectSingleError
    "function duplicate<T>(left: T, left: T) { return; }"
    fun error => match error with
      | .duplicateFunctionParameter _ "left" 0 1 => true
      | _ => false
  expectSingleError
    "function duplicateGeneric<T, T>() { return; }"
    fun error => match error with
      | .typeResolution _ (.duplicateGenericParameter "T" 0 1) => true
      | _ => false
  expectSingleError
    "contract Duplicate<T, T> {}"
    fun error => match error with
      | .typeResolution _ (.duplicateGenericParameter "T" 0 1) => true
      | _ => false
  expectSingleError
    "function malformed(value) { return; }"
    fun error => match error with
      | .malformedFunctionParameter _ 0 => true
      | _ => false
  expectSingleError
    "function missing(value: Missing) { return; }"
    fun error => match error with
      | .typeResolution _ (.unknownTypeName ["Missing"]) => true
      | _ => false
  expectSingleError
    "function constrained<T>() where T: Missing { return; }"
    fun error => match error with
      | .unknownTrait _ "Missing" => true
      | _ => false
  expectSingleError (String.intercalate "\n" [
    "trait Convert<Subject, Target> {}",
    "function constrained<T>() where T: Convert { return; }"
  ]) fun error => match error with
    | .traitArityMismatch _ _ 2 1 => true
    | _ => false
  expectSingleError
    "function nested() returns (comptime<comptime<Word>>) { return 0; }"
    fun error => match error with
      | .nestedComptimeReturn _ 0 => true
      | _ => false
  expectSingleError
    "function mixed() returns (Word, comptime<Word>) { return (0, 0); }"
    fun error => match error with
      | .comptimeReturnMustBeSingleton _ 1 2 => true
      | _ => false
  expectSingleError
    "enum Duplicate { Same, Same(Word) }"
    fun error => match error with
      | .duplicateDataConstructor _ "Same" 0 1 => true
      | _ => false
  expectSingleError (String.intercalate "\n" [
    "trait Identity<T> {}",
    "impl<T, U> Identity<T> {}"
  ]) fun error => match error with
    | .implementationParameterNotInHead implementation parameter =>
        decide (parameter.owner = implementation ∧ parameter.index = 1)
    | _ => false
  expectSingleError (String.intercalate "\n" [
    "trait Marker<T> {}",
    "trait Required<T> where T: Marker {}",
    "impl Required<Word> {}"
  ]) fun error => match error with
    | .missingImplementationTraitPredicate implementation predicate =>
        match predicate.trait with
        | .declaration trait => decide (
            implementation.declarationIndex = 2 ∧
            trait.declarationIndex = 0 ∧
            trait.moduleId = implementation.moduleId ∧
            predicate.subject = .word ∧ predicate.arguments = [])
        | .builtin _ => false
    | _ => false

private def testTraitPredicateContainmentAllowsReorderingAndExtras : IO Unit := do
  let source ← parsed "predicates.solc"
    (String.intercalate "\n" [
      "trait First<T> {}",
      "trait Second<T> {}",
      "trait Extra<T> {}",
      "trait Required<T> where T: First, T: Second {}",
      "impl Required<Word> where Word: Extra, Word: Second, Word: First {}"
    ])
  let environment ← catalog [source]
  match buildProgramSignatures environment with
  | .ok signatures =>
      assertTrue (signatures.implementations.length == 1)
        "reordered required predicates plus an extra predicate changed collection"
  | .error errors => throw (IO.userError
      s!"valid reordered implementation predicates were rejected: {reprStr errors}")

private def testMethodFailures : IO Unit := do
  expectSingleError (String.intercalate "\n" [
    "trait Add<T> { function add(left: T, right: T) returns (T); }",
    "impl Add<Word> {}"
  ]) fun error => match error with
    | .missingImplMethod _ { methodIndex := 0, .. } "add" => true
    | _ => false
  expectSingleError (String.intercalate "\n" [
    "trait Add<T> {}",
    "impl Add<Word> {",
    "  function add(left: Word, right: Word) returns (Word) { return left; }",
    "}"
  ]) fun error => match error with
    | .extraImplMethod { methodIndex := 0, .. } "add" => true
    | _ => false
  expectSingleError (String.intercalate "\n" [
    "trait Add<T> { function add(left: T, right: T) returns (T); }",
    "impl Add<Word> {",
    "  function add(left: Bool, right: Bool) returns (Bool) { return left; }",
    "}"
  ]) fun error => match error with
    | .implMethodSignatureMismatch { methodIndex := 0, .. }
        { methodIndex := 0, .. } [.word, .word] [.bool, .bool]
        [.word] [.bool] => true
    | _ => false
  expectSingleError (String.intercalate "\n" [
    "trait Stage<T> {",
    "  function stage(comptime value: T) returns (comptime<T>);",
    "}",
    "impl Stage<Word> {",
    "  function stage(value: Word) returns (Word) { return value; }",
    "}"
  ]) fun error => match error with
    | .implMethodComptimeMismatch { methodIndex := 0, .. }
        { methodIndex := 0, .. } [true] [false] true false => true
    | _ => false
  expectSingleError (String.intercalate "\n" [
    "trait Marker<T> {}",
    "trait Add<T> {",
    "  function add(left: T, right: T) returns (T) where T: Marker;",
    "}",
    "impl Add<Word> {",
    "  function add(left: Word, right: Word) returns (Word) { return left; }",
    "}"
  ]) fun error => match error with
    | .implMethodPredicateMismatch { methodIndex := 0, .. }
        { methodIndex := 0, .. } [_] [] => true
    | _ => false
  expectSingleError (String.intercalate "\n" [
    "trait Add<T> { function add(value: T) returns (T); }",
    "impl Add<Word> {",
    "  function add(value: Word) returns (Word) { return value; }",
    "  function add(other: Word) returns (Word) { return other; }",
    "}"
  ]) fun error => match error with
    | .duplicateImplMethod _ "add" 0 1 => true
    | _ => false
  expectSingleError (String.intercalate "\n" [
    "trait Add<T> { function add<U>(value: T) returns (T); }",
    "impl Add<Word> {}"
  ]) fun error => match error with
    | .traitMethodLocalGenerics { methodIndex := 0, .. } => true
    | _ => false

private def testAmbiguousTrait : IO Unit := do
  let left ← parsed "left.solc" "export {Shared}; trait Shared<T> {}"
  let right ← parsed "right.solc" "export {Shared}; trait Shared<T> {}"
  let consumer ← parsed "consumer.solc" (String.intercalate "\n" [
    "import * from left;",
    "import * from right;",
    "function constrained<T>() where T: Shared { return; }"
  ])
  let environment ← catalog [left, right, consumer]
  match buildProgramSignatures environment with
  | .error [.ambiguousTrait _ "Shared" candidates] =>
      assertTrue (candidates.length == 2)
        "ambiguous trait candidates were not retained"
  | result => throw (IO.userError
      s!"ambiguous trait result changed: {reprStr result}")

private def testStrictTraitVisibility : IO Unit := do
  let provider ← parsed "provider.solc"
    "export {Hidden}; trait Hidden<T> {}"
  let unrelated ← parsed "unrelated.solc"
    "export {*}; enum Visible { Only }"
  let consumer ← parsed "consumer.solc" (String.intercalate "\n" [
    "import * from unrelated;",
    "function constrained<T>() where T: Hidden { return; }"
  ])
  let environment ← catalog [provider, unrelated, consumer]
  match buildProgramSignatures environment with
  | .error [.unknownTrait _ "Hidden"] => pure ()
  | result => throw (IO.userError
      s!"an unimported trait reached signature resolution: {reprStr result}")

end ProgramSignatures

/-- Run the first source-connected signature and trait-rule vertical slice. -/
def testProgramSignatures : IO Unit := do
  ProgramSignatures.testSuccessfulCollection
  ProgramSignatures.testContractCatalog
  ProgramSignatures.testDefaultImplementationMarkerCollection
  ProgramSignatures.testComptimeMarkerCollection
  ProgramSignatures.testBuiltinIntResolutionProfile
  ProgramSignatures.testMethodCatalog
  ProgramSignatures.testFailures
  ProgramSignatures.testTraitPredicateContainmentAllowsReorderingAndExtras
  ProgramSignatures.testMethodFailures
  ProgramSignatures.testAmbiguousTrait
  ProgramSignatures.testStrictTraitVisibility

end Tests
end

section
-- leanmerge: from Solcore.Test.ProgramTypeAliases
/-! Executable regressions for transparent whole-program type aliases. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

namespace ProgramTypeAliases

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def parsed (origin : Syntax.SourceOrigin) (path content : String) :
    IO Syntax.ParsedFile := do
  let file : Syntax.SourceFile := { id := { origin, path }, content }
  match Syntax.Parser.parse file with
  | .error error =>
      throw (IO.userError s!"{path}: parser invariant: {reprStr error}")
  | .ok output =>
      unless output.lexicalDiagnostics.isEmpty &&
          output.parseDiagnostics.isEmpty do
        throw (IO.userError
          s!"{path}: source diagnostics: {reprStr output.lexicalDiagnostics}; {reprStr output.parseDiagnostics}")
      pure output.parsed

private def build (sources : List Syntax.ParsedFile) : IO ProgramEnvironment := do
  match buildProgramEnvironment sources with
  | .ok environment => pure environment
  | .error errors =>
      throw (IO.userError s!"program environment failed: {reprStr errors}")

private def declaration (environment : ProgramEnvironment)
    (modulePath name : String) : IO ProgramDeclaration := do
  match environment.declarations.find? fun declaration =>
      declaration.id.moduleId.path.render == modulePath &&
        declaration.name == some name with
  | some declaration => pure declaration
  | none => throw (IO.userError s!"missing declaration {modulePath}.{name}")

private def aliasBody (declaration : ProgramDeclaration) : IO Syntax.TypeExpr := do
  match declaration.source.value with
  | .typeAlias alias => pure alias.value.value
  | _ => throw (IO.userError "selected declaration was not a type alias")

private def resolveAliasBodyResult (environment : ProgramEnvironment)
    (declaration : ProgramDeclaration) :
    IO (Except ProgramTypeResolutionError TypeSystem.Ty) := do
  let source ← aliasBody declaration
  pure (resolveProgramTypeAliasBody environment declaration source)

private def resolveAliasBody (environment : ProgramEnvironment)
    (modulePath name : String) : IO TypeSystem.Ty := do
  let selected ← declaration environment modulePath name
  match ← resolveAliasBodyResult environment selected with
  | .ok type => pure type
  | .error error =>
      throw (IO.userError s!"{modulePath}.{name} did not resolve: {reprStr error}")

private def testTransparentSubstitution : IO Unit := do
  let source ← parsed .main "aliases.solc" (String.intercalate "\n" [
    "enum Box<T> { Wrap(T) }",
    "type Id(T) = T;",
    "type Pair(A, B) = (A, B);",
    "type Reverse(A, B) = Pair<B, A>;",
    "type Boxed(T) = Box<Id<T>>;",
    "type UseId = Id<Word>;",
    "type UsePair = Reverse<Word, Bool>;",
    "type UseBox = Boxed<Bool>;"
  ])
  let environment ← build [source]
  let box ← declaration environment "aliases" "Box"
  let useId ← resolveAliasBody environment "aliases" "UseId"
  let usePair ← resolveAliasBody environment "aliases" "UsePair"
  let useBox ← resolveAliasBody environment "aliases" "UseBox"
  assertTrue (decide (useId = TypeSystem.Ty.word))
    "a generic identity alias remained nominal"
  assertTrue (decide (usePair =
      TypeSystem.Ty.product TypeSystem.Ty.bool TypeSystem.Ty.word))
    "nested aliases did not compose their parameter substitutions"
  assertTrue (decide (useBox = TypeSystem.Ty.nominal box.id [.bool]))
    "an alias nested in a nominal argument was not expanded"

private def testDefinitionSiteScope : IO Unit := do
  let provider ← parsed .main "base.solc" (String.intercalate "\n" [
    "enum Hidden { Provider }",
    "export {Hidden};"
  ])
  let alias ← parsed .main "alias.solc" (String.intercalate "\n" [
    "import {Hidden} from base;",
    "type PublicAlias = Hidden;",
    "export {PublicAlias};"
  ])
  let consumer ← parsed .main "consumer.solc" (String.intercalate "\n" [
    "import {PublicAlias} from alias;",
    "enum Hidden { Consumer }",
    "type Use = PublicAlias;"
  ])
  let environment ← build [provider, alias, consumer]
  let providerHidden ← declaration environment "base" "Hidden"
  let consumerHidden ← declaration environment "consumer" "Hidden"
  let use ← resolveAliasBody environment "consumer" "Use"
  assertTrue (decide (use = TypeSystem.Ty.nominal providerHidden.id []))
    "an alias did not retain its definition-site private import"
  assertTrue (decide (use ≠ TypeSystem.Ty.nominal consumerHidden.id []))
    "a use-site declaration captured an alias body"

private def testResolvedAliasPositions : IO Unit := do
  let source ← parsed .main "positions.solc" (String.intercalate "\n" [
    "type Scalar = Word;",
    "type Table = mapping(Scalar => Scalar);",
    "type Reference = @Scalar;",
    "type Staged = comptime<Scalar>;",
    "trait Marker<T> {}",
    "impl Marker<Scalar> {}",
    "function keep(value: Scalar) returns (Scalar) where Scalar: Marker {",
    "  return value;",
    "}"
  ])
  let environment ← build [source]
  let marker ← declaration environment "positions" "Marker"
  let table ← resolveAliasBody environment "positions" "Table"
  let reference ← resolveAliasBody environment "positions" "Reference"
  let staged ← resolveAliasBody environment "positions" "Staged"
  assertTrue (decide (table = TypeSystem.Ty.mapping .word .word ∧
      reference = TypeSystem.Ty.proxy .word ∧
      staged = TypeSystem.Ty.comptime .word))
    "aliases did not normalize inside mapping, proxy, or comptime types"
  let signatures ← match buildProgramSignatures environment with
    | .ok signatures => pure signatures
    | .error errors => throw (IO.userError
        s!"alias position signatures failed: {reprStr errors}")
  match signatures.functions, signatures.implRules with
  | [signature], [rule] =>
      assertTrue (decide (
          signature.parameterTypes = [.word] ∧
          signature.returnTypes = [.word] ∧
          signature.scheme.predicates = [{
            trait := .declaration marker.id
            subject := .word
            arguments := []
          }] ∧
          rule.head = {
            trait := .declaration marker.id
            subject := .word
            arguments := []
          }))
        "aliases did not normalize in a signature predicate or impl head"
  | functions, rules => throw (IO.userError
      s!"alias position catalogs changed: {reprStr functions}; {reprStr rules}")

private def testCycleDiagnostics : IO Unit := do
  let source ← parsed .main "cycles.solc" (String.intercalate "\n" [
    "type Direct = Direct;",
    "type Left = Right;",
    "type Right = Left;",
    "type UseMutual = Left;"
  ])
  let environment ← build [source]
  let direct ← declaration environment "cycles" "Direct"
  let left ← declaration environment "cycles" "Left"
  let right ← declaration environment "cycles" "Right"
  match ← resolveAliasBodyResult environment direct with
  | .error (.cyclicTypeAlias cycle) =>
      assertTrue (decide (cycle = [direct.id, direct.id]))
        "a direct alias cycle did not retain its closed declaration path"
  | result => throw (IO.userError
      s!"direct alias cycle result changed: {reprStr result}")
  let useMutual ← declaration environment "cycles" "UseMutual"
  match ← resolveAliasBodyResult environment useMutual with
  | .error (.cyclicTypeAlias cycle) =>
      assertTrue (decide (cycle = [left.id, right.id, left.id]))
        "a mutual alias cycle did not retain its closed declaration path"
  | result => throw (IO.userError
      s!"mutual alias cycle result changed: {reprStr result}")

private def testExpansionBudget : IO Unit := do
  let source ← parsed .main "fuel.solc" (String.intercalate "\n" [
    "type Base = Word;",
    "type Middle = Base;",
    "type Use = Middle;"
  ])
  let environment ← build [source]
  let use ← declaration environment "fuel" "Use"
  let body ← aliasBody use
  match resolveProgramTypeAliasBodyWithBudgets environment use 1 1 body with
  | .error .aliasExpansionLimit => pure ()
  | result => throw (IO.userError
      s!"independent alias expansion budget result changed: {reprStr result}")

private def testSharedNodeBudget : IO Unit := do
  let source ← parsed .main "branching_fuel.solc" (String.intercalate "\n" [
    "type Base = Word;",
    "type Pair = (Base, Base);",
    "type Quad = (Pair, Pair);",
    "type Use = Quad;"
  ])
  let environment ← build [source]
  let use ← declaration environment "branching_fuel" "Use"
  let body ← aliasBody use
  match resolveProgramTypeAliasBodyWithBudgets environment use 16 8 body with
  | .error .aliasExpansionLimit => pure ()
  | result => throw (IO.userError
      s!"branching aliases did not share their node budget: {reprStr result}")
  match resolveProgramTypeAliasBodyWithBudgets environment use 16 32 body with
  | .ok type =>
      let pair := TypeSystem.Ty.product .word .word
      assertTrue (decide (type = TypeSystem.Ty.product pair pair))
        "branching alias normalization changed below its node budget"
  | .error error => throw (IO.userError
      s!"branching aliases exhausted a sufficient budget: {reprStr error}")

private def testDefaultEagerExpansionBudget : IO Unit := do
  let source ← parsed .main "default_fuel.solc" (String.intercalate "\n" [
    "type T0 = Word;",
    "type T1 = (T0, T0);",
    "type T2 = (T1, T1);",
    "type T3 = (T2, T2);",
    "type T4 = (T3, T3);",
    "type T5 = (T4, T4);",
    "type T6 = (T5, T5);",
    "type T7 = (T6, T6);",
    "type T8 = (T7, T7);",
    "type T9 = (T8, T8);",
    "type T10 = (T9, T9);",
    "type T11 = (T10, T10);",
    "type T12 = (T11, T11);",
    "type T13 = (T12, T12);"
  ])
  let environment ← build [source]
  let terminal ← declaration environment "default_fuel" "T13"
  match buildProgramSignatures environment with
  | .error [.typeResolution id .aliasExpansionLimit] =>
      assertTrue (decide (id = terminal.id))
        "default alias node-budget failure lost its declaration owner"
  | result => throw (IO.userError
      s!"default eager alias budget result changed: {reprStr result}")

private def testUnusedAliasValidation : IO Unit := do
  let source ← parsed .main "invalid_aliases.solc" (String.intercalate "\n" [
    "type Id(T) = T;",
    "type Duplicate(T, T) = T;",
    "type Missing = Absent;",
    "type WrongArity = Id;",
    "type TooMany = Id<Word, Bool>;",
    "type Direct = Direct;",
    "type Left = Right;",
    "type Right = Left;"
  ])
  let environment ← build [source]
  let duplicate ← declaration environment "invalid_aliases" "Duplicate"
  let missing ← declaration environment "invalid_aliases" "Missing"
  let wrongArity ← declaration environment "invalid_aliases" "WrongArity"
  let tooMany ← declaration environment "invalid_aliases" "TooMany"
  let direct ← declaration environment "invalid_aliases" "Direct"
  let left ← declaration environment "invalid_aliases" "Left"
  let right ← declaration environment "invalid_aliases" "Right"
  match buildProgramSignatures environment with
  | .error [
      .typeResolution duplicateId
        (.duplicateGenericParameter "T" 0 1),
      .typeResolution missingId (.unknownTypeName ["Absent"]),
      .typeResolution wrongArityId (.typeArityMismatch ["Id"] 1 0),
      .typeResolution tooManyId (.typeArityMismatch ["Id"] 1 2),
      .typeResolution directId (.cyclicTypeAlias directCycle),
      .typeResolution leftId (.cyclicTypeAlias leftCycle),
      .typeResolution rightId (.cyclicTypeAlias rightCycle)
    ] =>
      assertTrue (decide (
          duplicateId = duplicate.id ∧
          missingId = missing.id ∧
          wrongArityId = wrongArity.id ∧
          tooManyId = tooMany.id ∧
          directId = direct.id ∧
          leftId = left.id ∧
          rightId = right.id ∧
          directCycle = [direct.id, direct.id] ∧
          leftCycle = [left.id, right.id, left.id] ∧
          rightCycle = [right.id, left.id, right.id]))
        "unused alias diagnostics lost declaration order or cycle paths"
  | result => throw (IO.userError
      s!"unused alias validation result changed: {reprStr result}")

end ProgramTypeAliases

/-- Run transparent type-alias expansion and diagnostic regressions. -/
def testProgramTypeAliases : IO Unit := do
  ProgramTypeAliases.testTransparentSubstitution
  ProgramTypeAliases.testDefinitionSiteScope
  ProgramTypeAliases.testResolvedAliasPositions
  ProgramTypeAliases.testCycleDiagnostics
  ProgramTypeAliases.testExpansionBudget
  ProgramTypeAliases.testSharedNodeBudget
  ProgramTypeAliases.testDefaultEagerExpansionBudget
  ProgramTypeAliases.testUnusedAliasValidation

end Tests
end

section
-- leanmerge: from Solcore.Test.TraitResolution
set_option autoImplicit false

namespace Tests.TraitResolution

open Solcore.Frontend.TraitResolution

inductive TestTrait where
  | show
  | equality
  | loop
  deriving Repr, BEq, DecidableEq

inductive TestTy where
  | int
  | bool
  | wildcard
  deriving Repr, BEq, DecidableEq

abbrev TestPredicate := Predicate TestTrait TestTy
abbrev TestRule := ImplRule TestTrait TestTy Nat
abbrev TestProgram := Program TestTrait TestTy Nat

private abbrev obligation (trait : TestTrait) (subject : TestTy) : TestPredicate :=
  { trait := trait, subject := subject, arguments := [] }

private abbrev eqInt := obligation .equality .int
private abbrev eqBool := obligation .equality .bool
private abbrev showInt := obligation .show .int
private abbrev showBool := obligation .show .bool
private abbrev loopInt := obligation .loop .int

private abbrev exactProgram (rules : List TestRule) : TestProgram :=
  { rules := rules, matchHead := exactHeadMatcher }

private abbrev eqIntRule (id : Nat := 0) : TestRule :=
  { id := id, head := eqInt, wherePredicates := [] }

private abbrev showIntRule (id : Nat := 1) (premises : List TestPredicate := [eqInt]) : TestRule :=
  { id := id, head := showInt, wherePredicates := premises }

private abbrev defaultShowIntRule (id : Nat)
    (premises : List TestPredicate := []) : TestRule :=
  { id := id
    head := showInt
    wherePredicates := premises
    isDefault := true }

theorem exact_head_and_where_predicate_produce_nested_evidence :
    (match (resolve (exactProgram [eqIntRule, showIntRule]) 2 showInt).outcome with
    | .success (.byImpl actualGoal 1 [.byImpl actualPremise 0 []]) =>
        actualGoal == showInt && actualPremise == eqInt
    | _ => false) = true := by
  decide

theorem missing_impl_is_a_definite_no_solution :
    (resolve (exactProgram [eqIntRule]) 2 showBool).outcome ==
      .noSolution := by
  rfl

theorem exhausted_depth_is_inconclusive :
    (resolve (exactProgram [eqIntRule, showIntRule]) 1 showInt).outcome ==
      .inconclusive (.depthLimit eqInt) := by
  rfl

private abbrev loopRule : TestRule :=
  { id := 4, head := loopInt, wherePredicates := [loopInt] }

theorem an_active_recursive_goal_is_an_inconclusive_cycle :
    (resolve (exactProgram [loopRule]) 8 loopInt).outcome ==
      .inconclusive (.cycle loopInt) := by
  rfl

theorem two_successful_impls_are_explicitly_ambiguous :
    (resolve (exactProgram [showIntRule 10 [], showIntRule 11 []]) 1 showInt).outcome ==
      .inconclusive (.ambiguous showInt 10 11) := by
  rfl

theorem one_success_does_not_hide_an_inconclusive_competitor :
    (resolve (exactProgram [showIntRule 10 [], showIntRule 11 [loopInt], loopRule]) 8 showInt).outcome ==
      .inconclusive (.incompleteCandidates showInt 10) := by
  rfl

theorem an_ordinary_success_wins_even_when_a_default_is_declared_first :
    (match (resolve
      (exactProgram [defaultShowIntRule 30, showIntRule 31 []]) 1 showInt).outcome with
    | .success (.byImpl actualGoal 31 []) => actualGoal == showInt
    | _ => false) = true := by
  decide

theorem an_ordinary_success_does_not_expand_default_premises :
    (let report := resolve (exactProgram
      [defaultShowIntRule 41 [loopInt], showIntRule 42 [], loopRule]) 8 showInt
    (match report.outcome with
      | .success (.byImpl actualGoal 42 []) => actualGoal == showInt
      | _ => false) && report.statistics.expandedGoals == 1) = true := by
  decide

theorem ordinary_premise_no_solution_falls_back_to_default :
    (match (resolve
      (exactProgram [showIntRule 32 [eqBool], defaultShowIntRule 33]) 2 showInt).outcome with
    | .success (.byImpl actualGoal 33 []) => actualGoal == showInt
    | _ => false) = true := by
  decide

theorem ordinary_inconclusive_search_blocks_default_fallback :
    (resolve (exactProgram
      [showIntRule 34 [loopInt], defaultShowIntRule 35, loopRule]) 8 showInt).outcome ==
      .inconclusive (.cycle loopInt) := by
  rfl

theorem ordinary_tier_ambiguity_blocks_default_fallback :
    (resolve (exactProgram
      [defaultShowIntRule 36, showIntRule 37 [], showIntRule 38 []]) 1 showInt).outcome ==
      .inconclusive (.ambiguous showInt 37 38) := by
  rfl

theorem default_tier_retains_existing_ambiguity_check :
    (resolve (exactProgram
      [defaultShowIntRule 39, defaultShowIntRule 40]) 1 showInt).outcome ==
      .inconclusive (.ambiguous showInt 39 40) := by
  rfl

private abbrev sharedPremiseProgram : TestProgram :=
  exactProgram [eqIntRule, showIntRule 1 [eqInt, eqInt]]

theorem completed_goals_are_tabled_across_sibling_predicates :
    ((match (resolve sharedPremiseProgram 2 showInt).outcome with
      | .success (.byImpl actualGoal 1 [
          .byImpl firstPremise 0 [],
          .byImpl secondPremise 0 []]) =>
            actualGoal == showInt && firstPremise == eqInt && secondPremise == eqInt
      | _ => false) &&
    (resolve sharedPremiseProgram 2 showInt).statistics.expandedGoals == 2 &&
    (resolve sharedPremiseProgram 2 showInt).statistics.memoHits == 1) = true := by
  decide

private abbrev instantiateWildcard (replacement : TestTy)
    (predicate : TestPredicate) : TestPredicate :=
  { predicate with
    subject := if predicate.subject == .wildcard then replacement else predicate.subject
    arguments := predicate.arguments.map fun argument =>
      if argument == .wildcard then replacement else argument }

/-- Tiny stand-in for the forthcoming unification boundary: a wildcard impl head
matches any subject and instantiates every wildcard in its where predicates. -/
private abbrev wildcardMatcher : HeadMatcher TestTrait TestTy Nat :=
  fun rule goal =>
    if rule.head.trait == goal.trait && rule.head.arguments == goal.arguments then
      if rule.head.subject == .wildcard then
        some (rule.wherePredicates.map (instantiateWildcard goal.subject))
      else if rule.head.subject == goal.subject then
        some rule.wherePredicates
      else
        none
    else
      none

private abbrev genericShowRule : TestRule :=
  { id := 20
    head := obligation .show .wildcard
    wherePredicates := [obligation .equality .wildcard] }

private abbrev wildcardProgram : TestProgram :=
  { rules := [eqIntRule 21, genericShowRule], matchHead := wildcardMatcher }

theorem a_head_matcher_can_instantiate_where_predicates :
    ((match (resolve wildcardProgram 2 showInt).outcome with
      | .success (.byImpl actualGoal 20 [.byImpl actualPremise 21 []]) =>
          actualGoal == showInt && actualPremise == eqInt
      | _ => false) &&
    (match (resolve wildcardProgram 2 showBool).outcome with
      | .noSolution => true
      | _ => false) &&
    eqBool == instantiateWildcard .bool (obligation .equality .wildcard)) = true := by
  decide

end Tests.TraitResolution
end

section
-- leanmerge: from Solcore.Test.TraitResolutionEvidenceEquality
/-! Finite comparison tests preserve the previous derived comparison order and
outcomes, including nested premises and the three independently compared fields. -/
set_option autoImplicit false
namespace Tests.TraitResolutionEvidenceEquality
open Solcore.Frontend.TraitResolution
abbrev Proof := Evidence Nat Nat Nat

def leaf (goal implementation : Nat) : Proof := .byImpl ⟨goal, goal + 1, [goal + 2]⟩ implementation []
def nest : Nat → Proof → Proof
  | 0, proof => proof
  | depth + 1, proof => .byImpl ⟨depth, 0, []⟩ depth [leaf depth depth, nest depth proof]

/-- The law holds for any finite tree, not just the test depths. -/
theorem reflects (left right : Proof) (accepted : (left == right) = true) : left = right := eq_of_beq accepted

theorem reflexive (value : Proof) : (value == value) = true := by simp

theorem deep_same (depth : Nat) : (nest depth (leaf 1 2) == nest depth (leaf 1 2)) = true := by simp

private inductive Previous where
  | byImpl (goal : Predicate Nat Nat) (implementation : Nat) (premises : List Previous)
  deriving BEq

private def previous : Proof → Previous
  | .byImpl goal implementation premises => .byImpl goal implementation (premises.map previous)

private def check (name : String) (left right : Proof) (expected : Bool) : IO Unit := do
  let actual := left == right
  unless actual == expected do throw (IO.userError s!"Evidence comparison {name}: unexpected result")
  unless actual == (previous left == previous right) do
    throw (IO.userError s!"Evidence comparison {name}: changed previous comparison")

def run : IO Unit := do
  check "empty premises" (leaf 1 2) (leaf 1 2) true
  check "goal" (leaf 1 2) (leaf 2 2) false
  check "implementation" (leaf 1 2) (leaf 1 3) false
  check "subject" (leaf 1 2) (.byImpl ⟨1, 7, [3]⟩ 2 []) false
  check "goal arguments" (leaf 1 2) (.byImpl ⟨1, 2, [4]⟩ 2 []) false
  check "ordered premises" (.byImpl ⟨0, 0, []⟩ 0 [leaf 1 1, leaf 2 2])
    (.byImpl ⟨0, 0, []⟩ 0 [leaf 2 2, leaf 1 1]) false
  check "premise length" (.byImpl ⟨0, 0, []⟩ 0 [leaf 1 1]) (.byImpl ⟨0, 0, []⟩ 0 []) false
  check "deep equality" (nest 128 (leaf 1 2)) (nest 128 (leaf 1 2)) true
  check "deep difference" (nest 128 (leaf 1 2)) (nest 128 (leaf 1 3)) false
  IO.println "[PASS] structural evidence equality"
end Tests.TraitResolutionEvidenceEquality
end
