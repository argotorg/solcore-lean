import Solcore.Frontend.ExecutableImplMethods
import Solcore.Frontend.SourceCoreElaboration

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
