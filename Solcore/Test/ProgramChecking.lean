import Solcore.Frontend.ProgramChecking

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
