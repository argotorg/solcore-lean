import Solcore.Syntax.Parser
import Solcore.Frontend.ProgramSignatures

/-! Executable source-to-signature and source-to-impl-rule regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

namespace ProgramSignatures

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
      signatures.implRules.length = 1))
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
  let left ← parsed "left.solc" "trait Shared<T> {}"
  let right ← parsed "right.solc" "trait Shared<T> {}"
  let consumer ← parsed "consumer.solc"
    "function constrained<T>() where T: Shared { return; }"
  let environment ← catalog [left, right, consumer]
  match buildProgramSignatures environment with
  | .error [.ambiguousTrait _ "Shared" candidates] =>
      assertTrue (candidates.length == 2)
        "ambiguous trait candidates were not retained"
  | result => throw (IO.userError
      s!"ambiguous trait result changed: {reprStr result}")

end ProgramSignatures

/-- Run the first source-connected signature and trait-rule vertical slice. -/
def testProgramSignatures : IO Unit := do
  ProgramSignatures.testSuccessfulCollection
  ProgramSignatures.testMethodCatalog
  ProgramSignatures.testFailures
  ProgramSignatures.testMethodFailures
  ProgramSignatures.testAmbiguousTrait

end Tests
