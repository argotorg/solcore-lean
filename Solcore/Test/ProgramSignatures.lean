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
          assertTrue (decide (predicate.trait = eqTrait.id ∧
              predicate.subject = parameter ∧ predicate.arguments = []))
            "function where predicate changed"
      | predicates => throw (IO.userError
          s!"function predicates changed: {reprStr predicates}")
      let instantiated := signature.scheme.instantiate 7
      assertTrue (decide (instantiated.body =
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
      let parameter : TypeSystem.Ty :=
        .parameter { owner := rule.id, index := 0 }
      assertTrue (decide (rule.head.trait = convertTrait.id ∧
          rule.head.subject = TypeSystem.Ty.nominal box.id [parameter] ∧
          rule.head.arguments = [.word] ∧
          rule.wherePredicates = [{
            trait := eqTrait.id
            subject := parameter
            arguments := []
          }]))
        "impl head/where predicate resolution changed"
  | rules => throw (IO.userError s!"impl rules changed: {reprStr rules}")

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
  ProgramSignatures.testFailures
  ProgramSignatures.testAmbiguousTrait

end Tests
