import Solcore.Syntax.Parser
import Solcore.Frontend.ProgramTypeResolution

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

private def environment : IO ProgramEnvironment := do
  let types ← parsed .main "types.solc" (String.intercalate "\n" [
    "enum Box<T> { Wrap(T) }",
    "trait Show<T> {}",
    "type Identity(T) = T;",
    "type Applied(T) = T<Word>;",
    "type Local = Box<Word>;",
    "type Callable = function(Box<Word>) returns (Bool);"
  ])
  let models ← parsed .main "models.solc" (String.intercalate "\n" [
    "type Qualified = types.Box<Bool>;",
    "type Fallback = Box<word>;",
    "type External = dep.containers.Remote;",
    "type Tupled = (unit, Bool, Word);",
    "type WrongArity = Box;",
    "type MissingAlias = Missing;"
  ])
  let dependency ← parsed (.external "dep") "containers.solc"
    "enum Remote { One }"
  match buildProgramEnvironment [types, models, dependency] with
  | .ok result => pure result
  | .error errors =>
      throw (IO.userError s!"environment rejected valid sources: {reprStr errors}")

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
  let fallback ← resolvedAlias environment "models" "Fallback"
  assertTrue (decide (fallback = TypeSystem.Ty.nominal box.id [.word]))
    "unique whole-program fallback did not resolve"
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
  let left ← parsed .main "left.solc" "enum Shared { Left }"
  let right ← parsed .main "right.solc" "enum Shared { Right }"
  let consumer ← parsed .main "consumer.solc" "type Use = Shared;"
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
  ProgramEnvironmentAndTypeResolution.expectEnvironmentFailures

end Tests
