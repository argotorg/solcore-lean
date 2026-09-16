import Solcore.Syntax.Parser
import Solcore.Frontend.ProgramInterfaces

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

private def testExplicitErrors : IO Unit := do
  let unsupported ← parsed "unsupported.solc" (String.intercalate "\n" [
    "enum Choice { One }",
    "export {Choice(*), (==)};"
  ])
  let unsupportedEnvironment ← environment [unsupported]
  let unsupportedId ← moduleId unsupportedEnvironment "unsupported"
  match buildProgramInterfaces unsupportedEnvironment with
  | .error [.unsupportedConstructorExport owner "Choice",
      .unsupportedOperatorExport operatorOwner "=="] =>
      assertTrue (decide (owner = unsupportedId ∧ operatorOwner = unsupportedId))
        "unsupported export errors lost their owner"
  | result => throw (IO.userError
      s!"unsupported selector result changed: {reprStr result}")
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
  ProgramInterfaces.testExplicitErrors

end Tests
