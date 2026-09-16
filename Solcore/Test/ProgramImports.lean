import Solcore.Syntax.Parser
import Solcore.Frontend.ProgramTypeResolution

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
