import Solcore.Frontend.SourceInference

/-!
Focused end-to-end checks for constructor visibility at the source-inference
boundary.  These phase-eight regressions run from the aggregate test suite.
-/

set_option autoImplicit false

namespace Tests.SourceConstructorVisibility

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace (entry : String)
    (sources : List (String × String)) : Workspace.RawWorkspace := {
  entry
  mainSources := sources.map fun source => {
    path := source.1
    content := source.2
  }
  externalLibraries := []
}

private def workspaceWithExternal (entry : String)
    (sources : List (String × String)) (externalName : String)
    (externalSources : List (String × String)) : Workspace.RawWorkspace := {
  entry
  mainSources := sources.map fun source => {
    path := source.1
    content := source.2
  }
  externalLibraries := [{
    name := externalName
    sources := externalSources.map fun source => {
      path := source.1
      content := source.2
    }
  }]
}

private def expectAccepted (label entry : String)
    (sources : List (String × String)) : IO Unit := do
  match loadAndCheckProgram (workspace entry sources) with
  | .ok _ => pure ()
  | .error errors => throw (IO.userError
      s!"{label} was rejected: {reprStr errors}")

private def expectUnknownConstructor (label entry : String)
    (sources : List (String × String)) (qualifiers : List String)
    (name : String) : IO Unit := do
  match loadAndCheckProgram (workspace entry sources) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body failure =>
            failure.error == .unknownConstructor qualifiers name
        | _ => false)
        s!"{label} reported the wrong failure: {reprStr errors}"
  | .ok _ => throw (IO.userError
      s!"{label} exposed a hidden constructor")

private def expectBodyError (label : String)
    (workspace : Workspace.RawWorkspace) (accept : Error → Bool) : IO Unit := do
  match loadAndCheckProgram workspace with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body failure => accept failure.error
        | _ => false)
        s!"{label} reported the wrong failure: {reprStr errors}"
  | .ok _ => throw (IO.userError s!"{label} was unexpectedly accepted")

private def testLocalAndImportedVisibility : IO Unit := do
  expectAccepted "local defining module" "local.solc" [
    ("local.solc", String.intercalate "\n" [
      "enum Box { Wrap(Word) }",
      "export {Box};",
      "function local(value: Word) returns (Box) { return Box.Wrap(value); }"
    ])
  ]
  let opaqueProvider := String.intercalate "\n" [
    "enum Box { Empty, Wrap(Word) }",
    "export {Box};"
  ]
  let opaqueConsumer := String.intercalate "\n" [
    "import provider;",
    "function bad(value: Word) returns (provider.Box) {",
    "  return provider.Box.Wrap(value);",
    "}"
  ]
  expectUnknownConstructor "opaque named export" "consumer.solc"
    [("provider.solc", opaqueProvider), ("consumer.solc", opaqueConsumer)]
    ["provider", "Box"] "Wrap"
  let visibleProvider := String.intercalate "\n" [
    "enum Box { Empty, Wrap(Word) }",
    "export {Box(Wrap)};"
  ]
  let visibleConsumer := String.intercalate "\n" [
    "import provider;",
    "function good(value: Word) returns (provider.Box) {",
    "  return provider.Box.Wrap(value);",
    "}"
  ]
  expectAccepted "selected imported constructor" "consumer.solc"
    [("provider.solc", visibleProvider), ("consumer.solc", visibleConsumer)]
  let selectedConsumer := String.intercalate "\n" [
    "import {Box} from provider;",
    "function good(value: Word) returns (Box) { return Box.Wrap(value); }"
  ]
  expectAccepted "unqualified selected type import" "selected.solc"
    [("provider.solc", visibleProvider), ("selected.solc", selectedConsumer)]
  expectUnknownConstructor "opaque unqualified selected type import"
    "selected.solc"
    [("provider.solc", opaqueProvider), ("selected.solc", selectedConsumer)]
    ["Box"] "Wrap"

private def testSubsetAndContextualVisibility : IO Unit := do
  let provider := String.intercalate "\n" [
    "enum Choice { Shown(Word), Hidden(Word) }",
    "export {Choice(Shown)};"
  ]
  let hidden := String.intercalate "\n" [
    "import provider;",
    "function bad(value: Word) returns (provider.Choice) {",
    "  return provider.Choice.Hidden(value);",
    "}"
  ]
  expectUnknownConstructor "unselected explicit constructor" "hidden.solc"
    [("provider.solc", provider), ("hidden.solc", hidden)]
    ["provider", "Choice"] "Hidden"
  let contextual := String.intercalate "\n" [
    "import provider;",
    "function bad(value: Word) returns (provider.Choice) {",
    "  return .Hidden(value);",
    "}"
  ]
  expectUnknownConstructor "unselected contextual constructor" "contextual.solc"
    [("provider.solc", provider), ("contextual.solc", contextual)] [] "Hidden"

private def testReExportVisibility : IO Unit := do
  let provider := String.intercalate "\n" [
    "enum Box { Wrap(Word) }",
    "export {Box(*)};"
  ]
  let consumer := String.intercalate "\n" [
    "import facade;",
    "function use(value: Word) returns (facade.Box) {",
    "  return facade.Box.Wrap(value);",
    "}"
  ]
  expectAccepted "wildcard re-export" "consumer.solc" [
    ("provider.solc", provider),
    ("facade.solc", "export provider.*;"),
    ("consumer.solc", consumer)
  ]
  expectUnknownConstructor "named re-export" "consumer.solc" [
    ("provider.solc", provider),
    ("facade.solc", "export provider.{Box};"),
    ("consumer.solc", consumer)
  ] ["facade", "Box"] "Wrap"

private def testAliasConstructorBoundary : IO Unit := do
  expectAccepted "contextual constructor through transparent alias" "main.solc" [
    ("main.solc", String.intercalate "\n" [
      "enum Box<T> { Wrap(T) }",
      "type WordBox = Box<Word>;",
      "function good(value: Word) returns (WordBox) { return .Wrap(value); }"
    ])
  ]
  let qualifiedAlias := workspace "main.solc" [
    ("main.solc", String.intercalate "\n" [
      "enum Box<T> { Wrap(T) }",
      "type WordBox = Box<Word>;",
      "function bad(value: Word) returns (WordBox) {",
      "  return WordBox.Wrap(value);",
      "}"
    ])
  ]
  expectBodyError "type alias constructor namespace" qualifiedAlias fun error =>
    match error with
    | .unsupportedExpression kind => kind == "field"
    | _ => false

  let provider := String.intercalate "\n" [
    "enum Box<T> { Wrap(T), Hidden(T) }",
    "type WordBox = Box<Word>;",
    "export {Box(Wrap), WordBox};"
  ]
  let imported := String.intercalate "\n" [
    "import {Box, WordBox} from provider;",
    "function good(value: Word) returns (WordBox) { return .Wrap(value); }"
  ]
  expectAccepted "imported contextual constructor through transparent alias"
    "imported.solc" [("provider.solc", provider), ("imported.solc", imported)]
  let hidden := String.intercalate "\n" [
    "import {Box, WordBox} from provider;",
    "function bad(value: Word) returns (WordBox) { return .Hidden(value); }"
  ]
  expectUnknownConstructor "hidden constructor through imported alias"
    "hidden.solc" [("provider.solc", provider), ("hidden.solc", hidden)]
    [] "Hidden"
  let aliasOnly := String.intercalate "\n" [
    "import {WordBox} from provider;",
    "function bad(value: Word) returns (WordBox) { return .Wrap(value); }"
  ]
  expectUnknownConstructor "alias import without constructor visibility"
    "alias_only.solc"
    [("provider.solc", provider), ("alias_only.solc", aliasOnly)] [] "Wrap"

private def testCanonicalPathDoesNotBypassImports : IO Unit := do
  let provider :=
    "enum Box { Wrap(Word) } export {Box(*)};"
  let consumer := String.intercalate "\n" [
    "function bad(value: Word) returns (Word) {",
    "  return provider.Box.Wrap(value);",
    "}"
  ]
  expectBodyError "unimported canonical constructor path"
    (workspace "consumer.solc" [
      ("provider.solc", provider), ("consumer.solc", consumer)
    ]) fun error =>
      error == .unsupportedExpression "field"

private def testLibraryIdentityIsolation : IO Unit := do
  let mainProvider :=
    "enum Box { MainOnly } export {Box(MainOnly)};"
  let externalProvider :=
    "enum Box { ExternalOnly } export {Box(ExternalOnly)};"
  let accepted := String.intercalate "\n" [
    "import * as Main from shared;",
    "import * as Ext from @dep.shared;",
    "function mainBox() returns (Main.Box) { return Main.Box.MainOnly; }",
    "function externalBox() returns (Ext.Box) { return Ext.Box.ExternalOnly; }"
  ]
  let acceptedWorkspace := workspaceWithExternal "accepted.solc"
    [("shared.solc", mainProvider), ("accepted.solc", accepted)] "dep"
    [("shared.solc", externalProvider)]
  match loadAndCheckProgram acceptedWorkspace with
  | .ok _ => pure ()
  | .error errors => throw (IO.userError
      s!"same-path library-local constructors were rejected: {reprStr errors}")
  let leaked := String.intercalate "\n" [
    "import * as Main from shared;",
    "import * as Ext from @dep.shared;",
    "function bad() returns (Main.Box) { return Main.Box.ExternalOnly; }"
  ]
  let leakedWorkspace := workspaceWithExternal "leaked.solc"
    [("shared.solc", mainProvider), ("leaked.solc", leaked)] "dep"
    [("shared.solc", externalProvider)]
  expectBodyError "main/external constructor visibility isolation"
    leakedWorkspace fun error =>
      error == .unknownConstructor ["Main", "Box"] "ExternalOnly"
  let reverseLeak := String.intercalate "\n" [
    "import * as Main from shared;",
    "import * as Ext from @dep.shared;",
    "function bad() returns (Ext.Box) { return Ext.Box.MainOnly; }"
  ]
  let reverseLeakWorkspace := workspaceWithExternal "reverse.solc"
    [("shared.solc", mainProvider), ("reverse.solc", reverseLeak)] "dep"
    [("shared.solc", externalProvider)]
  expectBodyError "external/main constructor visibility isolation"
    reverseLeakWorkspace fun error =>
      error == .unknownConstructor ["Ext", "Box"] "MainOnly"

def testSourceConstructorVisibility : IO Unit := do
  testLocalAndImportedVisibility
  testSubsetAndContextualVisibility
  testReExportVisibility
  testAliasConstructorBoundary
  testCanonicalPathDoesNotBypassImports
  testLibraryIdentityIsolation

end Tests.SourceConstructorVisibility

namespace Tests

/-- Run the source-level constructor-visibility regressions. -/
def testSourceConstructorVisibility : IO Unit :=
  SourceConstructorVisibility.testSourceConstructorVisibility

end Tests
