import Solcore.Syntax.Parser

/-! Executable import and pragma parser regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private abbrev ByteRange := Nat × Nat

private def parserSource : SourceId := {
  origin := .main
  path := "parser-modules.sol"
}

private def assertEqual {alpha : Type} [BEq alpha] [Repr alpha]
    (actual expected : alpha) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def byteRange (span : SourceSpan) : ByteRange :=
  (span.startByte, span.endByte)

private def checkedParse (label content : String) : IO ParseOutput := do
  let file : SourceFile := { id := parserSource, content }
  match Parser.parse file with
  | .error error =>
      throw (IO.userError
        s!"{label}: parser invariant failed: {reprStr error}")
  | .ok output =>
      assertEqual output.lexicalDiagnostics []
        s!"{label} lexical diagnostics"
      unless output.parsed.items.all
          (fun item => item.span.isValidFor file) do
        throw (IO.userError s!"{label}: invalid item span")
      unless output.parseDiagnostics.all
          (fun diagnostic => diagnostic.span.isValidFor file) do
        throw (IO.userError s!"{label}: invalid diagnostic span")
      pure output

private structure PathShape where
  rooted : Bool
  components : List String
  deriving Repr, BEq

private inductive SelectorShape where
  | identifier (name : String)
  | operator (spelling : String)
  deriving Repr, BEq

private structure SelectedShape where
  source : SelectorShape
  alias : Option String
  deriving Repr, BEq

private inductive ImportShape where
  | plain (path : PathShape)
  | namespaceAlias (path : PathShape) (alias : String)
  | wildcard (path : PathShape) (hidden : Option (List SelectorShape))
  | selected
      (items : List SelectedShape)
      (path : PathShape)
      (hidden : Option (List SelectorShape))
  deriving Repr, BEq

private def identifierTexts (names : NonemptyList Identifier) : List String :=
  names.toList.map (fun name => name.value)

private def pathShape (path : ModulePath) : PathShape := {
  rooted := path.value.externalMarker.isSome
  components := identifierTexts path.value.components
}

private def selectorShape (selector : SelectorName) : SelectorShape :=
  match selector.value with
  | .identifier name => .identifier name.value
  | .operator spelling => .operator spelling

private def hidingShape (clause : HidingClause) : List SelectorShape :=
  clause.value.names.toList.map selectorShape

private def importShape (declaration : ImportDecl) : ImportShape :=
  match declaration.value with
  | .plain path => .plain (pathShape path)
  | .namespace path alias => .namespaceAlias (pathShape path) alias.value
  | .wildcard path hidden =>
      .wildcard (pathShape path) (hidden.map hidingShape)
  | .selected items path hidden =>
      .selected
        (items.elements.toList.map fun item => {
          source := selectorShape item.value.source
          alias := item.value.alias.map (fun name => name.value)
        })
        (pathShape path) (hidden.map hidingShape)

private def importDecls (output : ParseOutput) : List ImportDecl :=
  output.parsed.items.filterMap fun item => match item.value with
    | .importDecl declaration => some declaration
    | _ => none

private def pragmaDecls (output : ParseOutput) : List PragmaDecl :=
  output.parsed.items.filterMap fun item => match item.value with
    | .pragmaDecl declaration => some declaration
    | _ => none

private def testImportForms : IO Unit := do
  let output ← checkedParse "canonical imports" (String.intercalate "\n" [
    "import alpha.beta;",
    "import @vendor.pkg;",
    "import * as ns from lib.deep;",
    "import * as ext from @vendor.deep;",
    "import * from lib.all;",
    "import * from @vendor.all hiding {gone, (!),};",
    "import {foo, bar as baz, (==) as eq,} from @pkg.names hiding {foo, (+=),};"
  ])
  assertEqual output.parseDiagnostics [] "canonical import diagnostics"
  assertEqual ((importDecls output).map importShape) [
    .plain ⟨false, ["alpha", "beta"]⟩,
    .plain ⟨true, ["vendor", "pkg"]⟩,
    .namespaceAlias ⟨false, ["lib", "deep"]⟩ "ns",
    .namespaceAlias ⟨true, ["vendor", "deep"]⟩ "ext",
    .wildcard ⟨false, ["lib", "all"]⟩ none,
    .wildcard ⟨true, ["vendor", "all"]⟩
      (some [.identifier "gone", .operator "!"]),
    .selected [
        ⟨.identifier "foo", none⟩,
        ⟨.identifier "bar", some "baz"⟩,
        ⟨.operator "==", some "eq"⟩
      ] ⟨true, ["pkg", "names"]⟩
      (some [.identifier "foo", .operator "+="])
  ] "canonical import forms"

private def operatorSpellings : List String := [
  ":=", "->", "=>", "==", "!=", ">=", "<=", "&&", "||",
  "+=", "-=", "*=", "/=", "^=", "&=", "|=", "%=", "~=",
  "+", "-", "*", "/", "%", "!", "~", "<", ">", "=", "|",
  "&", "^", ":", "+-"
]

private def testOperatorSelectors : IO Unit := do
  let selectors := operatorSpellings.map (fun spelling =>
    "(" ++ spelling ++ ")")
  let output ← checkedParse "operator selectors"
    ("import {" ++ String.intercalate ", " selectors ++ "} from ops;")
  assertEqual output.parseDiagnostics [] "operator selector diagnostics"
  match (importDecls output).map importShape with
  | [.selected items _ none] =>
      assertEqual (items.map (fun item => item.source))
        (operatorSpellings.map .operator) "operator selector spellings"
  | shapes => throw (IO.userError
      s!"operator selectors: unexpected imports {reprStr shapes}")

private def testImportSpans : IO Unit := do
  let output ← checkedParse "import spans"
    "import {foo as bar, (==),} from @pkg.mod hiding {gone,};"
  assertEqual output.parseDiagnostics [] "import span diagnostics"
  match importDecls output with
  | [{ span, value := .selected selection path (some hidden) }] =>
      assertEqual (byteRange span) (0, 56) "import declaration span"
      assertEqual (byteRange selection.span) (7, 26) "import selection span"
      match selection.elements.toList with
      | [first, operator] =>
          assertEqual (byteRange first.span) (8, 18) "aliased import span"
          assertEqual (byteRange operator.span) (20, 24) "operator import span"
      | values => throw (IO.userError
          s!"import spans: unexpected selection {reprStr values}")
      assertEqual (byteRange path.span) (32, 40) "external module span"
      assertEqual (path.value.externalMarker.map byteRange) (some (32, 33))
        "external marker span"
      assertEqual (byteRange hidden.span) (41, 55) "hiding clause span"
      assertEqual (hidden.value.names.toList.map
        (fun name => byteRange name.span)) [(49, 53)] "hidden-name span"
  | declarations => throw (IO.userError
      s!"import spans: unexpected declarations {reprStr declarations}")

private def testPragmaFormsAndHyphens : IO Unit := do
  let output ← checkedParse "pragma forms" (String.intercalate "\n" [
    "pragma solcore;",
    "pragma solcore feature,experimental,;",
    "pragma sol-core 型,;"
  ])
  assertEqual output.parseDiagnostics [] "pragma-name hyphen policy"
  assertEqual ((pragmaDecls output).map fun declaration =>
      (declaration.value.name.value,
        declaration.value.items.map (fun item => item.value))) [
    ("solcore", []),
    ("solcore", ["feature", "experimental"]),
    ("sol-core", ["型"])
  ] "empty and trailing pragma items"
  match pragmaDecls output with
  | [_, _, declaration] =>
      assertEqual (byteRange declaration.span) (54, 75) "UTF-8 pragma span"
      assertEqual (byteRange declaration.value.name.span) (61, 69)
        "hyphenated pragma-name span"
      assertEqual (declaration.value.items.map
        (fun item => byteRange item.span)) [(70, 73)] "UTF-8 pragma item span"
  | declarations => throw (IO.userError
      s!"pragma spans: unexpected declarations {reprStr declarations}")

  let invalid ← checkedParse "pragma item hyphen"
    "pragma sol-core bad-item;"
  match pragmaDecls invalid with
  | [declaration] =>
      assertEqual declaration.value.name.value "sol-core"
        "pragma name remains raw"
  | declarations => throw (IO.userError
      s!"pragma item hyphen: unexpected declarations {reprStr declarations}")
  match invalid.parseDiagnostics with
  | [{ span, kind := .invalidIdentifierHyphen "bad-item" }] =>
      assertEqual (byteRange span) (16, 24) "pragma item hyphen span"
  | diagnostics => throw (IO.userError
      s!"pragma item hyphen: unexpected diagnostics {reprStr diagnostics}")

private def testMissingImportSemicolon : IO Unit := do
  let output ← checkedParse "missing import semicolon"
    "import pkg\ntype Later = word;"
  match output.parsed.items with
  | [
      { span := importSpan, value := .importDecl importDeclaration, .. },
      { value := .typeAlias alias, .. }
    ] =>
      assertEqual (importShape importDeclaration) (.plain ⟨false, ["pkg"]⟩)
        "missing semicolon import shape"
      assertEqual (byteRange importSpan) (0, 10) "missing semicolon import span"
      assertEqual alias.value.name.value "Later" "following item preserved"
  | items => throw (IO.userError
      s!"missing import semicolon: unexpected items {reprStr items}")
  match output.parseDiagnostics with
  | [{ span, kind := .constraintViolation
        (.trailingSemicolonRequired .importDecl) }] =>
      assertEqual (byteRange span) (11, 15) "missing semicolon diagnostic span"
  | diagnostics => throw (IO.userError
      s!"missing import semicolon: unexpected diagnostics {reprStr diagnostics}")

/-! Run canonical import and pragma parser regressions. -/
def testSyntaxParserModules : IO Unit := do
  testImportForms
  testOperatorSelectors
  testImportSpans
  testPragmaFormsAndHyphens
  testMissingImportSemicolon

end Tests
