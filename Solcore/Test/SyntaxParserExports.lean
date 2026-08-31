import Solcore.Syntax.Parser

/-! Executable export parser regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private abbrev ByteRange := Nat × Nat

private def parserSource : SourceId := {
  origin := .main
  path := "parser-exports.sol"
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
  | .error error => throw (IO.userError
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

private inductive ConstructorShape where
  | all
  | named (names : List String)
  deriving Repr, BEq

private inductive ExportNameShape where
  | wildcard
  | identifier (name : String) (constructors : Option ConstructorShape)
  | operator (spelling : String)
  deriving Repr, BEq

private inductive LocalExportShape where
  | name (name : ExportNameShape)
  | moduleWildcard (path : List String)
  deriving Repr, BEq

private inductive ExportShape where
  | local (items : List LocalExportShape)
  | wholeModule (path : List String)
  | moduleAlias (path : List String) (alias : String)
  | itemsFromWildcard (path : List String)
  | itemsFromSelected (path : List String) (items : List ExportNameShape)
  deriving Repr, BEq

private def identifierTexts (names : NonemptyList Identifier) : List String :=
  names.toList.map (fun name => name.value)

private def qualifiedComponents (name : QualifiedName) : List String :=
  identifierTexts name.value.components

private def constructorShape
    (selection : ConstructorSelection) : ConstructorShape :=
  match selection.value with
  | .all _ => .all
  | .named names => .named (identifierTexts names)

private def exportNameShape (name : ExportName) : ExportNameShape :=
  match name.value with
  | .wildcard _ => .wildcard
  | .identifier identifier constructors =>
      .identifier identifier.value (constructors.map constructorShape)
  | .operator spelling => .operator spelling.value

private def localExportShape (item : LocalExportItem) : LocalExportShape :=
  match item.value with
  | .name name => .name (exportNameShape name)
  | .moduleWildcard path _ => .moduleWildcard (qualifiedComponents path)

private def exportShape (declaration : ExportDecl) : ExportShape :=
  match declaration.value with
  | .local items => .local (items.elements.map localExportShape)
  | .module path => .wholeModule (qualifiedComponents path)
  | .moduleAs path alias =>
      .moduleAlias (qualifiedComponents path) alias.value
  | .itemsFrom path selection =>
      match selection.value with
      | .wildcard _ => .itemsFromWildcard (qualifiedComponents path)
      | .selected items => .itemsFromSelected
          (qualifiedComponents path) (items.elements.map exportNameShape)

private def exportDecls (output : ParseOutput) : List ExportDecl :=
  output.parsed.items.filterMap fun item => match item.value with
    | .exportDecl declaration => some declaration
    | _ => none

private def testExportForms : IO Unit := do
  let output ← checkedParse "canonical exports" (String.intercalate "\n" [
    "export {};",
    "export {value, *, lib.deep.*, (==), Option(*), Result(Ok, Err),};",
    "export pkg.deep;",
    "export pkg.deep as alias;",
    "export pkg.deep.*;",
    "export pkg.deep.{};",
    "export pkg.deep.{value, *, (:=), Option(Some),};"
  ])
  assertEqual output.parseDiagnostics [] "canonical export diagnostics"
  assertEqual ((exportDecls output).map exportShape) [
    .local [],
    .local [
      .name (.identifier "value" none), .name .wildcard,
      .moduleWildcard ["lib", "deep"], .name (.operator "=="),
      .name (.identifier "Option" (some .all)),
      .name (.identifier "Result" (some (.named ["Ok", "Err"])))
    ],
    .wholeModule ["pkg", "deep"],
    .moduleAlias ["pkg", "deep"] "alias",
    .itemsFromWildcard ["pkg", "deep"],
    .itemsFromSelected ["pkg", "deep"] [],
    .itemsFromSelected ["pkg", "deep"] [
      .identifier "value" none, .wildcard, .operator ":=",
      .identifier "Option" (some (.named ["Some"]))
    ]
  ] "canonical export forms and written distinctions"

private def testExportSpans : IO Unit := do
  let output ← checkedParse "export spans"
    "export pkg.deep.{Option(Some, None), (==), *,};"
  assertEqual output.parseDiagnostics [] "export span diagnostics"
  match exportDecls output with
  | [{ span, value := .itemsFrom path selection }] =>
      assertEqual (byteRange span) (0, 47) "export declaration span"
      assertEqual (byteRange path.span) (7, 15) "export module span"
      assertEqual (byteRange selection.span) (16, 46) "export selection span"
      match selection.value with
      | .selected { elements := [option, operator, wildcard], .. } =>
          assertEqual (byteRange option.span) (17, 35) "constructor export span"
          assertEqual (byteRange operator.span) (37, 41) "operator export span"
          assertEqual (byteRange wildcard.span) (43, 44) "wildcard export span"
      | value => throw (IO.userError
          s!"export spans: unexpected selection {reprStr value}")
  | declarations => throw (IO.userError
      s!"export spans: unexpected declarations {reprStr declarations}")

private def testConstructorTrailingCommaStops : IO Unit := do
  let output ← checkedParse "constructor trailing comma"
    "export {Option(Some,)};\ntype Later = word;"
  assertEqual output.parsed.items.length 0
    "malformed recognized declaration stops later parsing"
  match output.parseDiagnostics with
  | [{ span, kind := .unexpected (some (.symbol .rightParen))
        { head := .identifier, tail := [] } .exportDecl }] =>
      assertEqual (byteRange span) (20, 21)
        "constructor trailing-comma rejection span"
  | diagnostics => throw (IO.userError
      s!"constructor trailing comma: unexpected diagnostics {reprStr diagnostics}")

/-- Run canonical export parser regressions. -/
def testSyntaxParserExports : IO Unit := do
  testExportForms
  testExportSpans
  testConstructorTrailingCommaStops

end Tests
