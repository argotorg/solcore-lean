import Solcore.Syntax.Parser

/-! Successful canonical type-alias parser regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private abbrev ByteRange := Nat × Nat

private inductive TypeShape where
  | named (components : List String) (arguments : Option (List TypeShape))
  | mapping (key value : TypeShape)
  | proxy (inner : TypeShape)
  | function
      (parameters : List TypeShape)
      (returns : Option (List TypeShape))
  | comptime (inner : TypeShape)
  | tuple (elements : List TypeShape)
  | error
  deriving Repr, BEq, Inhabited

private def parserSource : SourceId := {
  origin := .main
  path := "parser-types.sol"
}

private def assertEqual {alpha : Type} [BEq alpha] [Repr alpha]
    (actual expected : alpha) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def byteRange (span : SourceSpan) : ByteRange :=
  (span.startByte, span.endByte)

private partial def typeShape (type : TypeExpr) : TypeShape :=
  match type.value with
  | .named name arguments =>
      .named
        (name.value.components.toList.map (fun component => component.value))
        (arguments.map fun values =>
          values.elements.toList.map typeShape)
  | .mapping _ _ key value => .mapping (typeShape key) (typeShape value)
  | .proxy _ inner => .proxy (typeShape inner)
  | .function _ parameters returns =>
      .function (parameters.elements.map typeShape)
        (returns.map fun values => values.elements.map typeShape)
  | .comptime _ _ inner => .comptime (typeShape inner)
  | .tuple elements => .tuple (elements.map typeShape)
  | .error => .error

private def asTypeAlias? (item : TopItem) : Option TypeAliasDecl :=
  match item.value with
  | .typeAlias declaration => some declaration
  | _ => none

private def aliasDeclarations (label : String)
    (output : ParseOutput) : IO (List TypeAliasDecl) := do
  let declarations := output.parsed.items.filterMap asTypeAlias?
  assertEqual declarations.length output.parsed.items.length
    s!"{label} type-alias item count"
  pure declarations

private def declarationAt (label : String)
    (declarations : List TypeAliasDecl) (index : Nat) : IO TypeAliasDecl :=
  match declarations[index]? with
  | some declaration => pure declaration
  | none => throw (IO.userError s!"{label}: missing declaration {index}")

private def checkedParse (label content : String) : IO ParseOutput := do
  let file : SourceFile := { id := parserSource, content }
  match Parser.parse file with
  | .error error =>
      throw (IO.userError
        s!"{label}: parser invariant failed: {reprStr error}")
  | .ok output =>
      assertEqual output.parsed.source file.id s!"{label} source owner"
      assertEqual output.parsed.span (SourceSpan.fullFile file)
        s!"{label} full-file span"
      assertEqual output.lexicalDiagnostics []
        s!"{label} lexical diagnostics"
      unless output.parsed.items.all
          (fun item => item.span.isValidFor file) do
        throw (IO.userError s!"{label}: item span escaped the source")
      unless output.parseDiagnostics.all
          (fun diagnostic => diagnostic.span.isValidFor file) do
        throw (IO.userError s!"{label}: diagnostic span escaped the source")
      pure output

private def aliasNames (declarations : List TypeAliasDecl) : List String :=
  declarations.map fun declaration => declaration.value.name.value

private def aliasShapes
    (declarations : List TypeAliasDecl) : List TypeShape :=
  declarations.map fun declaration => typeShape declaration.value.value

private def aliasParameterNames
    (declaration : TypeAliasDecl) : Option (List String) :=
  declaration.value.parameters.map fun parameters =>
    parameters.elements.map (fun parameter => parameter.value)

private def named (name : String) : TypeShape :=
  .named [name] none

private def testEveryTypeForm : IO Unit := do
  let output ← checkedParse "all Core type forms" (String.intercalate "\n" [
    "type Plain = pkg.Word;",
    "type Generic = pkg.Box<A, mapping(K => @V)>;",
    "type Proxy = @Target;",
    "type Callable = function(A, @B) returns (C, ());",
    "type Compile = comptime<function()>;",
    "type EmptyTuple = ();",
    "type Singleton = (A);",
    "type Pair = (A, B);"
  ])
  assertEqual output.parseDiagnostics [] "all Core type-form diagnostics"
  let declarations ← aliasDeclarations "all Core type forms" output
  assertEqual (aliasNames declarations) [
      "Plain", "Generic", "Proxy", "Callable", "Compile",
      "EmptyTuple", "Singleton", "Pair"
    ] "all Core type-form names"
  assertEqual (aliasShapes declarations) [
      .named ["pkg", "Word"] none,
      .named ["pkg", "Box"] (some [
        named "A", .mapping (named "K") (.proxy (named "V"))]),
      .proxy (named "Target"),
      .function [named "A", .proxy (named "B")]
        (some [named "C", .tuple []]),
      .comptime (.function [] none),
      .tuple [],
      .tuple [named "A"],
      .tuple [named "A", named "B"]
    ] "all Core type-form source distinctions"

private def testAliasParameters : IO Unit := do
  let output ← checkedParse "alias parameters" (String.intercalate "\n" [
    "type NoParams = A;",
    "type EmptyParams() = B;",
    "type Explicit(T, U) = Pair<T, U>;"
  ])
  assertEqual output.parseDiagnostics [] "alias-parameter diagnostics"
  let declarations ← aliasDeclarations "alias parameters" output
  assertEqual (declarations.map aliasParameterNames)
    [none, some [], some ["T", "U"]]
    "absent, empty, and explicit alias parameters"

private def testContextualIdentifiers : IO Unit := do
  let output ← checkedParse "contextual identifiers"
    "type Contextual(comptime, derive, enum, from, hiding, impl, mapping, returns, trait, where, while) = while;"
  assertEqual output.parseDiagnostics [] "contextual-identifier diagnostics"
  let declarations ← aliasDeclarations "contextual identifiers" output
  let declaration ← declarationAt "contextual identifiers" declarations 0
  assertEqual (aliasParameterNames declaration) (some [
      "comptime", "derive", "enum", "from", "hiding", "impl",
      "mapping", "returns", "trait", "where", "while"
    ]) "contextual words in identifier positions"
  assertEqual (typeShape declaration.value.value) (named "while")
    "contextual word as named type"

private def testUtf8ByteSpans : IO Unit := do
  let output ← checkedParse "UTF-8 byte spans"
    "type 型(T) = comptime<λ.Word>;"
  assertEqual output.parseDiagnostics [] "UTF-8 span diagnostics"
  let declarations ← aliasDeclarations "UTF-8 byte spans" output
  let declaration ← declarationAt "UTF-8 byte spans" declarations 0
  assertEqual (byteRange declaration.span) (0, 32) "UTF-8 alias span"
  assertEqual (byteRange declaration.value.name.span) (5, 8)
    "UTF-8 alias-name span"
  match declaration.value.parameters with
  | some parameters =>
      assertEqual (byteRange parameters.span) (8, 11)
        "UTF-8 parameter delimiter span"
  | none => throw (IO.userError "UTF-8 parameters were lost")
  assertEqual (byteRange declaration.value.value.span) (14, 31)
    "UTF-8 comptime type span"
  match declaration.value.value.value with
  | .comptime keyword arguments inner =>
      assertEqual (byteRange keyword) (14, 22) "UTF-8 comptime keyword"
      assertEqual (byteRange arguments) (22, 31) "UTF-8 comptime arguments"
      assertEqual (byteRange inner.span) (23, 30) "UTF-8 inner type span"
      match inner.value with
      | .named name none =>
          assertEqual
            (name.value.components.toList.map fun component =>
              (component.value, byteRange component.span))
            [("λ", (23, 25)), ("Word", (26, 30))]
            "UTF-8 qualified-name component spans"
      | _ => throw (IO.userError "UTF-8 inner type changed shape")
  | _ => throw (IO.userError "UTF-8 outer type changed shape")

private def testMappingConstraint : IO Unit := do
  let output ← checkedParse "mapping canonical constraint"
    "type M = mapping<K, V>;"
  let declarations ← aliasDeclarations "mapping canonical constraint" output
  let declaration ← declarationAt "mapping canonical constraint" declarations 0
  assertEqual (typeShape declaration.value.value)
    (.named ["mapping"] (some [named "K", named "V"]))
    "noncanonical mapping remains source-shaped"
  assertEqual output.parseDiagnostics [{
      span := declaration.value.value.span
      kind := .constraintViolation .mappingRequiresCanonicalForm
    }] "mapping canonical constraint diagnostic"
  assertEqual (byteRange declaration.value.value.span) (9, 22)
    "mapping canonical constraint span"

private def testHyphenDiagnostic : IO Unit := do
  let output ← checkedParse "hyphen diagnostic"
    "type bad-name = Good;"
  let declarations ← aliasDeclarations "hyphen diagnostic" output
  let declaration ← declarationAt "hyphen diagnostic" declarations 0
  assertEqual declaration.value.name.value "bad-name"
    "hyphenated identifier preservation"
  assertEqual output.parseDiagnostics [{
      span := declaration.value.name.span
      kind := .invalidIdentifierHyphen "bad-name"
    }] "hyphen diagnostic"
  assertEqual (byteRange declaration.value.name.span) (5, 13)
    "hyphen diagnostic span"

/-- Run successful canonical type-alias parser and diagnostic regressions. -/
def testSyntaxParserTypes : IO Unit := do
  testEveryTypeForm
  testAliasParameters
  testContextualIdentifiers
  testUtf8ByteSpans
  testMappingConstraint
  testHyphenDiagnostic

end Tests
