import Solcore.Syntax.Module

/-!
Declarative token grammar for the canonical syntax.

This module describes accepted token slices without referring to parser
functions or parser replies.  A `Remainder` is the immutable token carrier,
active window, and cursor that identify the unconsumed input.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Parser-independent view of the tokens still available to a production. -/
structure Remainder where
  tokens : Array Token
  endIndex : Nat
  cursor : Nat
  deriving Repr, BEq, DecidableEq

/-- Exact located token at an index inside an active token window. -/
def TokenAt (tokens : Array Token) (endIndex : Nat)
    (index : Nat) (token : Token) : Prop :=
  index < endIndex ∧ tokens[index]? = some token

/-- No token of `kind` occurs at one position in the active window. -/
def TokenKindAbsentAt (tokens : Array Token) (endIndex index : Nat)
    (kind : TokenKind) : Prop :=
  ¬ ∃ span, TokenAt tokens endIndex index { span, value := kind }

/-- Last identifier of one nonempty forward-order component sequence. -/
def finalIdentifier : Identifier → List Identifier → Identifier
  | first, [] => first
  | _, next :: rest => finalIdentifier next rest

/-- Grammar of the dotted components following a first identifier. -/
inductive DottedIdentifierTailParses
    (tokens : Array Token) (endIndex : Nat) :
    Nat → List Identifier → Nat → Prop where
  | done (cursor : Nat)
      (stopped : TokenKindAbsentAt tokens endIndex cursor (.symbol .dot)) :
      DottedIdentifierTailParses tokens endIndex cursor [] cursor
  | next {cursor finish : Nat} {component : Identifier}
      {components : List Identifier}
      (dotSpan : SourceSpan)
      (dotToken : TokenAt tokens endIndex cursor {
        span := dotSpan
        value := .symbol .dot
      })
      (componentToken : TokenAt tokens endIndex (cursor + 1) {
        span := component.span
        value := .identifier component.value
      })
      (tail : DottedIdentifierTailParses tokens endIndex (cursor + 2)
        components finish) :
      DottedIdentifierTailParses tokens endIndex cursor
        (component :: components) finish

/-- Independent recognition judgment for one nonempty qualified name. -/
def QualifiedNameParses
    (input : Remainder) (name : Syntax.QualifiedName)
    (output : Remainder) : Prop :=
  output.tokens = input.tokens ∧
    output.endIndex = input.endIndex ∧
    TokenAt input.tokens input.endIndex input.cursor {
      span := name.value.components.head.span
      value := .identifier name.value.components.head.value
    } ∧
    DottedIdentifierTailParses input.tokens input.endIndex
      (input.cursor + 1) name.value.components.tail output.cursor ∧
    name.span = SourceSpan.cover name.value.components.head.span
      (finalIdentifier name.value.components.head
        name.value.components.tail).span

/--
Independent recognition judgment for one module path.

A local path is exactly a qualified name.  An external-package path starts
with `@` and then parses the same qualified-name grammar from the following
token.  The retained marker, components, and covering span are fixed by the
recognized tokens.
-/
inductive ModulePathParses : Remainder → Syntax.ModulePath → Remainder → Prop
    where
  | local {input output : Remainder} {name : Syntax.QualifiedName}
      (nameParses : QualifiedNameParses input name output) :
      ModulePathParses input {
        span := name.span
        value := {
          externalMarker := none
          components := name.value.components
        }
      } output
  | externalPackage {input output : Remainder} {name : Syntax.QualifiedName}
      (markerSpan : SourceSpan)
      (markerToken : TokenAt input.tokens input.endIndex input.cursor {
        span := markerSpan
        value := .symbol .at
      })
      (nameParses : QualifiedNameParses
        { input with cursor := input.cursor + 1 } name output) :
      ModulePathParses input {
        span := SourceSpan.cover markerSpan name.span
        value := {
          externalMarker := some markerSpan
          components := name.value.components
        }
      } output

/-! Plain imports remain a separate judgment as other import forms are added. -/

/-- Grammar of the module path and semicolon following `import`. -/
def PlainImportTailParses (startSpan : SourceSpan)
    (input : Remainder) (declaration : Syntax.ImportDecl)
    (output : Remainder) : Prop :=
  ∃ path afterPath semicolonSpan,
    ModulePathParses input path afterPath ∧
    TokenAt afterPath.tokens afterPath.endIndex afterPath.cursor {
      span := semicolonSpan
      value := .symbol .semicolon
    } ∧
    output = { afterPath with cursor := afterPath.cursor + 1 } ∧
    declaration = {
      span := SourceSpan.cover startSpan semicolonSpan
      value := .plain path
    }

/-- Independent recognition judgment for `import ModulePath ;`. -/
def PlainImportDeclParses
    (input : Remainder) (declaration : Syntax.ImportDecl)
    (output : Remainder) : Prop :=
  ∃ keywordSpan,
    TokenAt input.tokens input.endIndex input.cursor {
      span := keywordSpan
      value := .keyword .importKw
    } ∧
    PlainImportTailParses keywordSpan
      { input with cursor := input.cursor + 1 } declaration output

/-- Grammar after `import` for `* as alias from ModulePath ;`. -/
def NamespaceImportTailParses (startSpan : SourceSpan)
    (input : Remainder) (declaration : Syntax.ImportDecl)
    (output : Remainder) : Prop :=
  ∃ starSpan asSpan alias fromSpan path afterPath semicolonSpan,
    TokenAt input.tokens input.endIndex input.cursor {
      span := starSpan
      value := .symbol .star
    } ∧
    TokenAt input.tokens input.endIndex (input.cursor + 1) {
      span := asSpan
      value := .keyword .asKw
    } ∧
    TokenAt input.tokens input.endIndex (input.cursor + 2) {
      span := alias.span
      value := .identifier alias.value
    } ∧
    TokenAt input.tokens input.endIndex (input.cursor + 3) {
      span := fromSpan
      value := .identifier ContextualKeyword.from.spelling
    } ∧
    ModulePathParses { input with cursor := input.cursor + 4 }
      path afterPath ∧
    TokenAt afterPath.tokens afterPath.endIndex afterPath.cursor {
      span := semicolonSpan
      value := .symbol .semicolon
    } ∧
    output = { afterPath with cursor := afterPath.cursor + 1 } ∧
    declaration = {
      span := SourceSpan.cover startSpan semicolonSpan
      value := .namespace path alias
    }

/-- Independent recognition judgment for one complete namespace import. -/
def NamespaceImportDeclParses
    (input : Remainder) (declaration : Syntax.ImportDecl)
    (output : Remainder) : Prop :=
  ∃ keywordSpan,
    TokenAt input.tokens input.endIndex input.cursor {
      span := keywordSpan
      value := .keyword .importKw
    } ∧
    NamespaceImportTailParses keywordSpan
      { input with cursor := input.cursor + 1 } declaration output

/-- Token grammar after the first pragma argument has been consumed. -/
inductive PragmaItemsTailParses
    (tokens : Array Token) (endIndex : Nat) :
    Nat → List Identifier → Nat → Prop where
  | done (cursor : Nat) :
      PragmaItemsTailParses tokens endIndex cursor [] cursor
  | trailing {cursor : Nat}
      (commaSpan : SourceSpan)
      (commaToken : TokenAt tokens endIndex cursor {
        span := commaSpan
        value := .symbol .comma
      }) :
      PragmaItemsTailParses tokens endIndex cursor [] (cursor + 1)
  | next {cursor finish : Nat} {item : Identifier}
      {items : List Identifier}
      (commaSpan : SourceSpan)
      (commaToken : TokenAt tokens endIndex cursor {
        span := commaSpan
        value := .symbol .comma
      })
      (itemToken : TokenAt tokens endIndex (cursor + 1) {
        span := item.span
        value := .identifier item.value
      })
      (tail : PragmaItemsTailParses tokens endIndex (cursor + 2)
        items finish) :
      PragmaItemsTailParses tokens endIndex cursor (item :: items) finish

/--
Token grammar of pragma arguments.  Arguments are comma-separated ordinary
identifiers, and a final comma is accepted.  The finishing cursor is the first
token not belonging to the argument sequence.
-/
inductive PragmaItemsParses (tokens : Array Token) (endIndex : Nat) :
    Nat → List Identifier → Nat → Prop where
  | empty (cursor : Nat) :
      PragmaItemsParses tokens endIndex cursor [] cursor
  | nonempty {cursor finish : Nat} {item : Identifier}
      {items : List Identifier}
      (itemToken : TokenAt tokens endIndex cursor {
        span := item.span
        value := .identifier item.value
      })
      (tail : PragmaItemsTailParses tokens endIndex (cursor + 1)
        items finish) :
      PragmaItemsParses tokens endIndex cursor (item :: items) finish

/--
Independent recognition judgment for one complete pragma declaration.

Besides the punctuation, this checks the exact text and span of the pragma
name and every argument retained in the AST.  The output remainder must keep
the same token carrier and active window and begin after the semicolon.
-/
def PragmaDeclParses
    (input : Remainder) (declaration : Syntax.PragmaDecl)
    (output : Remainder) : Prop :=
  ∃ keywordSpan semicolonSpan semicolonIndex,
    output.tokens = input.tokens ∧
    output.endIndex = input.endIndex ∧
    TokenAt input.tokens input.endIndex input.cursor {
      span := keywordSpan
      value := .keyword .pragmaKw
    } ∧
    TokenAt input.tokens input.endIndex (input.cursor + 1) {
      span := declaration.value.name.span
      value := .identifier declaration.value.name.value
    } ∧
    PragmaItemsParses input.tokens input.endIndex (input.cursor + 2)
      declaration.value.items semicolonIndex ∧
    TokenAt input.tokens input.endIndex semicolonIndex {
      span := semicolonSpan
      value := .symbol .semicolon
    } ∧
    output.cursor = semicolonIndex + 1 ∧
    declaration.span = SourceSpan.cover keywordSpan semicolonSpan

end Solcore.Syntax.DeclarativeGrammar
