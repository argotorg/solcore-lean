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

/-! Import and export selectors share an exact identifier/operator grammar. -/

/-- Symbols admitted as parts of a parenthesized import/export operator. -/
def SelectorOperatorSymbol : Symbol → Prop
  | .colonEqual | .arrow | .fatArrow | .equalEqual | .notEqual
  | .greaterEqual | .lessEqual | .logicalAnd | .logicalOr
  | .plusEqual | .minusEqual | .starEqual | .slashEqual | .caretEqual
  | .ampEqual | .pipeEqual | .percentEqual | .tildeEqual
  | .plus | .minus | .star | .slash | .percent | .bang | .tilde
  | .less | .greater | .equal | .pipe | .amp | .caret | .colon => True
  | _ => False

/--
Forward-order grammar of the symbols inside an operator selector.

The empty case is useful for the recursive tail.  `OperatorSelectorParses`
separately requires the complete sequence to be nonempty.
-/
inductive SelectorOperatorPartsParses
    (tokens : Array Token) (endIndex : Nat) :
    Nat → List String → Nat → Prop where
  | done (cursor : Nat) :
      SelectorOperatorPartsParses tokens endIndex cursor [] cursor
  | next {cursor finish : Nat} {symbol : Symbol} {parts : List String}
      (allowed : SelectorOperatorSymbol symbol)
      (span : SourceSpan)
      (token : TokenAt tokens endIndex cursor {
        span
        value := .symbol symbol
      })
      (tail : SelectorOperatorPartsParses tokens endIndex
        (cursor + 1) parts finish) :
      SelectorOperatorPartsParses tokens endIndex cursor
        (symbol.spelling :: parts) finish

/-- Exact grammar of one parenthesized, nonempty operator selector. -/
def OperatorSelectorParses
    (input : Remainder) (selector : Syntax.SelectorName)
    (output : Remainder) : Prop :=
  ∃ openingSpan closingSpan parts closingIndex,
    output.tokens = input.tokens ∧
    output.endIndex = input.endIndex ∧
    TokenAt input.tokens input.endIndex input.cursor {
      span := openingSpan
      value := .symbol .leftParen
    } ∧
    SelectorOperatorPartsParses input.tokens input.endIndex
      (input.cursor + 1) parts closingIndex ∧
    parts ≠ [] ∧
    TokenAt input.tokens input.endIndex closingIndex {
      span := closingSpan
      value := .symbol .rightParen
    } ∧
    output.cursor = closingIndex + 1 ∧
    selector = {
      span := SourceSpan.cover openingSpan closingSpan
      value := .operator (String.join parts)
    }

/-- Independent grammar of an identifier or parenthesized operator selector. -/
inductive SelectorNameParses :
    Remainder → Syntax.SelectorName → Remainder → Prop where
  | identifier {input output : Remainder} {name : Identifier}
      (nameToken : TokenAt input.tokens input.endIndex input.cursor {
        span := name.span
        value := .identifier name.value
      })
      (tokensEq : output.tokens = input.tokens)
      (endIndexEq : output.endIndex = input.endIndex)
      (cursorEq : output.cursor = input.cursor + 1) :
      SelectorNameParses input {
        span := name.span
        value := .identifier name
      } output
  | operator {input output : Remainder} {selector : Syntax.SelectorName}
      (parsed : OperatorSelectorParses input selector output) :
      SelectorNameParses input selector output

/-! Generic nonempty delimiter grammar used by hiding and selection lists. -/

/--
Forward-order grammar after one delimited element has been recognized.

The absence premises retain the executable parser's branch priority: a comma
is handled before a closing symbol, and a closing symbol immediately following
a comma is handled as the optional trailing comma rather than as an element.
-/
inductive TrailingDelimitedTailParses {α : Type}
    (closing : Symbol)
    (elementParses : Remainder → α → Remainder → Prop) :
    Remainder → List α → SourceSpan → Remainder → Prop where
  | close {input : Remainder} {closingSpan : SourceSpan}
      (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .comma))
      (closingToken : TokenAt input.tokens input.endIndex input.cursor {
        span := closingSpan
        value := .symbol closing
      }) :
      TrailingDelimitedTailParses closing elementParses input [] closingSpan
        { input with cursor := input.cursor + 1 }
  | trailing {input : Remainder} {commaSpan closingSpan : SourceSpan}
      (commaToken : TokenAt input.tokens input.endIndex input.cursor {
        span := commaSpan
        value := .symbol .comma
      })
      (closingToken : TokenAt input.tokens input.endIndex
        (input.cursor + 1) {
          span := closingSpan
          value := .symbol closing
        }) :
      TrailingDelimitedTailParses closing elementParses input [] closingSpan
        { input with cursor := input.cursor + 2 }
  | next {input afterElement output : Remainder}
      {commaSpan closingSpan : SourceSpan} {element : α}
      {elements : List α}
      (commaToken : TokenAt input.tokens input.endIndex input.cursor {
        span := commaSpan
        value := .symbol .comma
      })
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        (input.cursor + 1) (.symbol closing))
      (elementParsed : elementParses
        { input with cursor := input.cursor + 1 } element afterElement)
      (progress : input.cursor + 1 < afterElement.cursor)
      (tail : TrailingDelimitedTailParses closing elementParses afterElement
        elements closingSpan output) :
      TrailingDelimitedTailParses closing elementParses input
        (element :: elements) closingSpan output

/--
Independent grammar of a nonempty comma-separated list with an optional final
comma.  Delimiter and element ranges remain in source order, while the output
retains the input token carrier and active-window end.
-/
def NonemptyTrailingDelimitedListParses {α : Type}
    (opening closing : Symbol)
    (elementParses : Remainder → α → Remainder → Prop)
    (input : Remainder) (values : DelimitedList α)
    (output : Remainder) : Prop :=
  ∃ openingSpan first afterFirst rest closingSpan,
    output.tokens = input.tokens ∧
    output.endIndex = input.endIndex ∧
    TokenAt input.tokens input.endIndex input.cursor {
      span := openingSpan
      value := .symbol opening
    } ∧
    elementParses { input with cursor := input.cursor + 1 }
      first afterFirst ∧
    input.cursor + 1 < afterFirst.cursor ∧
    TrailingDelimitedTailParses closing elementParses afterFirst rest
      closingSpan output ∧
    values.elements = first :: rest ∧
    values.span = SourceSpan.cover openingSpan closingSpan

/-- Exact optional alias following one selected import name. -/
inductive SelectedAliasParses :
    Remainder → Option Identifier → Remainder → Prop where
  | absent {input : Remainder}
      (stopped : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .asKw)) :
      SelectedAliasParses input none input
  | present {input output : Remainder} {name : Identifier}
      (asSpan : SourceSpan)
      (asToken : TokenAt input.tokens input.endIndex input.cursor {
        span := asSpan
        value := .keyword .asKw
      })
      (nameToken : TokenAt input.tokens input.endIndex (input.cursor + 1) {
        span := name.span
        value := .identifier name.value
      })
      (tokensEq : output.tokens = input.tokens)
      (endIndexEq : output.endIndex = input.endIndex)
      (cursorEq : output.cursor = input.cursor + 2) :
      SelectedAliasParses input (some name) output

/-- Independent grammar of one import selector and its optional alias. -/
def SelectedImportParses
    (input : Remainder) (selection : Syntax.SelectedImport)
    (output : Remainder) : Prop :=
  ∃ afterSource,
    SelectorNameParses input selection.value.source afterSource ∧
    SelectedAliasParses afterSource selection.value.alias output ∧
    selection.span = match selection.value.alias with
      | none => selection.value.source.span
      | some alias =>
          SourceSpan.cover selection.value.source.span alias.span

/-- Independent grammar of one nonempty braced selected-import list. -/
def SelectedImportsParses
    (input : Remainder)
    (selection : NonemptyDelimitedList Syntax.SelectedImport)
    (output : Remainder) : Prop :=
  NonemptyTrailingDelimitedListParses .leftBrace .rightBrace
    SelectedImportParses input {
      span := selection.span
      elements := selection.elements.toList
    } output

/-- Independent grammar of one nonempty braced selector-name list. -/
def NonemptySelectorListParses
    (input : Remainder) (names : NonemptyList Syntax.SelectorName)
    (listSpan : SourceSpan) (output : Remainder) : Prop :=
  NonemptyTrailingDelimitedListParses .leftBrace .rightBrace
    SelectorNameParses input {
      span := listSpan
      elements := names.toList
    } output

/-- Exact grammar of one nonempty `hiding { ... }` clause. -/
def HidingClauseParses
    (input : Remainder) (clause : Syntax.HidingClause)
    (output : Remainder) : Prop :=
  ∃ markerSpan listSpan,
    TokenAt input.tokens input.endIndex input.cursor {
      span := markerSpan
      value := .identifier ContextualKeyword.hiding.spelling
    } ∧
    NonemptySelectorListParses { input with cursor := input.cursor + 1 }
      clause.value.names listSpan output ∧
    clause.span = SourceSpan.cover markerSpan listSpan

/-- Maximal optional grammar for a trailing hiding clause. -/
inductive OptionalHidingParses :
    Remainder → Option Syntax.HidingClause → Remainder → Prop where
  | absent {input : Remainder}
      (stopped : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.hiding.spelling)) :
      OptionalHidingParses input none input
  | present {input output : Remainder} {clause : Syntax.HidingClause}
      (parsed : HidingClauseParses input clause output) :
      OptionalHidingParses input (some clause) output

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

/-- Grammar after `import` for `* from ModulePath ;` without hiding. -/
def WildcardImportNoHidingTailParses (startSpan : SourceSpan)
    (input : Remainder) (declaration : Syntax.ImportDecl)
    (output : Remainder) : Prop :=
  ∃ starSpan fromSpan path afterPath semicolonSpan,
    TokenAt input.tokens input.endIndex input.cursor {
      span := starSpan
      value := .symbol .star
    } ∧
    TokenAt input.tokens input.endIndex (input.cursor + 1) {
      span := fromSpan
      value := .identifier ContextualKeyword.from.spelling
    } ∧
    ModulePathParses { input with cursor := input.cursor + 2 }
      path afterPath ∧
    TokenAt afterPath.tokens afterPath.endIndex afterPath.cursor {
      span := semicolonSpan
      value := .symbol .semicolon
    } ∧
    output = { afterPath with cursor := afterPath.cursor + 1 } ∧
    declaration = {
      span := SourceSpan.cover startSpan semicolonSpan
      value := .wildcard path none
    }

/-- Independent recognition judgment for a complete wildcard import without hiding. -/
def WildcardImportNoHidingDeclParses
    (input : Remainder) (declaration : Syntax.ImportDecl)
    (output : Remainder) : Prop :=
  ∃ keywordSpan,
    TokenAt input.tokens input.endIndex input.cursor {
      span := keywordSpan
      value := .keyword .importKw
    } ∧
    WildcardImportNoHidingTailParses keywordSpan
      { input with cursor := input.cursor + 1 } declaration output

/-- Grammar after `import` for a wildcard import with optional hiding. -/
def WildcardImportTailParses (startSpan : SourceSpan)
    (input : Remainder) (declaration : Syntax.ImportDecl)
    (output : Remainder) : Prop :=
  ∃ starSpan fromSpan path afterPath hidden afterHidden semicolonSpan,
    TokenAt input.tokens input.endIndex input.cursor {
      span := starSpan
      value := .symbol .star
    } ∧
    TokenAt input.tokens input.endIndex (input.cursor + 1) {
      span := fromSpan
      value := .identifier ContextualKeyword.from.spelling
    } ∧
    ModulePathParses { input with cursor := input.cursor + 2 }
      path afterPath ∧
    OptionalHidingParses afterPath hidden afterHidden ∧
    TokenAt afterHidden.tokens afterHidden.endIndex afterHidden.cursor {
      span := semicolonSpan
      value := .symbol .semicolon
    } ∧
    output = { afterHidden with cursor := afterHidden.cursor + 1 } ∧
    declaration = {
      span := SourceSpan.cover startSpan semicolonSpan
      value := .wildcard path hidden
    }

/-- Independent recognition judgment for a complete wildcard import. -/
def WildcardImportDeclParses
    (input : Remainder) (declaration : Syntax.ImportDecl)
    (output : Remainder) : Prop :=
  ∃ keywordSpan,
    TokenAt input.tokens input.endIndex input.cursor {
      span := keywordSpan
      value := .keyword .importKw
    } ∧
    WildcardImportTailParses keywordSpan
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
