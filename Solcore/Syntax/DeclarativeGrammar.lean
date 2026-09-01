import Solcore.Syntax.Declaration

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

/-- Exact grammar of one checked identifier occurrence. -/
def IdentifierParses
    (input : Remainder) (name : Identifier) (output : Remainder) : Prop :=
  TokenAt input.tokens input.endIndex input.cursor {
      span := name.span
      value := .identifier name.value
    } ∧
    output.tokens = input.tokens ∧
    output.endIndex = input.endIndex ∧
    output.cursor = input.cursor + 1

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

/-- No dot followed by an identifier begins at one active-window cursor. -/
def DotIdentifierAbsentAt
    (tokens : Array Token) (endIndex cursor : Nat) : Prop :=
  ¬ ∃ dotSpan componentSpan text,
    TokenAt tokens endIndex cursor {
      span := dotSpan
      value := .symbol .dot
    } ∧
    TokenAt tokens endIndex (cursor + 1) {
      span := componentSpan
      value := .identifier text
    }

/-- Forward dotted tail of an export path, stopping before selection suffixes. -/
inductive ExportPathTailParses
    (tokens : Array Token) (endIndex : Nat) :
    Nat → List Identifier → Nat → Prop where
  | done (cursor : Nat)
      (stopped : DotIdentifierAbsentAt tokens endIndex cursor) :
      ExportPathTailParses tokens endIndex cursor [] cursor
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
      (tail : ExportPathTailParses tokens endIndex (cursor + 2)
        components finish) :
      ExportPathTailParses tokens endIndex cursor
        (component :: components) finish

/-- Independent maximal grammar of one export module path. -/
def ExportPathParses
    (input : Remainder) (path : Syntax.QualifiedName)
    (output : Remainder) : Prop :=
  output.tokens = input.tokens ∧
    output.endIndex = input.endIndex ∧
    TokenAt input.tokens input.endIndex input.cursor {
      span := path.value.components.head.span
      value := .identifier path.value.components.head.value
    } ∧
    ExportPathTailParses input.tokens input.endIndex (input.cursor + 1)
      path.value.components.tail output.cursor ∧
    path.span = SourceSpan.cover path.value.components.head.span
      (finalIdentifier path.value.components.head
        path.value.components.tail).span

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

/--
Independent grammar of a possibly empty comma-separated list with an optional
final comma.  The nonempty branch records that the parser's preferred empty
branch did not match immediately after the opening delimiter.
-/
inductive TrailingDelimitedListParses {α : Type}
    (opening closing : Symbol)
    (elementParses : Remainder → α → Remainder → Prop) :
    Remainder → DelimitedList α → Remainder → Prop where
  | empty {input : Remainder} (openingSpan closingSpan : SourceSpan)
      (openingToken : TokenAt input.tokens input.endIndex input.cursor {
        span := openingSpan
        value := .symbol opening
      })
      (closingToken : TokenAt input.tokens input.endIndex (input.cursor + 1) {
        span := closingSpan
        value := .symbol closing
      }) :
      TrailingDelimitedListParses opening closing elementParses input {
        span := SourceSpan.cover openingSpan closingSpan
        elements := []
      } { input with cursor := input.cursor + 2 }
  | nonempty {input output : Remainder} {values : DelimitedList α}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        (input.cursor + 1) (.symbol closing))
      (parsed : NonemptyTrailingDelimitedListParses opening closing
        elementParses input values output) :
      TrailingDelimitedListParses opening closing elementParses input values
        output

/-- Forward-order tail grammar for a list that rejects a final comma. -/
inductive NoTrailingDelimitedTailParses {α : Type}
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
      NoTrailingDelimitedTailParses closing elementParses input [] closingSpan
        { input with cursor := input.cursor + 1 }
  | next {input afterElement output : Remainder}
      {commaSpan closingSpan : SourceSpan} {element : α}
      {elements : List α}
      (commaToken : TokenAt input.tokens input.endIndex input.cursor {
        span := commaSpan
        value := .symbol .comma
      })
      (elementParsed : elementParses
        { input with cursor := input.cursor + 1 } element afterElement)
      (progress : input.cursor + 1 < afterElement.cursor)
      (tail : NoTrailingDelimitedTailParses closing elementParses afterElement
        elements closingSpan output) :
      NoTrailingDelimitedTailParses closing elementParses input
        (element :: elements) closingSpan output

/--
Independent grammar of a nonempty comma-separated list that rejects a final
comma.  The parser does not inspect the closing token after a comma; it calls
the element parser directly, so the recursive case carries no closing-absence
premise.
-/
def NonemptyNoTrailingDelimitedListParses {α : Type}
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
    NoTrailingDelimitedTailParses closing elementParses afterFirst rest
      closingSpan output ∧
    values.elements = first :: rest ∧
    values.span = SourceSpan.cover openingSpan closingSpan

/--
Independent grammar of a possibly empty comma-separated list that rejects a
final comma.  The nonempty branch records that the parser's preferred empty
branch did not match immediately after the opening delimiter.
-/
inductive NoTrailingDelimitedListParses {α : Type}
    (opening closing : Symbol)
    (elementParses : Remainder → α → Remainder → Prop) :
    Remainder → DelimitedList α → Remainder → Prop where
  | empty {input : Remainder} (openingSpan closingSpan : SourceSpan)
      (openingToken : TokenAt input.tokens input.endIndex input.cursor {
        span := openingSpan
        value := .symbol opening
      })
      (closingToken : TokenAt input.tokens input.endIndex (input.cursor + 1) {
        span := closingSpan
        value := .symbol closing
      }) :
      NoTrailingDelimitedListParses opening closing elementParses input {
        span := SourceSpan.cover openingSpan closingSpan
        elements := []
      } { input with cursor := input.cursor + 2 }
  | nonempty {input output : Remainder} {values : DelimitedList α}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        (input.cursor + 1) (.symbol closing))
      (parsed : NonemptyNoTrailingDelimitedListParses opening closing
        elementParses input values output) :
      NoTrailingDelimitedListParses opening closing elementParses input values
        output

/-- Exact nonempty constructor-name list between parentheses. -/
def ConstructorNamesParses
    (input : Remainder) (constructors : NonemptyList Identifier)
    (span : SourceSpan) (output : Remainder) : Prop :=
  NonemptyNoTrailingDelimitedListParses .leftParen .rightParen
    IdentifierParses input {
      span
      elements := constructors.toList
    } output

/-- Independent grammar of an all-or-named constructor selection. -/
inductive ConstructorSelectionParses :
    Remainder → Syntax.ConstructorSelection → Remainder → Prop where
  | all {input : Remainder}
      (openingSpan markerSpan closingSpan : SourceSpan)
      (openingToken : TokenAt input.tokens input.endIndex input.cursor {
        span := openingSpan
        value := .symbol .leftParen
      })
      (markerToken : TokenAt input.tokens input.endIndex (input.cursor + 1) {
        span := markerSpan
        value := .symbol .star
      })
      (closingToken : TokenAt input.tokens input.endIndex (input.cursor + 2) {
        span := closingSpan
        value := .symbol .rightParen
      }) :
      ConstructorSelectionParses input {
        span := SourceSpan.cover openingSpan closingSpan
        value := .all markerSpan
      } { input with cursor := input.cursor + 3 }
  | named {input output : Remainder} {constructors : NonemptyList Identifier}
      {span : SourceSpan}
      (namesParsed : ConstructorNamesParses input constructors span output) :
      ConstructorSelectionParses input {
        span
        value := .named constructors
      } output

/-- Maximal optional constructor selection following one exported name. -/
inductive OptionalConstructorSelectionParses :
    Remainder → Option Syntax.ConstructorSelection → Remainder → Prop where
  | absent {input : Remainder}
      (stopped : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .leftParen)) :
      OptionalConstructorSelectionParses input none input
  | present {input output : Remainder}
      {selection : Syntax.ConstructorSelection}
      (parsed : ConstructorSelectionParses input selection output) :
      OptionalConstructorSelectionParses input (some selection) output

/-- Independent grammar of one wildcard, operator, or identifier export name. -/
inductive ExportNameParses :
    Remainder → Syntax.ExportName → Remainder → Prop where
  | wildcard {input : Remainder} (markerSpan : SourceSpan)
      (markerToken : TokenAt input.tokens input.endIndex input.cursor {
        span := markerSpan
        value := .symbol .star
      }) :
      ExportNameParses input {
        span := markerSpan
        value := .wildcard markerSpan
      } { input with cursor := input.cursor + 1 }
  | operator {input output : Remainder} {span : SourceSpan}
      {spelling : String}
      (starAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .star))
      (parsed : OperatorSelectorParses input {
        span
        value := .operator spelling
      } output) :
      ExportNameParses input {
        span
        value := .operator { span, value := spelling }
      } output
  | identifier {input afterName output : Remainder}
      {name : Identifier}
      {constructors : Option Syntax.ConstructorSelection}
      (starAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .star))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (nameParsed : IdentifierParses input name afterName)
      (constructorsParsed : OptionalConstructorSelectionParses afterName
        constructors output) :
      ExportNameParses input {
        span := match constructors with
          | none => name.span
          | some selection => SourceSpan.cover name.span selection.span
        value := .identifier name constructors
      } output

/-- No identifier followed by a dot begins at one active-window cursor. -/
def IdentifierDotAbsentAt
    (tokens : Array Token) (endIndex cursor : Nat) : Prop :=
  ¬ ∃ identifierSpan dotSpan text,
    TokenAt tokens endIndex cursor {
      span := identifierSpan
      value := .identifier text
    } ∧
    TokenAt tokens endIndex (cursor + 1) {
      span := dotSpan
      value := .symbol .dot
    }

/-- Independent grammar of one local export name or qualified wildcard. -/
inductive LocalExportItemParses :
    Remainder → Syntax.LocalExportItem → Remainder → Prop where
  | moduleWildcard {input afterPath : Remainder}
      {path : Syntax.QualifiedName}
      (dotSpan markerSpan : SourceSpan)
      (pathParsed : ExportPathParses input path afterPath)
      (dotToken : TokenAt afterPath.tokens afterPath.endIndex
        afterPath.cursor {
          span := dotSpan
          value := .symbol .dot
        })
      (markerToken : TokenAt afterPath.tokens afterPath.endIndex
        (afterPath.cursor + 1) {
          span := markerSpan
          value := .symbol .star
        }) :
      LocalExportItemParses input {
        span := SourceSpan.cover path.span markerSpan
        value := .moduleWildcard path markerSpan
      } { afterPath with cursor := afterPath.cursor + 2 }
  | name {input output : Remainder} {name : Syntax.ExportName}
      (qualifiedAbsent : IdentifierDotAbsentAt input.tokens input.endIndex
        input.cursor)
      (nameParsed : ExportNameParses input name output) :
      LocalExportItemParses input {
        span := name.span
        value := .name name
      } output

/-- Independent grammar of a wildcard or braced remote export selection. -/
inductive ExportSelectionParses :
    Remainder → Syntax.ExportSelection → Remainder → Prop where
  | wildcard {input : Remainder} (markerSpan : SourceSpan)
      (markerToken : TokenAt input.tokens input.endIndex input.cursor {
        span := markerSpan
        value := .symbol .star
      }) :
      ExportSelectionParses input {
        span := markerSpan
        value := .wildcard markerSpan
      } { input with cursor := input.cursor + 1 }
  | selected {input output : Remainder}
      {items : DelimitedList Syntax.ExportName}
      (starAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .star))
      (itemsParsed : TrailingDelimitedListParses .leftBrace .rightBrace
        ExportNameParses input items output) :
      ExportSelectionParses input {
        span := items.span
        value := .selected items
      } output

/-- Exact semicolon and covering span that finish one export payload. -/
def FinishExportParses (start : SourceSpan) (value : Syntax.ExportDeclValue)
    (input : Remainder) (declaration : Syntax.ExportDecl)
    (output : Remainder) : Prop :=
  ∃ semicolonSpan,
    TokenAt input.tokens input.endIndex input.cursor {
      span := semicolonSpan
      value := .symbol .semicolon
    } ∧
    output = { input with cursor := input.cursor + 1 } ∧
    declaration = {
      span := SourceSpan.cover start semicolonSpan
      value
    }

/-- Grammar after `export` for one braced list of local items. -/
def LocalExportTailParses (start : SourceSpan)
    (input : Remainder) (declaration : Syntax.ExportDecl)
    (output : Remainder) : Prop :=
  ∃ items afterItems,
    TrailingDelimitedListParses .leftBrace .rightBrace LocalExportItemParses
      input items afterItems ∧
    FinishExportParses start (.local items) afterItems declaration output

/-- Grammar after `export` for a path followed by a remote selection. -/
def ItemsFromExportTailParses (start : SourceSpan)
    (input : Remainder) (declaration : Syntax.ExportDecl)
    (output : Remainder) : Prop :=
  ∃ path afterPath dotSpan selection afterSelection,
    ExportPathParses input path afterPath ∧
    TokenAt afterPath.tokens afterPath.endIndex afterPath.cursor {
      span := dotSpan
      value := .symbol .dot
    } ∧
    ExportSelectionParses
      { afterPath with cursor := afterPath.cursor + 1 }
      selection afterSelection ∧
    FinishExportParses start (.itemsFrom path selection) afterSelection
      declaration output

/-- Grammar after `export` for a path and `as` alias. -/
def ModuleAsExportTailParses (start : SourceSpan)
    (input : Remainder) (declaration : Syntax.ExportDecl)
    (output : Remainder) : Prop :=
  ∃ path afterPath asSpan alias afterAlias,
    ExportPathParses input path afterPath ∧
    TokenKindAbsentAt afterPath.tokens afterPath.endIndex afterPath.cursor
      (.symbol .dot) ∧
    TokenAt afterPath.tokens afterPath.endIndex afterPath.cursor {
      span := asSpan
      value := .keyword .asKw
    } ∧
    IdentifierParses { afterPath with cursor := afterPath.cursor + 1 }
      alias afterAlias ∧
    FinishExportParses start (.moduleAs path alias) afterAlias declaration
      output

/-- Grammar after `export` for a path with no selection or alias suffix. -/
def ModuleExportTailParses (start : SourceSpan)
    (input : Remainder) (declaration : Syntax.ExportDecl)
    (output : Remainder) : Prop :=
  ∃ path afterPath,
    ExportPathParses input path afterPath ∧
    TokenKindAbsentAt afterPath.tokens afterPath.endIndex afterPath.cursor
      (.symbol .dot) ∧
    TokenKindAbsentAt afterPath.tokens afterPath.endIndex afterPath.cursor
      (.keyword .asKw) ∧
    FinishExportParses start (.module path) afterPath declaration output

/-- Parser-independent union of the three path-export suffix forms. -/
inductive PathExportTailParses (start : SourceSpan) :
    Remainder → Syntax.ExportDecl → Remainder → Prop where
  | itemsFrom {input output : Remainder}
      {declaration : Syntax.ExportDecl}
      (parsed : ItemsFromExportTailParses start input declaration output) :
      PathExportTailParses start input declaration output
  | moduleAs {input output : Remainder}
      {declaration : Syntax.ExportDecl}
      (parsed : ModuleAsExportTailParses start input declaration output) :
      PathExportTailParses start input declaration output
  | module {input output : Remainder}
      {declaration : Syntax.ExportDecl}
      (parsed : ModuleExportTailParses start input declaration output) :
      PathExportTailParses start input declaration output

/-- Independent recognition judgment for one complete local export. -/
def LocalExportDeclParses
    (input : Remainder) (declaration : Syntax.ExportDecl)
    (output : Remainder) : Prop :=
  ∃ keywordSpan,
    TokenAt input.tokens input.endIndex input.cursor {
      span := keywordSpan
      value := .keyword .exportKw
    } ∧
    LocalExportTailParses keywordSpan
      { input with cursor := input.cursor + 1 } declaration output

/-- Independent recognition judgment for an items-from-module export. -/
def ItemsFromExportDeclParses
    (input : Remainder) (declaration : Syntax.ExportDecl)
    (output : Remainder) : Prop :=
  ∃ keywordSpan,
    TokenAt input.tokens input.endIndex input.cursor {
      span := keywordSpan
      value := .keyword .exportKw
    } ∧
    TokenKindAbsentAt input.tokens input.endIndex (input.cursor + 1)
      (.symbol .leftBrace) ∧
    ItemsFromExportTailParses keywordSpan
      { input with cursor := input.cursor + 1 } declaration output

/-- Independent recognition judgment for a module-alias export. -/
def ModuleAsExportDeclParses
    (input : Remainder) (declaration : Syntax.ExportDecl)
    (output : Remainder) : Prop :=
  ∃ keywordSpan,
    TokenAt input.tokens input.endIndex input.cursor {
      span := keywordSpan
      value := .keyword .exportKw
    } ∧
    TokenKindAbsentAt input.tokens input.endIndex (input.cursor + 1)
      (.symbol .leftBrace) ∧
    ModuleAsExportTailParses keywordSpan
      { input with cursor := input.cursor + 1 } declaration output

/-- Independent recognition judgment for a plain module export. -/
def ModuleExportDeclParses
    (input : Remainder) (declaration : Syntax.ExportDecl)
    (output : Remainder) : Prop :=
  ∃ keywordSpan,
    TokenAt input.tokens input.endIndex input.cursor {
      span := keywordSpan
      value := .keyword .exportKw
    } ∧
    TokenKindAbsentAt input.tokens input.endIndex (input.cursor + 1)
      (.symbol .leftBrace) ∧
    ModuleExportTailParses keywordSpan
      { input with cursor := input.cursor + 1 } declaration output

/-- Parser-independent union of the four complete canonical export forms. -/
inductive ExportDeclParses :
    Remainder → Syntax.ExportDecl → Remainder → Prop where
  | ofLocal {input output : Remainder} {declaration : Syntax.ExportDecl}
      (parsed : LocalExportDeclParses input declaration output) :
      ExportDeclParses input declaration output
  | ofModule {input output : Remainder} {declaration : Syntax.ExportDecl}
      (parsed : ModuleExportDeclParses input declaration output) :
      ExportDeclParses input declaration output
  | ofModuleAs {input output : Remainder} {declaration : Syntax.ExportDecl}
      (parsed : ModuleAsExportDeclParses input declaration output) :
      ExportDeclParses input declaration output
  | ofItemsFrom {input output : Remainder}
      {declaration : Syntax.ExportDecl}
      (parsed : ItemsFromExportDeclParses input declaration output) :
      ExportDeclParses input declaration output

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

/-- Grammar after `import` for a selected import with optional hiding. -/
def SelectiveImportTailParses (startSpan : SourceSpan)
    (input : Remainder) (declaration : Syntax.ImportDecl)
    (output : Remainder) : Prop :=
  ∃ selection afterSelection fromSpan path afterPath hidden afterHidden
      semicolonSpan,
    SelectedImportsParses input selection afterSelection ∧
    TokenAt afterSelection.tokens afterSelection.endIndex
      afterSelection.cursor {
        span := fromSpan
        value := .identifier ContextualKeyword.from.spelling
      } ∧
    ModulePathParses
      { afterSelection with cursor := afterSelection.cursor + 1 }
      path afterPath ∧
    OptionalHidingParses afterPath hidden afterHidden ∧
    TokenAt afterHidden.tokens afterHidden.endIndex afterHidden.cursor {
      span := semicolonSpan
      value := .symbol .semicolon
    } ∧
    output = { afterHidden with cursor := afterHidden.cursor + 1 } ∧
    declaration = {
      span := SourceSpan.cover startSpan semicolonSpan
      value := .selected selection path hidden
    }

/-- Independent recognition judgment for one complete selected import. -/
def SelectiveImportDeclParses
    (input : Remainder) (declaration : Syntax.ImportDecl)
    (output : Remainder) : Prop :=
  ∃ keywordSpan,
    TokenAt input.tokens input.endIndex input.cursor {
      span := keywordSpan
      value := .keyword .importKw
    } ∧
    SelectiveImportTailParses keywordSpan
      { input with cursor := input.cursor + 1 } declaration output

/-- Parser-independent union of the four complete canonical import forms. -/
inductive ImportDeclParses :
    Remainder → Syntax.ImportDecl → Remainder → Prop where
  | ofPlain {input output : Remainder} {declaration : Syntax.ImportDecl}
      (parsed : PlainImportDeclParses input declaration output) :
      ImportDeclParses input declaration output
  | ofNamespace {input output : Remainder} {declaration : Syntax.ImportDecl}
      (parsed : NamespaceImportDeclParses input declaration output) :
      ImportDeclParses input declaration output
  | ofWildcard {input output : Remainder} {declaration : Syntax.ImportDecl}
      (parsed : WildcardImportDeclParses input declaration output) :
      ImportDeclParses input declaration output
  | ofSelected {input output : Remainder} {declaration : Syntax.ImportDecl}
      (parsed : SelectiveImportDeclParses input declaration output) :
      ImportDeclParses input declaration output

/-! Derive targets retain reserved-keyword recovery without parser details. -/

/-- Hard keywords retained as diagnosed components of a derive target. -/
def ReservedDeriveTargetKeyword : HardKeyword → Prop
  | .importKw | .exportKw | .pragmaKw | .typeKw | .dataKw
  | .classKw | .instanceKw | .contractKw | .publicKw | .payableKw
  | .functionKw | .constructorKw | .fallbackKw | .forallKw
  | .defaultKw => True
  | _ => False

/-- Exact grammar of one ordinary or diagnosed reserved derive component. -/
inductive DeriveComponentParses :
    Remainder → Identifier → Remainder → Prop where
  | identifier {input output : Remainder} {name : Identifier}
      (parsed : IdentifierParses input name output) :
      DeriveComponentParses input name output
  | reserved {input : Remainder} (keyword : HardKeyword)
      (allowed : ReservedDeriveTargetKeyword keyword)
      (span : SourceSpan)
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .keyword keyword
      }) :
      DeriveComponentParses input {
        span
        value := keyword.spelling
      } { input with cursor := input.cursor + 1 }

/-- Maximal forward dotted tail of one derive target. -/
inductive DeriveTargetTailParses :
    Remainder → List Identifier → Remainder → Prop where
  | done {input : Remainder}
      (stopped : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot)) :
      DeriveTargetTailParses input [] input
  | next {input afterComponent output : Remainder}
      {component : Identifier} {components : List Identifier}
      (dotSpan : SourceSpan)
      (dotToken : TokenAt input.tokens input.endIndex input.cursor {
        span := dotSpan
        value := .symbol .dot
      })
      (componentParsed : DeriveComponentParses
        { input with cursor := input.cursor + 1 }
        component afterComponent)
      (tail : DeriveTargetTailParses afterComponent components output) :
      DeriveTargetTailParses input (component :: components) output

/-- Independent maximal grammar of one dotted derive target. -/
def DeriveTargetParses
    (input : Remainder) (target : Syntax.DeriveTarget)
    (output : Remainder) : Prop :=
  ∃ first afterFirst components,
    DeriveComponentParses input first afterFirst ∧
    DeriveTargetTailParses afterFirst components output ∧
    target = {
      span := SourceSpan.cover first.span
        (finalIdentifier first components).span
      value := { components := { head := first, tail := components } }
    }

/--
Independent grammar of the normal `#[derive(...)]` path.  Empty target lists
and reserved target components remain represented here because the executable
normal path retains them with diagnostics; the public parser soundness theorem
uses diagnostic freedom to exclude recovery as a whole.
-/
def DeriveAttributeParses
    (input : Remainder) (value : Syntax.DeriveAttribute)
    (output : Remainder) : Prop :=
  ∃ hashSpan bracketSpan deriveSpan targets afterTargets closingSpan,
    TokenAt input.tokens input.endIndex input.cursor {
      span := hashSpan
      value := .symbol .hash
    } ∧
    TokenAt input.tokens input.endIndex (input.cursor + 1) {
      span := bracketSpan
      value := .symbol .leftBracket
    } ∧
    TokenAt input.tokens input.endIndex (input.cursor + 2) {
      span := deriveSpan
      value := .identifier ContextualKeyword.derive.spelling
    } ∧
    NoTrailingDelimitedListParses .leftParen .rightParen DeriveTargetParses
      { input with cursor := input.cursor + 3 } targets afterTargets ∧
    TokenAt afterTargets.tokens afterTargets.endIndex afterTargets.cursor {
      span := closingSpan
      value := .symbol .rightBracket
    } ∧
    output = { afterTargets with cursor := afterTargets.cursor + 1 } ∧
    value = {
      span := SourceSpan.cover hashSpan closingSpan
      value := { targets }
    }

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
