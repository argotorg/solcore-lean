import Solcore.Syntax.Trivia
import Solcore.Syntax.Parser.Diagnostic
import Solcore.Syntax.Lexer.Contract
import Solcore.Syntax.Declaration

/-!
Foundations of the declarative grammar.

The grammar describes accepted token slices without referring to parser functions.
Main declarations:
- tokens: `Remainder`, `TokenAt`, `ExactTokenParses`, `IdentifierParses`,
  `QualifiedNameParses`;
- outcome contracts: `DeterministicOutcomeSpec`, `ExactDeterministicOutcomeSpec`;
- lexical carriers: `LexedFileValidationAccepts`, `LexedFileValidationRejects`;
- diagnostic filtering: `LexicalCascadeFilters`, `ParseDiagnosticCascadeFilters`.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeDiagnosticCascadeGrammar
/-! Independent lexical-cascade suppression for diagnostic spans known to be
ordinary failure or recovery events. Order and duplicate spans are retained;
protected constraint, identifier, and nesting events are outside this relation. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The cascade policy counts LF only; an invalid UTF-8 prefix has index zero. -/
def cascadeLineIndex (source : String) (offset : Nat) : Nat :=
  match Trivia.utf8Slice? source 0 offset with
  | some leading => leading.toList.count '\n'
  | none => 0

/-- An ordered, valid gap consists of Rust whitespace other than CR or LF. -/
def HorizontalWhitespaceGap (source : String)
    (lexical parsed : SourceSpan) : Prop :=
  lexical.endByte ≤ parsed.startByte ∧
    ∃ gap, Trivia.utf8Slice? source lexical.endByte parsed.startByte = some gap ∧
      (gap.toList.all fun character =>
        Trivia.isRustWhitespace character && character != '\n' && character != '\r') = true

/-- Exact source and range conditions making an ordinary parse event a cascade.
The inclusive lexical endpoint and the LF-only line rule are intentional. -/
def LexicalSpanSuppresses (source : String) (lexical parsed : SourceSpan) : Prop :=
  lexical.source = parsed.source ∧
    (cascadeLineIndex source lexical.startByte =
        cascadeLineIndex source parsed.startByte ∨
      (lexical.startByte < parsed.endByte ∧ parsed.startByte < lexical.endByte) ∨
      (lexical.startByte ≤ parsed.startByte ∧ parsed.startByte ≤ lexical.endByte) ∨
      HorizontalWhitespaceGap source lexical parsed)

/-- At least one retained lexical range suppresses this candidate event. -/
def LexicalCascadeSuppresses (source : String) (lexical : List SourceSpan)
    (parsed : SourceSpan) : Prop :=
  ∃ span ∈ lexical, LexicalSpanSuppresses source span parsed

/-- Source-ordered filtering of candidate event spans, preserving duplicates. -/
inductive LexicalCascadeFilters (source : String) (lexical : List SourceSpan) :
    List SourceSpan → List SourceSpan → Prop where
  | nil : LexicalCascadeFilters source lexical [] []
  | keep {span : SourceSpan} {raw kept : List SourceSpan}
      (retained : ¬ LexicalCascadeSuppresses source lexical span)
      (tail : LexicalCascadeFilters source lexical raw kept) :
      LexicalCascadeFilters source lexical (span :: raw) (span :: kept)
  | drop {span : SourceSpan} {raw kept : List SourceSpan}
      (suppressed : LexicalCascadeSuppresses source lexical span)
      (tail : LexicalCascadeFilters source lexical raw kept) :
      LexicalCascadeFilters source lexical (span :: raw) kept

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeParseDiagnosticCascadeGrammar
/-! Independent normalization of complete, potentially mixed diagnostic traces.
The diagnostic catalog is shared data, not a parser or an execution witness. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Only unexpected-token reports and recovery events have cascade provenance.
Identifier, grammar-constraint, and nesting reports are always protected. -/
def LexicalCascadeCandidate : ParseDiagnosticKind → Prop
  | .unexpected .. | .recovered .. => True
  | _ => False

/-- A removable report needs both a candidate kind and a lexical span witness. -/
def ParseDiagnosticCascadeSuppresses (source : String)
    (lexical : List SourceSpan) (diagnostic : ParseDiagnostic) : Prop :=
  LexicalCascadeCandidate diagnostic.kind ∧
    LexicalCascadeSuppresses source lexical diagnostic.span

/-- Keep or drop each complete report in place, preserving metadata and duplicates. -/
inductive ParseDiagnosticCascadeFilters (source : String) (lexical : List SourceSpan) :
    List ParseDiagnostic → List ParseDiagnostic → Prop where
  | nil : ParseDiagnosticCascadeFilters source lexical [] []
  | keep {diagnostic : ParseDiagnostic} {raw kept : List ParseDiagnostic}
      (retained : ¬ ParseDiagnosticCascadeSuppresses source lexical diagnostic)
      (tail : ParseDiagnosticCascadeFilters source lexical raw kept) :
      ParseDiagnosticCascadeFilters source lexical (diagnostic :: raw) (diagnostic :: kept)
  | drop {diagnostic : ParseDiagnostic} {raw kept : List ParseDiagnostic}
      (suppressed : ParseDiagnosticCascadeSuppresses source lexical diagnostic)
      (tail : ParseDiagnosticCascadeFilters source lexical raw kept) :
      ParseDiagnosticCascadeFilters source lexical (diagnostic :: raw) kept

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeLexedValidationOutcomeGrammar
/-!
Parser-independent exact outcomes for validating an already-tokenized source.
The relations stop at the first invalid span and preserve the public preflight
priority: source identity, tokens, comments, then lexical diagnostics.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- An exact source-order location reported by a validation scan. -/
structure IndexedSpan where
  index : Nat
  span : SourceSpan
  deriving Repr, BEq, DecidableEq

/-- Parser-neutral failures of already-tokenized source validation. -/
inductive LexedValidationFailure where
  | sourceMismatch (expected actual : SourceId)
  | invalidTokenSpan (index : Nat) (span : SourceSpan)
  | invalidCommentSpan (index : Nat) (span : SourceSpan)
  | invalidLexicalDiagnosticSpan (index : Nat) (span : SourceSpan)
  deriving Repr, BEq, DecidableEq

/-- Exact acceptance condition for one ordered, nonempty source span. -/
def OrderedSpanAccepted (file : SourceFile) (previousEnd : Nat)
    (span : SourceSpan) : Prop :=
  span.ValidFor file ∧
    previousEnd ≤ span.startByte ∧
    span.startByte < span.endByte

/-- Scan source-ordered spans, returning the first invalid indexed span. -/
inductive OrderedSpanValidationScans {α : Type} (file : SourceFile)
    (spanOf : α → SourceSpan) :
    Nat → Nat → List α → Option IndexedSpan → Prop where
  | done {index previousEnd : Nat} :
      OrderedSpanValidationScans file spanOf index previousEnd [] none
  | rejected {index previousEnd : Nat} {item : α} {rest : List α}
      (invalid : ¬ OrderedSpanAccepted file previousEnd (spanOf item)) :
      OrderedSpanValidationScans file spanOf index previousEnd (item :: rest)
        (some { index := index, span := spanOf item })
  | continues {index previousEnd : Nat} {item : α} {rest : List α}
      {result : Option IndexedSpan}
      (accepted : OrderedSpanAccepted file previousEnd (spanOf item))
      (tail : OrderedSpanValidationScans file spanOf (index + 1)
        (spanOf item).endByte rest result) :
      OrderedSpanValidationScans file spanOf index previousEnd (item :: rest)
        result

/-- Scan pointwise source-owned spans, returning the first invalid one. -/
inductive SpanValidationScans {α : Type} (file : SourceFile)
    (spanOf : α → SourceSpan) :
    Nat → List α → Option IndexedSpan → Prop where
  | done {index : Nat} :
      SpanValidationScans file spanOf index [] none
  | rejected {index : Nat} {item : α} {rest : List α}
      (invalid : ¬ (spanOf item).ValidFor file) :
      SpanValidationScans file spanOf index (item :: rest)
        (some { index := index, span := spanOf item })
  | continues {index : Nat} {item : α} {rest : List α}
      {result : Option IndexedSpan}
      (accepted : (spanOf item).ValidFor file)
      (tail : SpanValidationScans file spanOf (index + 1) rest result) :
      SpanValidationScans file spanOf index (item :: rest) result

/-- Exact token-span scan used by whole-file validation. -/
abbrev TokenSpanValidationScans (file : SourceFile) :=
  OrderedSpanValidationScans file (fun token : Token => token.span)

/-- Exact comment-span scan used by whole-file validation. -/
abbrev CommentSpanValidationScans (file : SourceFile) :=
  OrderedSpanValidationScans file (fun comment : Comment => comment.span)

/-- Exact lexical-diagnostic span scan used by whole-file validation. -/
abbrev LexicalDiagnosticSpanValidationScans (file : SourceFile) :=
  SpanValidationScans file
    (fun diagnostic : LexicalDiagnostic => diagnostic.span)

/-- Exact priority-ordered outcome of validating one tokenized source file. -/
inductive LexedFileValidationOutcome (file : SourceFile)
    (lexed : LexedFile) : Option LexedValidationFailure → Prop where
  | sourceRejected (mismatch : lexed.source ≠ file.id) :
      LexedFileValidationOutcome file lexed
        (some (.sourceMismatch file.id lexed.source))
  | tokenRejected {invalid : IndexedSpan}
      (sourceAccepted : lexed.source = file.id)
      (tokens : TokenSpanValidationScans file 0 0 lexed.tokens
        (some invalid)) :
      LexedFileValidationOutcome file lexed
        (some (.invalidTokenSpan invalid.index invalid.span))
  | commentRejected {invalid : IndexedSpan}
      (sourceAccepted : lexed.source = file.id)
      (tokens : TokenSpanValidationScans file 0 0 lexed.tokens none)
      (comments : CommentSpanValidationScans file 0 0 lexed.comments
        (some invalid)) :
      LexedFileValidationOutcome file lexed
        (some (.invalidCommentSpan invalid.index invalid.span))
  | diagnosticRejected {invalid : IndexedSpan}
      (sourceAccepted : lexed.source = file.id)
      (tokens : TokenSpanValidationScans file 0 0 lexed.tokens none)
      (comments : CommentSpanValidationScans file 0 0 lexed.comments none)
      (diagnostics : LexicalDiagnosticSpanValidationScans file 0
        lexed.diagnostics (some invalid)) :
      LexedFileValidationOutcome file lexed
        (some (.invalidLexicalDiagnosticSpan invalid.index invalid.span))
  | accepted
      (sourceAccepted : lexed.source = file.id)
      (tokens : TokenSpanValidationScans file 0 0 lexed.tokens none)
      (comments : CommentSpanValidationScans file 0 0 lexed.comments none)
      (diagnostics : LexicalDiagnosticSpanValidationScans file 0
        lexed.diagnostics none) :
      LexedFileValidationOutcome file lexed none

/-- Whole-file validation accepts every retained lexical artifact. -/
def LexedFileValidationAccepts (file : SourceFile)
    (lexed : LexedFile) : Prop :=
  LexedFileValidationOutcome file lexed none

/-- Whole-file validation rejects with one exact first failure. -/
def LexedFileValidationRejects (file : SourceFile) (lexed : LexedFile)
    (failure : LexedValidationFailure) : Prop :=
  LexedFileValidationOutcome file lexed (some failure)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeGrammar
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

/-- Consume one exact token while retaining the immutable active window. -/
def ExactTokenParses (kind : TokenKind) (input : Remainder)
    (span : SourceSpan) (output : Remainder) : Prop :=
  TokenAt input.tokens input.endIndex input.cursor { span, value := kind } ∧
    output = { input with cursor := input.cursor + 1 }

/-- No requested contextual-word and following-symbol pair starts here. -/
def ContextualSymbolPairAbsentAt (input : Remainder)
    (keyword : ContextualKeyword) (symbol : Symbol) : Prop :=
  ¬ ∃ keywordSpan symbolSpan,
    TokenAt input.tokens input.endIndex input.cursor {
      span := keywordSpan
      value := .identifier keyword.spelling
    } ∧
    TokenAt input.tokens input.endIndex (input.cursor + 1) {
      span := symbolSpan
      value := .symbol symbol
    }

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

/-! Recursive grammar of canonical type-expression token shapes. -/

/-
Independent recursive grammar of every non-recovery type expression, together
with its concrete recursive delimiter and optional-suffix support judgments.

The concrete list judgments mirror `TrailingDelimitedListParses`.  They are
mutual because Lean's positivity checker cannot nest this recursive grammar
through the generic relation's parser parameter.
-/
mutual
  inductive TypeExprParses :
      Remainder → Syntax.TypeExpr → Remainder → Prop where
    | function {input afterKeyword afterParameters output : Remainder}
        {result : Syntax.TypeExpr}
        {parameters : DelimitedList Syntax.TypeExpr}
        {returns : Option (DelimitedList Syntax.TypeExpr)}
        (keywordSpan : SourceSpan)
        (keywordToken : ExactTokenParses (.keyword .functionKw)
          input keywordSpan afterKeyword)
        (resultEq : result = {
          span := SourceSpan.cover keywordSpan (match returns with
            | some values => values.span
            | none => parameters.span)
          value := .function keywordSpan parameters returns
        })
        (parametersParsed : TypeExprTrailingDelimitedListParses
          .leftParen .rightParen afterKeyword parameters afterParameters)
        (returnsParsed : OptionalFunctionTypeReturnsParses
          afterParameters returns output) :
        TypeExprParses input result output
    | comptime {input afterMarker afterOpening afterInner output : Remainder}
        {result : Syntax.TypeExpr}
        {inner : Syntax.TypeExpr}
        (markerSpan openingSpan closingSpan : SourceSpan)
        (markerToken : ExactTokenParses
          (.identifier ContextualKeyword.comptime.spelling)
          input markerSpan afterMarker)
        (openingToken : ExactTokenParses (.symbol .less)
          afterMarker openingSpan afterOpening)
        (closingToken : ExactTokenParses (.symbol .greater)
          afterInner closingSpan output)
        (resultEq : result = {
          span := SourceSpan.cover markerSpan closingSpan
          value := .comptime markerSpan
            (SourceSpan.cover openingSpan closingSpan) inner
        })
        (innerParsed : TypeExprParses afterOpening inner afterInner) :
        TypeExprParses input result output
    | mapping
        {input afterMarker afterOpening afterKey afterArrow afterValue output :
          Remainder}
        {result : Syntax.TypeExpr}
        {key value : Syntax.TypeExpr}
        (markerSpan openingSpan arrowSpan closingSpan : SourceSpan)
        (markerToken : ExactTokenParses
          (.identifier ContextualKeyword.mapping.spelling)
          input markerSpan afterMarker)
        (openingToken : ExactTokenParses (.symbol .leftParen)
          afterMarker openingSpan afterOpening)
        (arrowToken : ExactTokenParses (.symbol .fatArrow)
          afterKey arrowSpan afterArrow)
        (closingToken : ExactTokenParses (.symbol .rightParen)
          afterValue closingSpan output)
        (resultEq : result = {
          span := SourceSpan.cover markerSpan closingSpan
          value := .mapping markerSpan
            (SourceSpan.cover openingSpan closingSpan) key value
        })
        (keyParsed : TypeExprParses afterOpening key afterKey)
        (valueParsed : TypeExprParses afterArrow value afterValue) :
        TypeExprParses input result output
    | proxy {input afterMarker output : Remainder} {result inner : Syntax.TypeExpr}
        (markerSpan : SourceSpan)
        (markerToken : ExactTokenParses (.symbol .at)
          input markerSpan afterMarker)
        (resultEq : result = {
          span := SourceSpan.cover markerSpan inner.span
          value := .proxy markerSpan inner
        })
        (innerParsed : TypeExprParses afterMarker inner output) :
        TypeExprParses input result output
    | tuple {input output : Remainder}
        {result : Syntax.TypeExpr}
        {values : DelimitedList Syntax.TypeExpr}
        (resultEq : result = {
          span := values.span
          value := .tuple values.elements
        })
        (valuesParsed : TypeExprTrailingDelimitedListParses
          .leftParen .rightParen input values output) :
        TypeExprParses input result output
    | named {input afterName output : Remainder}
        {result : Syntax.TypeExpr}
        {name : Syntax.QualifiedName}
        {arguments : Option (NonemptyDelimitedList Syntax.TypeExpr)}
        (comptimeAbsent : ContextualSymbolPairAbsentAt
          input .comptime .less)
        (mappingAbsent : ContextualSymbolPairAbsentAt
          input .mapping .leftParen)
        (nameParsed : QualifiedNameParses input name afterName)
        (resultEq : result = {
          span := match arguments with
            | some values => SourceSpan.cover name.span values.span
            | none => name.span
          value := .named name arguments
        })
        (argumentsParsed : OptionalNamedTypeArgumentsParses
          afterName arguments output) :
        TypeExprParses input result output

  /-- Forward-order tail of a recursive type-expression delimiter list. -/
  inductive TypeExprTrailingDelimitedTailParses :
      Symbol → Remainder → List Syntax.TypeExpr → SourceSpan → Remainder →
        Prop where
    | close {closing : Symbol} {input : Remainder}
        {closingSpan : SourceSpan}
        (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex
          input.cursor (.symbol .comma))
        (closingToken : TokenAt input.tokens input.endIndex input.cursor {
          span := closingSpan
          value := .symbol closing
        }) :
        TypeExprTrailingDelimitedTailParses closing input [] closingSpan
          { input with cursor := input.cursor + 1 }
    | trailing {closing : Symbol} {input : Remainder}
        {commaSpan closingSpan : SourceSpan}
        (commaToken : TokenAt input.tokens input.endIndex input.cursor {
          span := commaSpan
          value := .symbol .comma
        })
        (closingToken : TokenAt input.tokens input.endIndex
          (input.cursor + 1) {
            span := closingSpan
            value := .symbol closing
          }) :
        TypeExprTrailingDelimitedTailParses closing input [] closingSpan
          { input with cursor := input.cursor + 2 }
    | next {closing : Symbol} {input afterElement output : Remainder}
        {commaSpan closingSpan : SourceSpan} {element : Syntax.TypeExpr}
        {elements values : List Syntax.TypeExpr}
        (commaToken : TokenAt input.tokens input.endIndex input.cursor {
          span := commaSpan
          value := .symbol .comma
        })
        (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
          (input.cursor + 1) (.symbol closing))
        (progress : input.cursor + 1 < afterElement.cursor)
        (elementsEq : values = element :: elements)
        (elementParsed : TypeExprParses
          { input with cursor := input.cursor + 1 } element afterElement)
        (tail : TypeExprTrailingDelimitedTailParses closing afterElement
          elements closingSpan output) :
        TypeExprTrailingDelimitedTailParses closing input
          values closingSpan output

  /-- Possibly empty recursive list with an optional trailing comma. -/
  inductive TypeExprTrailingDelimitedListParses :
      Symbol → Symbol → Remainder → DelimitedList Syntax.TypeExpr →
        Remainder → Prop where
    | empty {opening closing : Symbol} {input : Remainder}
        {values : DelimitedList Syntax.TypeExpr}
        (openingSpan closingSpan : SourceSpan)
        (elementsEq : values.elements = [])
        (spanEq : values.span = SourceSpan.cover openingSpan closingSpan)
        (openingToken : TokenAt input.tokens input.endIndex input.cursor {
          span := openingSpan
          value := .symbol opening
        })
        (closingToken : TokenAt input.tokens input.endIndex
          (input.cursor + 1) {
            span := closingSpan
            value := .symbol closing
          }) :
        TypeExprTrailingDelimitedListParses opening closing input values
          { input with cursor := input.cursor + 2 }
    | nonempty {opening closing : Symbol}
        {input afterFirst output : Remainder}
        {values : DelimitedList Syntax.TypeExpr}
        {first : Syntax.TypeExpr} {rest : List Syntax.TypeExpr}
        (openingSpan closingSpan : SourceSpan)
        (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
          (input.cursor + 1) (.symbol closing))
        (openingToken : TokenAt input.tokens input.endIndex input.cursor {
          span := openingSpan
          value := .symbol opening
        })
        (progress : input.cursor + 1 < afterFirst.cursor)
        (tokensEq : output.tokens = input.tokens)
        (endIndexEq : output.endIndex = input.endIndex)
        (elementsEq : values.elements = first :: rest)
        (spanEq : values.span = SourceSpan.cover openingSpan closingSpan)
        (firstParsed : TypeExprParses
          { input with cursor := input.cursor + 1 } first afterFirst)
        (tail : TypeExprTrailingDelimitedTailParses closing afterFirst rest
          closingSpan output) :
        TypeExprTrailingDelimitedListParses opening closing input values output

  /-- Optional, structurally nonempty generic arguments of a named type. -/
  inductive OptionalNamedTypeArgumentsParses :
      Remainder → Option (NonemptyDelimitedList Syntax.TypeExpr) →
        Remainder → Prop where
    | absent {input : Remainder}
        (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
          input.cursor (.symbol .less)) :
        OptionalNamedTypeArgumentsParses input none input
    | present {input afterFirst output : Remainder}
        {arguments : NonemptyDelimitedList Syntax.TypeExpr}
        {first : Syntax.TypeExpr} {rest : List Syntax.TypeExpr}
        (openingSpan closingSpan : SourceSpan)
        (openingToken : TokenAt input.tokens input.endIndex input.cursor {
          span := openingSpan
          value := .symbol .less
        })
        (progress : input.cursor + 1 < afterFirst.cursor)
        (tokensEq : output.tokens = input.tokens)
        (endIndexEq : output.endIndex = input.endIndex)
        (elementsEq : arguments.elements.toList = first :: rest)
        (spanEq : arguments.span =
          SourceSpan.cover openingSpan closingSpan)
        (firstParsed : TypeExprParses
          { input with cursor := input.cursor + 1 } first afterFirst)
        (tail : TypeExprTrailingDelimitedTailParses .greater afterFirst rest
          closingSpan output) :
        OptionalNamedTypeArgumentsParses input (some arguments) output

  /-- Optional `returns (...)` suffix of a function type. -/
  inductive OptionalFunctionTypeReturnsParses :
      Remainder → Option (DelimitedList Syntax.TypeExpr) → Remainder →
        Prop where
    | absent {input : Remainder}
        (returnsAbsent : TokenKindAbsentAt input.tokens input.endIndex
          input.cursor (.identifier ContextualKeyword.returns.spelling)) :
        OptionalFunctionTypeReturnsParses input none input
    | present {input afterMarker output : Remainder}
        {values : DelimitedList Syntax.TypeExpr} (markerSpan : SourceSpan)
        (markerToken : ExactTokenParses
          (.identifier ContextualKeyword.returns.spelling)
          input markerSpan afterMarker)
        (valuesParsed : TypeExprTrailingDelimitedListParses
          .leftParen .rightParen afterMarker values output) :
        OptionalFunctionTypeReturnsParses input (some values) output
end

/-! Grammar of named function parameters over recursive type expressions. -/

/-- No contextual `comptime` followed by an identifier starts here. -/
def ComptimeParameterPrefixAbsentAt (input : Remainder) : Prop :=
  ¬ ∃ markerSpan nameSpan name,
    TokenAt input.tokens input.endIndex input.cursor {
      span := markerSpan
      value := .identifier ContextualKeyword.comptime.spelling
    } ∧
    TokenAt input.tokens input.endIndex (input.cursor + 1) {
      span := nameSpan
      value := .identifier name
    }

/-- Exact non-recovery grammar of one typed named parameter. -/
inductive FunctionParameterParses :
    Remainder → Syntax.FunctionParameter → Remainder → Prop where
  | ordinary {input afterName afterColon output : Remainder}
      {name : Identifier} {type : Syntax.TypeExpr} (colonSpan : SourceSpan)
      (comptimePrefixAbsent : ComptimeParameterPrefixAbsentAt input)
      (nameParsed : IdentifierParses input name afterName)
      (colonToken : ExactTokenParses (.symbol .colon)
        afterName colonSpan afterColon)
      (typeParsed : TypeExprParses afterColon type output) :
      FunctionParameterParses input {
        span := SourceSpan.cover name.span type.span
        value := .typed none name type
      } output
  | comptime {input afterMarker afterName afterColon output : Remainder}
      {name : Identifier} {type : Syntax.TypeExpr}
      (markerSpan colonSpan : SourceSpan)
      (markerToken : ExactTokenParses
        (.identifier ContextualKeyword.comptime.spelling)
        input markerSpan afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (colonToken : ExactTokenParses (.symbol .colon)
        afterName colonSpan afterColon)
      (typeParsed : TypeExprParses afterColon type output) :
      FunctionParameterParses input {
        span := SourceSpan.cover markerSpan type.span
        value := .typed (some markerSpan) name type
      } output

/-- Possibly empty typed named parameters with an optional trailing comma. -/
def FunctionParametersParses
    (input : Remainder) (parameters : DelimitedList Syntax.FunctionParameter)
    (output : Remainder) : Prop :=
  TrailingDelimitedListParses .leftParen .rightParen
    FunctionParameterParses input parameters output

/-! Grammar of one trait predicate over recursive type expressions. -/

/-- Exact predicate `subject: Trait<arguments...>` in retained source order. -/
inductive PredicateParses :
    Remainder → Syntax.Predicate → Remainder → Prop where
  | parsed {input afterSubject afterColon afterName output : Remainder}
      {subject : Syntax.TypeExpr} {traitName : Identifier}
      {arguments : Option (NonemptyDelimitedList Syntax.TypeExpr)}
      (colonSpan : SourceSpan)
      (subjectParsed : TypeExprParses input subject afterSubject)
      (colonToken : ExactTokenParses (.symbol .colon)
        afterSubject colonSpan afterColon)
      (nameParsed : IdentifierParses afterColon traitName afterName)
      (argumentsParsed : OptionalNamedTypeArgumentsParses
        afterName arguments output) :
      PredicateParses input {
        span := SourceSpan.cover subject.span
          (match arguments with
          | some values => values.span
          | none => traitName.span)
        subject
        traitName
        arguments
      } output

/-! Grammar of bare, grouped, and optional `where` predicate sequences. -/

/-- Token kinds accepted by the canonical type-expression start lookahead. -/
inductive TypeExprStartToken : TokenKind → Prop where
  | function : TypeExprStartToken (.keyword .functionKw)
  | proxy : TypeExprStartToken (.symbol .at)
  | tuple : TypeExprStartToken (.symbol .leftParen)
  | identifier (name : String) : TypeExprStartToken (.identifier name)

/-- A canonical type expression can start at this remainder. -/
def TypeExprStartsAt (input : Remainder) : Prop :=
  ∃ span kind,
    TokenAt input.tokens input.endIndex input.cursor { span, value := kind } ∧
      TypeExprStartToken kind

/-- No token accepted by the type-expression start lookahead occurs here. -/
def TypeExprAbsentAt (input : Remainder) : Prop :=
  ¬ TypeExprStartsAt input

/--
Forward-order grammar of the commas and predicates following the first bare
predicate. The final span is the last predicate, or a retained trailing comma.
-/
inductive BarePredicateTailParses :
    SourceSpan → Remainder → List Syntax.Predicate → SourceSpan →
      Remainder → Prop where
  | done {input : Remainder} {lastSpan : SourceSpan}
      (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .comma)) :
      BarePredicateTailParses lastSpan input [] lastSpan input
  | trailing {input afterComma : Remainder}
      {lastSpan commaSpan : SourceSpan}
      (commaToken : ExactTokenParses (.symbol .comma)
        input commaSpan afterComma)
      (nextAbsent : TypeExprAbsentAt afterComma) :
      BarePredicateTailParses lastSpan input [] commaSpan afterComma
  | next {input afterComma afterPredicate output : Remainder}
      {lastSpan commaSpan finalSpan : SourceSpan}
      {predicate : Syntax.Predicate} {predicates : List Syntax.Predicate}
      (commaToken : ExactTokenParses (.symbol .comma)
        input commaSpan afterComma)
      (nextStarts : TypeExprStartsAt afterComma)
      (predicateParsed : PredicateParses afterComma predicate afterPredicate)
      (tail : BarePredicateTailParses predicate.span afterPredicate
        predicates finalSpan output) :
      BarePredicateTailParses lastSpan input (predicate :: predicates)
        finalSpan output

/-- Exact grammar of a nonempty unparenthesized predicate sequence. -/
inductive BarePredicateSequenceParses :
    Remainder → NonemptyDelimitedList Syntax.Predicate → Remainder → Prop where
  | parsed {input afterFirst output : Remainder}
      {first : Syntax.Predicate} {rest : List Syntax.Predicate}
      {finalSpan : SourceSpan}
      (firstParsed : PredicateParses input first afterFirst)
      (tailParsed : BarePredicateTailParses first.span afterFirst rest
        finalSpan output) :
      BarePredicateSequenceParses input {
        span := SourceSpan.cover first.span finalSpan
        elements := { head := first, tail := rest }
      } output

/-- Exact generic-delimiter grammar of a parenthesized predicate sequence. -/
def GroupedPredicateSequenceParses
    (input : Remainder) (values : NonemptyDelimitedList Syntax.Predicate)
    (output : Remainder) : Prop :=
  NonemptyTrailingDelimitedListParses .leftParen .rightParen PredicateParses
    input { span := values.span, elements := values.elements.toList } output

/-- The preferred grouped predicate grammar has no derivation from here. -/
def GroupedPredicateSequenceUnavailable (input : Remainder) : Prop :=
  ¬ ∃ values output, GroupedPredicateSequenceParses input values output

/-- Prioritized successful branch of the transactional predicate choice. -/
inductive PredicateSequenceParses :
    Remainder → NonemptyDelimitedList Syntax.Predicate → Remainder → Prop where
  | bare {input output : Remainder}
      {values : NonemptyDelimitedList Syntax.Predicate}
      (groupedUnavailable : GroupedPredicateSequenceUnavailable input)
      (parsed : BarePredicateSequenceParses input values output) :
      PredicateSequenceParses input values output
  | grouped {input output : Remainder}
      {values : NonemptyDelimitedList Syntax.Predicate}
      (parsed : GroupedPredicateSequenceParses input values output) :
      PredicateSequenceParses input values output

/-- Prioritized optional `where` marker and its nonempty predicate sequence. -/
inductive OptionalWhereClauseParses :
    Remainder → Option Syntax.WhereClause → Remainder → Prop where
  | absent {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.where.spelling)) :
      OptionalWhereClauseParses input none input
  | present {input afterMarker output : Remainder}
      {predicates : NonemptyDelimitedList Syntax.Predicate}
      (markerSpan : SourceSpan)
      (markerToken : ExactTokenParses
        (.identifier ContextualKeyword.where.spelling)
        input markerSpan afterMarker)
      (predicatesParsed : PredicateSequenceParses
        afterMarker predicates output) :
      OptionalWhereClauseParses input (some {
        span := SourceSpan.cover markerSpan predicates.span
        predicates := predicates.elements
      }) output

/-! Grammar shared by named function and trait-method signatures. -/

/-- Prioritized optional `returns (...)` clause with exact recursive types. -/
inductive OptionalReturnClauseParses :
    Remainder → Option Syntax.ReturnClause → Remainder → Prop where
  | absent {input : Remainder}
      (returnsAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.identifier ContextualKeyword.returns.spelling)) :
      OptionalReturnClauseParses input none input
  | present {input afterMarker output : Remainder}
      {types : DelimitedList Syntax.TypeExpr} (markerSpan : SourceSpan)
      (markerToken : ExactTokenParses
        (.identifier ContextualKeyword.returns.spelling)
        input markerSpan afterMarker)
      (typesParsed : TrailingDelimitedListParses
        .leftParen .rightParen TypeExprParses afterMarker types output) :
      OptionalReturnClauseParses input (some {
        span := SourceSpan.cover markerSpan types.span
        types
      }) output

/-- Prioritized optional occurrence of one fixed function modifier. -/
inductive OptionalFunctionModifierParses (keyword : HardKeyword) :
    Remainder → Option SourceSpan → Remainder → Prop where
  | absent {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword keyword)) :
      OptionalFunctionModifierParses keyword input none input
  | present {input output : Remainder} (markerSpan : SourceSpan)
      (markerToken : ExactTokenParses (.keyword keyword)
        input markerSpan output) :
      OptionalFunctionModifierParses keyword input (some markerSpan) output

/-- Exact fixed-order parsing of optional `public` then `payable` markers. -/
def FunctionModifiersParses
    (input : Remainder) (modifiers : Syntax.FunctionModifiers)
    (output : Remainder) : Prop :=
  ∃ afterPublic,
    OptionalFunctionModifierParses .publicKw input modifiers.publicMarker
      afterPublic ∧
    OptionalFunctionModifierParses .payableKw afterPublic
      modifiers.payableMarker output

/-- Module-level functions allow no contract-only modifiers. -/
def ModuleFunctionModifiersAllowed
    (modifiers : Syntax.FunctionModifiers) : Prop :=
  modifiers.publicMarker = none ∧ modifiers.payableMarker = none

/-- Contract functions allow every syntactically ordered modifier pair. -/
def ContractFunctionModifiersAllowed
    (_ : Syntax.FunctionModifiers) : Prop := True

/-- Parser-independent endpoint retained by one complete function signature. -/
def functionSignatureEnd (parameters : DelimitedList Syntax.FunctionParameter)
    (modifiers : Syntax.FunctionModifiers)
    (returnsClause : Option Syntax.ReturnClause)
    (whereClause : Option Syntax.WhereClause) : SourceSpan :=
  match whereClause with
  | some clause => clause.span
  | none => match returnsClause with
    | some clause => clause.span
    | none => match modifiers.payableMarker with
      | some span => span
      | none => match modifiers.publicMarker with
        | some span => span
        | none => parameters.span

/-! Grammar of canonical transparent type-alias declarations. -/

/-- Prioritized optional, possibly empty type-alias parameters. -/
inductive OptionalTypeAliasParametersParses :
    Remainder → Option (DelimitedList Identifier) → Remainder → Prop where
  | absent {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen)) :
      OptionalTypeAliasParametersParses input none input
  | present {input output : Remainder}
      {parameters : DelimitedList Identifier}
      (parsed : TrailingDelimitedListParses .leftParen .rightParen
        IdentifierParses input parameters output) :
      OptionalTypeAliasParametersParses input (some parameters) output

/-- Exact non-recovery grammar of one complete transparent type alias. -/
inductive TypeAliasDeclParses :
    Remainder → Syntax.TypeAliasDecl → Remainder → Prop where
  | parsed
      {input afterKeyword afterName afterParameters afterEqual afterValue
        output : Remainder}
      {name : Identifier}
      {parameters : Option (DelimitedList Identifier)}
      {value : Syntax.TypeExpr}
      (keywordSpan equalSpan semicolonSpan : SourceSpan)
      (keywordToken : ExactTokenParses (.keyword .typeKw)
        input keywordSpan afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (parametersParsed : OptionalTypeAliasParametersParses
        afterName parameters afterParameters)
      (equalToken : ExactTokenParses (.symbol .equal)
        afterParameters equalSpan afterEqual)
      (valueParsed : TypeExprParses afterEqual value afterValue)
      (semicolonToken : ExactTokenParses (.symbol .semicolon)
        afterValue semicolonSpan output) :
      TypeAliasDeclParses input {
        span := SourceSpan.cover keywordSpan semicolonSpan
        value := {
          name
          parameters
          value
        }
      } output

/-! Grammar shared by canonical declarations with generic parameters. -/

/-- Exact nonempty, trailing-comma generic parameter list. -/
def GenericParametersParses
    (input : Remainder) (parameters : Syntax.GenericParameters)
    (output : Remainder) : Prop :=
  NonemptyTrailingDelimitedListParses .less .greater IdentifierParses input {
    span := parameters.span
    elements := parameters.elements.toList
  } output

/-- Prioritized optional generic parameters selected by a leading `<`. -/
inductive OptionalGenericParametersParses :
    Remainder → Option Syntax.GenericParameters → Remainder → Prop where
  | absent {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .less)) :
      OptionalGenericParametersParses input none input
  | present {input output : Remainder}
      {parameters : Syntax.GenericParameters}
      (parsed : GenericParametersParses input parameters output) :
      OptionalGenericParametersParses input (some parameters) output

/--
Exact complete named-function signature under a parser-independent modifier
policy. The grammar retains every component in source order and excludes the
function body or trait-method semicolon.
-/
inductive FunctionSignatureParses
    (modifiersAllowed : Syntax.FunctionModifiers → Prop) :
    Remainder → Syntax.FunctionSignature → Remainder → Prop where
  | parsed
      {input afterKeyword afterName afterGenerics afterParameters
        afterModifiers afterReturns output : Remainder}
      {name : Identifier}
      {genericParameters : Option Syntax.GenericParameters}
      {parameters : DelimitedList Syntax.FunctionParameter}
      {modifiers : Syntax.FunctionModifiers}
      {returnsClause : Option Syntax.ReturnClause}
      {whereClause : Option Syntax.WhereClause}
      (keywordSpan : SourceSpan)
      (keywordToken : ExactTokenParses (.keyword .functionKw)
        input keywordSpan afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (genericsParsed : OptionalGenericParametersParses
        afterName genericParameters afterGenerics)
      (parametersParsed : FunctionParametersParses
        afterGenerics parameters afterParameters)
      (modifiersParsed : FunctionModifiersParses
        afterParameters modifiers afterModifiers)
      (returnsParsed : OptionalReturnClauseParses
        afterModifiers returnsClause afterReturns)
      (whereParsed : OptionalWhereClauseParses
        afterReturns whereClause output)
      (policy : modifiersAllowed modifiers) :
      FunctionSignatureParses modifiersAllowed input {
        span := SourceSpan.cover keywordSpan
          (functionSignatureEnd parameters modifiers returnsClause whereClause)
        name
        genericParameters
        parameters
        modifiers
        returnsClause
        whereClause
      } output

/-! Grammar of ordinary function declarations over an abstract block grammar. -/

/--
Exact signature-to-body grammar of an ordinary function declaration.

The body relation is deliberately abstract so this declaration grammar can be
composed with a parser-independent block grammar without referring to the
executable statement parser or its fuel.  The modifier policy is shared with
`FunctionSignatureParses` and therefore remains exact for the declaration's
syntactic location.
-/
inductive FunctionDeclParses
    (bodyParses : Remainder → Syntax.Block → Remainder → Prop)
    (modifiersAllowed : Syntax.FunctionModifiers → Prop) :
    Remainder → Syntax.FunctionDecl → Remainder → Prop where
  | parsed {input afterSignature output : Remainder}
      {signature : Syntax.FunctionSignature} {body : Syntax.Block}
      (signatureParsed : FunctionSignatureParses modifiersAllowed
        input signature afterSignature)
      (bodyParsed : bodyParses afterSignature body output) :
      FunctionDeclParses bodyParses modifiersAllowed input {
        span := SourceSpan.cover signature.span body.span
        value := { signature, body }
      } output

/-! Grammar of canonical implementation declarations over an abstract block grammar. -/

/-- Prioritized optional leading `default` marker of an implementation. -/
inductive OptionalImplDefaultMarkerParses :
    Remainder → Option SourceSpan → Remainder → Prop where
  | absent {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .defaultKw)) :
      OptionalImplDefaultMarkerParses input none input
  | present {input output : Remainder} (markerSpan : SourceSpan)
      (markerToken : ExactTokenParses (.keyword .defaultKw)
        input markerSpan output) :
      OptionalImplDefaultMarkerParses input (some markerSpan) output

/-- Exact nonempty implementation head arguments between angle brackets. -/
def ImplHeadArgumentsParses
    (input : Remainder) (arguments : NonemptyDelimitedList Syntax.TypeExpr)
    (output : Remainder) : Prop :=
  NonemptyTrailingDelimitedListParses .less .greater TypeExprParses input {
    span := arguments.span
    elements := arguments.elements.toList
  } output

/-- One implementation method is a module-policy function with empty trivia. -/
inductive ImplMethodParses
    (bodyParses : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.ImplMethod → Remainder → Prop where
  | parsed {input output : Remainder}
      {declaration : Syntax.FunctionDecl}
      (declarationParsed : FunctionDeclParses bodyParses
        ModuleFunctionModifiersAllowed input declaration output) :
      ImplMethodParses bodyParses input {
        span := declaration.span
        value := {
          leadingComments := []
          declaration
        }
      } output

/--
Forward-order implementation methods ending at the exact closing brace.

The closing branch has priority.  Every method branch records the executable
loop's strict cursor-progress guard independently of its fuel bound.
-/
inductive ImplMethodTailParses
    (bodyParses : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → List Syntax.ImplMethod → SourceSpan →
      Remainder → Prop where
  | close {input output : Remainder} (closingSpan : SourceSpan)
      (closingToken : ExactTokenParses (.symbol .rightBrace)
        input closingSpan output) :
      ImplMethodTailParses bodyParses input [] closingSpan output
  | next {input afterMethod output : Remainder}
      {method : Syntax.ImplMethod} {methods : List Syntax.ImplMethod}
      {closingSpan : SourceSpan}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (methodParsed : ImplMethodParses bodyParses input method afterMethod)
      (progress : input.cursor < afterMethod.cursor)
      (tail : ImplMethodTailParses bodyParses afterMethod methods
        closingSpan output) :
      ImplMethodTailParses bodyParses input (method :: methods)
        closingSpan output

/-- Exact braces, retained span, and source-order implementation methods. -/
inductive ImplBodyParses
    (bodyParses : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → SourceSpan → List Syntax.ImplMethod →
      Remainder → Prop where
  | parsed {input afterOpening output : Remainder}
      {methods : List Syntax.ImplMethod} (openingSpan closingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBrace)
        input openingSpan afterOpening)
      (methodsParsed : ImplMethodTailParses bodyParses afterOpening methods
        closingSpan output) :
      ImplBodyParses bodyParses input
        (SourceSpan.cover openingSpan closingSpan) methods output

/--
Exact canonical implementation declaration.  Function bodies remain abstract,
while the optional marker, head arguments, where clause, body, and outer range
are fixed independently of the executable parser.
-/
inductive ImplDeclParses
    (bodyParses : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.ImplDecl → Remainder → Prop where
  | parsed
      {input afterDefault afterMarker afterGenerics afterName afterArguments
        afterWhere output : Remainder}
      {defaultMarker : Option SourceSpan}
      {genericParameters : Option Syntax.GenericParameters}
      {traitName : Identifier}
      {headArguments : NonemptyDelimitedList Syntax.TypeExpr}
      {whereClause : Option Syntax.WhereClause}
      {bodySpan : SourceSpan} {methods : List Syntax.ImplMethod}
      (markerSpan : SourceSpan)
      (defaultParsed : OptionalImplDefaultMarkerParses input defaultMarker
        afterDefault)
      (markerToken : ExactTokenParses
        (.identifier ContextualKeyword.impl.spelling)
        afterDefault markerSpan afterMarker)
      (genericsParsed : OptionalGenericParametersParses
        afterMarker genericParameters afterGenerics)
      (nameParsed : IdentifierParses afterGenerics traitName afterName)
      (argumentsParsed : ImplHeadArgumentsParses
        afterName headArguments afterArguments)
      (whereParsed : OptionalWhereClauseParses
        afterArguments whereClause afterWhere)
      (bodyParsed : ImplBodyParses bodyParses afterWhere bodySpan methods
        output) :
      ImplDeclParses bodyParses input {
        span := SourceSpan.cover (defaultMarker.getD markerSpan) bodySpan
        value := {
          defaultMarker
          genericParameters
          traitName
          headArguments
          whereClause
          bodySpan
          methods
        }
      } output

/-! Grammar of strict contract entries and fields over abstract body/expression grammars. -/

/--
Exact modifiers retained by constructors and fallback entries.  An explicit
`public` marker is rejected by the strict diagnostic-free grammar because the
executable parser diagnoses and discards it; `payable` remains optional.
-/
def ContractEntryModifiersParses
    (input : Remainder) (payableMarker : Option SourceSpan)
    (output : Remainder) : Prop :=
  TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .publicKw) ∧
    OptionalFunctionModifierParses .payableKw input payableMarker output

/-- Exact constructor entry with an abstract required-tail block grammar. -/
inductive ConstructorDeclParses
    (bodyParses : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.ConstructorDecl → Remainder → Prop where
  | parsed
      {input afterMarker afterParameters afterModifiers output : Remainder}
      {parameters : DelimitedList Syntax.FunctionParameter}
      {payableMarker : Option SourceSpan} {body : Syntax.Block}
      (markerSpan : SourceSpan)
      (markerToken : ExactTokenParses (.keyword .constructorKw)
        input markerSpan afterMarker)
      (parametersParsed : FunctionParametersParses
        afterMarker parameters afterParameters)
      (modifiersParsed : ContractEntryModifiersParses
        afterParameters payableMarker afterModifiers)
      (bodyParsed : bodyParses afterModifiers body output) :
      ConstructorDeclParses bodyParses input {
        span := SourceSpan.cover markerSpan body.span
        value := { parameters, payableMarker, body }
      } output

/--
Exact fallback entry.  The empty-parameter premise excludes the executable
diagnostic path that retains an invalid nonempty list in the AST.
-/
inductive FallbackDeclParses
    (bodyParses : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.FallbackDecl → Remainder → Prop where
  | parsed
      {input afterMarker afterParameters afterModifiers output : Remainder}
      {parameters : DelimitedList Syntax.FunctionParameter}
      {payableMarker : Option SourceSpan} {body : Syntax.Block}
      (markerSpan : SourceSpan)
      (markerToken : ExactTokenParses (.keyword .fallbackKw)
        input markerSpan afterMarker)
      (parametersParsed : FunctionParametersParses
        afterMarker parameters afterParameters)
      (parameterless : parameters.elements = [])
      (modifiersParsed : ContractEntryModifiersParses
        afterParameters payableMarker afterModifiers)
      (bodyParsed : bodyParses afterModifiers body output) :
      FallbackDeclParses bodyParses input {
        span := SourceSpan.cover markerSpan body.span
        value := { parameters, payableMarker, body }
      } output

/-- Prioritized optional initializer of a contract storage field. -/
inductive OptionalContractFieldInitializerParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Option Syntax.Expr → Remainder → Prop where
  | absent {input : Remainder}
      (equalAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .equal)) :
      OptionalContractFieldInitializerParses expressionParses input none input
  | present {input afterEqual output : Remainder} {value : Syntax.Expr}
      (equalSpan : SourceSpan)
      (equalToken : ExactTokenParses (.symbol .equal)
        input equalSpan afterEqual)
      (valueParsed : expressionParses afterEqual value output) :
      OptionalContractFieldInitializerParses expressionParses input
        (some value) output

/-- Exact storage-field grammar with an abstract initializer expression. -/
inductive ContractFieldParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.ContractField → Remainder → Prop where
  | parsed
      {input afterName afterColon afterType afterInitializer output : Remainder}
      {name : Identifier} {type : Syntax.TypeExpr}
      {initializer : Option Syntax.Expr}
      (colonSpan semicolonSpan : SourceSpan)
      (nameParsed : IdentifierParses input name afterName)
      (colonToken : ExactTokenParses (.symbol .colon)
        afterName colonSpan afterColon)
      (typeParsed : TypeExprParses afterColon type afterType)
      (initializerParsed : OptionalContractFieldInitializerParses
        expressionParses afterType initializer afterInitializer)
      (semicolonToken : ExactTokenParses (.symbol .semicolon)
        afterInitializer semicolonSpan output) :
      ContractFieldParses expressionParses input {
        span := SourceSpan.cover name.span semicolonSpan
        value := { name, type, initializer }
      } output

/-! Grammar of canonical signature-only trait declarations. -/

/-- Exact module-policy signature followed by a trait-method semicolon. -/
inductive TraitMethodParses :
    Remainder → Syntax.TraitMethod → Remainder → Prop where
  | parsed {input afterSignature output : Remainder}
      {signature : Syntax.FunctionSignature} (semicolonSpan : SourceSpan)
      (signatureParsed : FunctionSignatureParses
        ModuleFunctionModifiersAllowed input signature afterSignature)
      (semicolonToken : ExactTokenParses (.symbol .semicolon)
        afterSignature semicolonSpan output) :
      TraitMethodParses input {
        span := SourceSpan.cover signature.span semicolonSpan
        value := {
          leadingComments := []
          signature
          semicolon := semicolonSpan
        }
      } output

/-- Forward-order methods ending at the exact closing trait brace. -/
inductive TraitMethodTailParses :
    Remainder → List Syntax.TraitMethod → SourceSpan →
      Remainder → Prop where
  | close {input output : Remainder} (closingSpan : SourceSpan)
      (closingToken : ExactTokenParses (.symbol .rightBrace)
        input closingSpan output) :
      TraitMethodTailParses input [] closingSpan output
  | next {input afterMethod output : Remainder}
      {method : Syntax.TraitMethod} {methods : List Syntax.TraitMethod}
      {closingSpan : SourceSpan}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (methodParsed : TraitMethodParses input method afterMethod)
      (tail : TraitMethodTailParses afterMethod methods closingSpan output) :
      TraitMethodTailParses input (method :: methods) closingSpan output

/-- Exact braces, retained body span, and source-order trait methods. -/
inductive TraitBodyParses :
    Remainder → SourceSpan → List Syntax.TraitMethod →
      Remainder → Prop where
  | parsed {input afterOpening output : Remainder}
      {methods : List Syntax.TraitMethod} (openingSpan closingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBrace)
        input openingSpan afterOpening)
      (methodsParsed : TraitMethodTailParses
        afterOpening methods closingSpan output) :
      TraitBodyParses input (SourceSpan.cover openingSpan closingSpan)
        methods output

/-- Exact canonical trait declaration with required generic parameters. -/
inductive TraitDeclParses :
    Remainder → Syntax.TraitDecl → Remainder → Prop where
  | parsed
      {input afterMarker afterName afterGenerics afterWhere output : Remainder}
      {name : Identifier} {genericParameters : Syntax.GenericParameters}
      {whereClause : Option Syntax.WhereClause} {bodySpan : SourceSpan}
      {methods : List Syntax.TraitMethod} (markerSpan : SourceSpan)
      (markerToken : ExactTokenParses
        (.identifier ContextualKeyword.trait.spelling)
        input markerSpan afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (genericsParsed : GenericParametersParses
        afterName genericParameters afterGenerics)
      (whereParsed : OptionalWhereClauseParses
        afterGenerics whereClause afterWhere)
      (bodyParsed : TraitBodyParses afterWhere bodySpan methods output) :
      TraitDeclParses input {
        span := SourceSpan.cover markerSpan bodySpan
        value := {
          name
          genericParameters
          whereClause
          bodySpan
          methods
        }
      } output

/-! Grammar of canonical algebraic enum declarations. -/

/-- Prioritized optional constructor payload with no trailing comma. -/
inductive OptionalEnumConstructorFieldsParses :
    Remainder → Option (DelimitedList Syntax.TypeExpr) → Remainder →
      Prop where
  | absent {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen)) :
      OptionalEnumConstructorFieldsParses input none input
  | present {input output : Remainder}
      {fields : DelimitedList Syntax.TypeExpr}
      (parsed : NoTrailingDelimitedListParses .leftParen .rightParen
        TypeExprParses input fields output) :
      OptionalEnumConstructorFieldsParses input (some fields) output

/-- Exact enum constructor name, optional payload, span, and empty trivia. -/
inductive EnumConstructorParses :
    Remainder → Syntax.EnumConstructor → Remainder → Prop where
  | parsed {input afterName output : Remainder}
      {name : Identifier}
      {fields : Option (DelimitedList Syntax.TypeExpr)}
      (nameParsed : IdentifierParses input name afterName)
      (fieldsParsed : OptionalEnumConstructorFieldsParses
        afterName fields output) :
      EnumConstructorParses input {
        span := SourceSpan.cover name.span
          (fields.map (fun values => values.span) |>.getD name.span)
        value := {
          leadingComments := []
          name
          fields
        }
      } output

/-- Possibly empty, trailing-comma enum body between braces. -/
def EnumBodyParses
    (input : Remainder) (bodySpan : SourceSpan)
    (constructors : List Syntax.EnumConstructor) (output : Remainder) : Prop :=
  TrailingDelimitedListParses .leftBrace .rightBrace EnumConstructorParses
    input { span := bodySpan, elements := constructors } output

/--
Exact enum declaration after an already supplied optional derive attribute.
The active remainder begins at the contextual `enum` marker; a supplied derive
attribute contributes only the retained outer start and AST field.
-/
inductive EnumDeclParses (deriveAttribute : Option Syntax.DeriveAttribute) :
    Remainder → Syntax.EnumDecl → Remainder → Prop where
  | parsed {input afterMarker afterName afterParameters output : Remainder}
      {name : Identifier}
      {parameters : Option Syntax.GenericParameters}
      {bodySpan : SourceSpan}
      {constructors : List Syntax.EnumConstructor}
      (markerSpan : SourceSpan)
      (markerToken : ExactTokenParses
        (.identifier ContextualKeyword.enum.spelling)
        input markerSpan afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (parametersParsed : OptionalGenericParametersParses
        afterName parameters afterParameters)
      (bodyParsed : EnumBodyParses afterParameters bodySpan constructors
        output) :
      EnumDeclParses deriveAttribute input {
        span := SourceSpan.cover
          (deriveAttribute.map (fun derive => derive.span) |>.getD markerSpan)
          bodySpan
        value := {
          deriveAttribute
          name
          parameters
          bodySpan
          constructors
        }
      } output

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

/-! Grammar of strict contract members, bodies, and complete declarations. -/

/-- Composite lookahead selecting a storage field before every other member. -/
def ContractFieldStartsAt (input : Remainder) : Prop :=
  ∃ spelling nameSpan colonSpan,
    TokenAt input.tokens input.endIndex input.cursor {
      span := nameSpan
      value := .identifier spelling
    } ∧
    TokenAt input.tokens input.endIndex (input.cursor + 1) {
      span := colonSpan
      value := .symbol .colon
    }

/--
Exact attribute-free member dispatch in executable priority order.  Negative
premises retain every earlier selector, including the field composite
lookahead that takes priority over a contextual `enum` spelling followed by
`:`.
-/
inductive ContractMemberCoreParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.ContractMember → Remainder → Prop where
  | field {input output : Remainder} {declaration : Syntax.ContractField}
      (startsField : ContractFieldStartsAt input)
      (parsed : ContractFieldParses expressionParses input declaration output) :
      ContractMemberCoreParses expressionParses allowBodyParses
        requiredBodyParses input {
          span := declaration.span
          leadingComments := []
          value := .field declaration
        } output
  | function {input output : Remainder} {declaration : Syntax.FunctionDecl}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (parsed : FunctionDeclParses allowBodyParses
        ContractFunctionModifiersAllowed input declaration output) :
      ContractMemberCoreParses expressionParses allowBodyParses
        requiredBodyParses input {
          span := declaration.span
          leadingComments := []
          value := .function declaration
        } output
  | constructor {input output : Remainder}
      {declaration : Syntax.ConstructorDecl}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (parsed : ConstructorDeclParses requiredBodyParses
        input declaration output) :
      ContractMemberCoreParses expressionParses allowBodyParses
        requiredBodyParses input {
          span := declaration.span
          leadingComments := []
          value := .constructor declaration
        } output
  | fallback {input output : Remainder}
      {declaration : Syntax.FallbackDecl}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (constructorAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .constructorKw))
      (parsed : FallbackDeclParses requiredBodyParses
        input declaration output) :
      ContractMemberCoreParses expressionParses allowBodyParses
        requiredBodyParses input {
          span := declaration.span
          leadingComments := []
          value := .fallback declaration
        } output
  | typeAlias {input output : Remainder}
      {declaration : Syntax.TypeAliasDecl}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (constructorAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .constructorKw))
      (fallbackAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .fallbackKw))
      (parsed : TypeAliasDeclParses input declaration output) :
      ContractMemberCoreParses expressionParses allowBodyParses
        requiredBodyParses input {
          span := declaration.span
          leadingComments := []
          value := .typeAlias declaration
        } output
  | enum {input output : Remainder} {declaration : Syntax.EnumDecl}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (constructorAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .constructorKw))
      (fallbackAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .fallbackKw))
      (typeAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .typeKw))
      (parsed : EnumDeclParses none input declaration output) :
      ContractMemberCoreParses expressionParses allowBodyParses
        requiredBodyParses input {
          span := declaration.span
          leadingComments := []
          value := .enum declaration
        } output

/--
Strict attribute-aware member dispatch.  A leading hash commits to derive
parsing; diagnostic freedom permits attachment only to the enum branch.
-/
inductive ContractMemberParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.ContractMember → Remainder → Prop where
  | plain {input output : Remainder} {member : Syntax.ContractMember}
      (hashAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .hash))
      (parsed : ContractMemberCoreParses expressionParses allowBodyParses
        requiredBodyParses input member output) :
      ContractMemberParses expressionParses allowBodyParses
        requiredBodyParses input member output
  | derivedEnum
      {input afterDerive output : Remainder}
      {derive : Syntax.DeriveAttribute} {declaration : Syntax.EnumDecl}
      (deriveParsed : DeriveAttributeParses input derive afterDerive)
      (fieldAbsent : ¬ ContractFieldStartsAt afterDerive)
      (functionAbsent : TokenKindAbsentAt afterDerive.tokens
        afterDerive.endIndex afterDerive.cursor (.keyword .functionKw))
      (constructorAbsent : TokenKindAbsentAt afterDerive.tokens
        afterDerive.endIndex afterDerive.cursor (.keyword .constructorKw))
      (fallbackAbsent : TokenKindAbsentAt afterDerive.tokens
        afterDerive.endIndex afterDerive.cursor (.keyword .fallbackKw))
      (typeAbsent : TokenKindAbsentAt afterDerive.tokens afterDerive.endIndex
        afterDerive.cursor (.keyword .typeKw))
      (enumParsed : EnumDeclParses (some derive)
        afterDerive declaration output) :
      ContractMemberParses expressionParses allowBodyParses
        requiredBodyParses input {
          span := declaration.span
          leadingComments := []
          value := .enum declaration
        } output

/-- Forward-order contract members ending at the exact closing brace. -/
inductive ContractMemberTailParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → List Syntax.ContractMember → SourceSpan →
      Remainder → Prop where
  | close {input output : Remainder} (closingSpan : SourceSpan)
      (closingToken : ExactTokenParses (.symbol .rightBrace)
        input closingSpan output) :
      ContractMemberTailParses expressionParses allowBodyParses
        requiredBodyParses input [] closingSpan output
  | next {input afterMember output : Remainder}
      {member : Syntax.ContractMember} {members : List Syntax.ContractMember}
      {closingSpan : SourceSpan}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (memberParsed : ContractMemberParses expressionParses allowBodyParses
        requiredBodyParses input member afterMember)
      (progress : input.cursor < afterMember.cursor)
      (tail : ContractMemberTailParses expressionParses allowBodyParses
        requiredBodyParses afterMember members closingSpan output) :
      ContractMemberTailParses expressionParses allowBodyParses
        requiredBodyParses input (member :: members) closingSpan output

/-- Exact braces, body span, and source-order strict contract members. -/
inductive ContractBodyParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → SourceSpan → List Syntax.ContractMember →
      Remainder → Prop where
  | parsed {input afterOpening output : Remainder}
      {members : List Syntax.ContractMember} (openingSpan closingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBrace)
        input openingSpan afterOpening)
      (membersParsed : ContractMemberTailParses expressionParses
        allowBodyParses requiredBodyParses afterOpening members closingSpan
        output) :
      ContractBodyParses expressionParses allowBodyParses requiredBodyParses
        input (SourceSpan.cover openingSpan closingSpan) members output

/-- Exact canonical contract declaration over abstract member leaves. -/
inductive ContractDeclParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.ContractDecl → Remainder → Prop where
  | parsed
      {input afterMarker afterName afterGenerics output : Remainder}
      {name : Identifier}
      {genericParameters : Option Syntax.GenericParameters}
      {bodySpan : SourceSpan} {members : List Syntax.ContractMember}
      (markerSpan : SourceSpan)
      (markerToken : ExactTokenParses (.keyword .contractKw)
        input markerSpan afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (genericsParsed : OptionalGenericParametersParses
        afterName genericParameters afterGenerics)
      (bodyParsed : ContractBodyParses expressionParses allowBodyParses
        requiredBodyParses afterGenerics bodySpan members output) :
      ContractDeclParses expressionParses allowBodyParses requiredBodyParses
        input {
          span := SourceSpan.cover markerSpan bodySpan
          value := { name, genericParameters, bodySpan, members }
        } output

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

/-! Parametric strict grammar of complete top-level declarations. -/

/-- Every listed selector token is absent at the current top-item cursor. -/
def TopItemKindsAbsentAt (input : Remainder)
    (kinds : List TokenKind) : Prop :=
  ∀ kind ∈ kinds,
    TokenKindAbsentAt input.tokens input.endIndex input.cursor kind

/--
Exact attribute-free top-level dispatch in executable priority order.  Core
function, implementation, and contract bodies remain abstract relations.
-/
inductive PlainTopItemParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.TopItem → Remainder → Prop where
  | importDecl {input output : Remainder} {declaration : Syntax.ImportDecl}
      (parsed : ImportDeclParses input declaration output) :
      PlainTopItemParses expressionParses allowBodyParses requiredBodyParses
        input {
          span := declaration.span
          leadingComments := []
          value := .importDecl declaration
        } output
  | exportDecl {input output : Remainder} {declaration : Syntax.ExportDecl}
      (earlierAbsent : TopItemKindsAbsentAt input [
        .keyword .importKw])
      (parsed : ExportDeclParses input declaration output) :
      PlainTopItemParses expressionParses allowBodyParses requiredBodyParses
        input {
          span := declaration.span
          leadingComments := []
          value := .exportDecl declaration
        } output
  | pragmaDecl {input output : Remainder} {declaration : Syntax.PragmaDecl}
      (earlierAbsent : TopItemKindsAbsentAt input [
        .keyword .importKw, .keyword .exportKw])
      (parsed : PragmaDeclParses input declaration output) :
      PlainTopItemParses expressionParses allowBodyParses requiredBodyParses
        input {
          span := declaration.span
          leadingComments := []
          value := .pragmaDecl declaration
        } output
  | typeAlias {input output : Remainder}
      {declaration : Syntax.TypeAliasDecl}
      (earlierAbsent : TopItemKindsAbsentAt input [
        .keyword .importKw, .keyword .exportKw, .keyword .pragmaKw])
      (parsed : TypeAliasDeclParses input declaration output) :
      PlainTopItemParses expressionParses allowBodyParses requiredBodyParses
        input {
          span := declaration.span
          leadingComments := []
          value := .typeAlias declaration
        } output
  | function {input output : Remainder} {declaration : Syntax.FunctionDecl}
      (earlierAbsent : TopItemKindsAbsentAt input [
        .keyword .importKw, .keyword .exportKw, .keyword .pragmaKw,
        .keyword .typeKw])
      (parsed : FunctionDeclParses allowBodyParses
        ModuleFunctionModifiersAllowed input declaration output) :
      PlainTopItemParses expressionParses allowBodyParses requiredBodyParses
        input {
          span := declaration.span
          leadingComments := []
          value := .function declaration
        } output
  | enum {input output : Remainder} {declaration : Syntax.EnumDecl}
      (earlierAbsent : TopItemKindsAbsentAt input [
        .keyword .importKw, .keyword .exportKw, .keyword .pragmaKw,
        .keyword .typeKw, .keyword .functionKw])
      (parsed : EnumDeclParses none input declaration output) :
      PlainTopItemParses expressionParses allowBodyParses requiredBodyParses
        input {
          span := declaration.span
          leadingComments := []
          value := .enum declaration
        } output
  | trait {input output : Remainder} {declaration : Syntax.TraitDecl}
      (earlierAbsent : TopItemKindsAbsentAt input [
        .keyword .importKw, .keyword .exportKw, .keyword .pragmaKw,
        .keyword .typeKw, .keyword .functionKw,
        .identifier ContextualKeyword.enum.spelling])
      (parsed : TraitDeclParses input declaration output) :
      PlainTopItemParses expressionParses allowBodyParses requiredBodyParses
        input {
          span := declaration.span
          leadingComments := []
          value := .trait declaration
        } output
  | impl {input output : Remainder} {declaration : Syntax.ImplDecl}
      (earlierAbsent : TopItemKindsAbsentAt input [
        .keyword .importKw, .keyword .exportKw, .keyword .pragmaKw,
        .keyword .typeKw, .keyword .functionKw,
        .identifier ContextualKeyword.enum.spelling,
        .identifier ContextualKeyword.trait.spelling])
      (parsed : ImplDeclParses allowBodyParses input declaration output) :
      PlainTopItemParses expressionParses allowBodyParses requiredBodyParses
        input {
          span := declaration.span
          leadingComments := []
          value := .impl declaration
        } output
  | contract {input output : Remainder} {declaration : Syntax.ContractDecl}
      (earlierAbsent : TopItemKindsAbsentAt input [
        .keyword .importKw, .keyword .exportKw, .keyword .pragmaKw,
        .keyword .typeKw, .keyword .functionKw,
        .identifier ContextualKeyword.enum.spelling,
        .identifier ContextualKeyword.trait.spelling,
        .identifier ContextualKeyword.impl.spelling,
        .keyword .defaultKw])
      (parsed : ContractDeclParses expressionParses allowBodyParses
        requiredBodyParses input declaration output) :
      PlainTopItemParses expressionParses allowBodyParses requiredBodyParses
        input {
          span := declaration.span
          leadingComments := []
          value := .contract declaration
        } output

/--
Strict derive-aware top-item grammar.  A leading hash commits to a derive
attribute; diagnostic freedom permits its attachment only to an enum.
-/
inductive TopItemParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.TopItem → Remainder → Prop where
  | plain {input output : Remainder} {item : Syntax.TopItem}
      (hashAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .hash))
      (parsed : PlainTopItemParses expressionParses allowBodyParses
        requiredBodyParses input item output) :
      TopItemParses expressionParses allowBodyParses requiredBodyParses
        input item output
  | derivedEnum
      {input afterDerive output : Remainder}
      {derive : Syntax.DeriveAttribute} {declaration : Syntax.EnumDecl}
      (deriveParsed : DeriveAttributeParses input derive afterDerive)
      (earlierAbsent : TopItemKindsAbsentAt afterDerive [
        .keyword .importKw, .keyword .exportKw, .keyword .pragmaKw,
        .keyword .typeKw, .keyword .functionKw])
      (enumParsed : EnumDeclParses (some derive)
        afterDerive declaration output) :
      TopItemParses expressionParses allowBodyParses requiredBodyParses
        input {
          span := declaration.span
          leadingComments := []
          value := .enum declaration
        } output

/-! Complete-file accumulation over an abstract top-item grammar. -/

/--
Forward-order grammar of the top-level items remaining after an existing
reverse accumulator.  The terminal condition mirrors the executable file
loop's `atEnd` check; strict progress mirrors its successful-item guard.
-/
inductive TopItemsParses
    (itemParses : Remainder → Syntax.TopItem → Remainder → Prop) :
    Remainder → List Syntax.TopItem → Remainder → Prop where
  | done {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      TopItemsParses itemParses input [] input
  | next {input afterItem output : Remainder}
      {item : Syntax.TopItem} {items : List Syntax.TopItem}
      (itemParsed : itemParses input item afterItem)
      (progress : input.cursor < afterItem.cursor)
      (rest : TopItemsParses itemParses afterItem items output) :
      TopItemsParses itemParses input (item :: items) output

/-- Every complete top-item derivation finishes at its active-window end. -/
theorem TopItemsParses.output_atEnd
    {itemParses : Remainder → Syntax.TopItem → Remainder → Prop}
    {input output : Remainder} {items : List Syntax.TopItem}
    (parsed : TopItemsParses itemParses input items output) :
    output.endIndex ≤ output.cursor := by
  induction parsed with
  | done atEnd => exact atEnd
  | next itemParsed progress rest inductionHypothesis =>
      exact inductionHypothesis

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeRejectionDiagnosticGrammar
/-!
Independent observations and uncommitted rejection reports. The source and
window-end byte are explicit context, separate from the token remainder.
Only the shared diagnostic data catalog is used; reports emit no event yet.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Current-token observation, including unavailable carriers and window ends. -/
inductive CurrentInputAt (source : SourceId) (endByte : Nat) :
    Remainder → SourceSpan → Option TokenKind → Prop where
  | token {input : Remainder} {current : Token}
      (present : TokenAt input.tokens input.endIndex input.cursor current) :
      CurrentInputAt source endByte input current.span (some current.value)
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      CurrentInputAt source endByte input
        { source, startByte := endByte, endByte } none
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      CurrentInputAt source endByte input
        { source, startByte := endByte, endByte } none

/-- Exact unexpected report selected by an expectation and grammar context.
The caller, not this judgment, decides whether to commit it as a diagnostic. -/
inductive RejectAtReports (source : SourceId) (endByte : Nat)
    (expected : NonemptyList ParseExpectation) (context : ParseContext)
    (input : Remainder) : ParseDiagnostic → Prop where
  | reported {span : SourceSpan} {found : Option TokenKind}
      (current : CurrentInputAt source endByte input span found) :
      RejectAtReports source endByte expected context input
        { span, kind := .unexpected found expected context }

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTransactionalFallbackGrammar
/-!
Implementation-independent outcomes for prioritized transactional fallback.

The preferred branch runs first.  Only its exact rejection permits the
fallback branch to run from the original remainder.  When both branches
reject, the wrapper also rejects at that original remainder.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary success of a preferred branch or of a fallback selected by an
exact preferred-branch rejection. -/
inductive TransactionalFallbackOrdinaryParses {alpha : Type}
    (primaryParses : Remainder → alpha → Remainder → Prop)
    (primaryRejects : Remainder → Remainder → Prop)
    (fallbackParses : Remainder → alpha → Remainder → Prop) :
    Remainder → alpha → Remainder → Prop where
  | primary {input output : Remainder} {value : alpha}
      (parsed : primaryParses input value output) :
      TransactionalFallbackOrdinaryParses primaryParses primaryRejects
        fallbackParses input value output
  | fallback {input primaryRejected output : Remainder} {value : alpha}
      (primaryRejection : primaryRejects input primaryRejected)
      (parsed : fallbackParses input value output) :
      TransactionalFallbackOrdinaryParses primaryParses primaryRejects
        fallbackParses input value output

/-- Exact rejection when both transactional alternatives reject.  Intermediate
rejected remainders are retained as evidence, while the wrapper rejects at its
original input remainder. -/
inductive TransactionalFallbackRejects
    (primaryRejects fallbackRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | both {input primaryRejected fallbackRejected : Remainder}
      (primaryRejection : primaryRejects input primaryRejected)
      (fallbackRejection : fallbackRejects input fallbackRejected) :
      TransactionalFallbackRejects primaryRejects fallbackRejects input input

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreBlockGrammar
/-!
Parser-independent grammar for raw braced Core statement sequences.

This layer describes direct block recognition inside one active token window.
It does not include the parser's balanced-block isolation wrapper.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Whether the final expression statement of a Core block needs a semicolon. -/
inductive CoreBlockTailPolicy where
  | allow
  | require
  deriving Repr, BEq, DecidableEq

/-- A statement is acceptable where an expression semicolon is mandatory. -/
def CoreBlockStatementTerminated (statement : Syntax.Statement) : Prop :=
  match statement.value with
  | .expression _ false => False
  | _ => True

/--
Exact diagnostic-free condition imposed by Core block-tail validation.

Every non-final expression statement must retain a semicolon.  The final
statement has the same requirement under `require`, while `allow` accepts it
unchanged.  Empty blocks and every non-expression statement are accepted.
-/
def CoreBlockTailsValid :
    CoreBlockTailPolicy → List Syntax.Statement → Prop
  | _, [] => True
  | .allow, [_] => True
  | .require, [last] => CoreBlockStatementTerminated last
  | policy, first :: second :: rest =>
      CoreBlockStatementTerminated first ∧
        CoreBlockTailsValid policy (second :: rest)

@[simp] theorem coreBlockTailsValid_nil (policy : CoreBlockTailPolicy) :
    CoreBlockTailsValid policy [] := by
  simp [CoreBlockTailsValid]

@[simp] theorem coreBlockTailsValid_allow_singleton
    (statement : Syntax.Statement) :
    CoreBlockTailsValid .allow [statement] := by
  simp [CoreBlockTailsValid]

@[simp] theorem coreBlockTailsValid_require_singleton
    (statement : Syntax.Statement) :
    CoreBlockTailsValid .require [statement] =
      CoreBlockStatementTerminated statement := by
  simp [CoreBlockTailsValid]

@[simp] theorem coreBlockTailsValid_cons_cons
    (policy : CoreBlockTailPolicy) (first second : Syntax.Statement)
    (rest : List Syntax.Statement) :
    CoreBlockTailsValid policy (first :: second :: rest) =
      (CoreBlockStatementTerminated first ∧
        CoreBlockTailsValid policy (second :: rest)) := by
  simp [CoreBlockTailsValid]

/--
Forward-order Core statements followed by their exact closing brace.

The recursive branch records that the preferred right-brace branch did not
match.  Its strict progress premise mirrors the executable loop's successful
statement guard independently of that loop's fuel bound.
-/
inductive CoreBlockItemsParses
    (statementParses :
      Remainder → Syntax.Statement → Remainder → Prop) :
    Remainder → List Syntax.Statement → SourceSpan →
      Remainder → Prop where
  | close {input output : Remainder} (closingSpan : SourceSpan)
      (closingToken : ExactTokenParses (.symbol .rightBrace)
        input closingSpan output) :
      CoreBlockItemsParses statementParses input [] closingSpan output
  | next {input afterStatement output : Remainder}
      {statement : Syntax.Statement} {statements : List Syntax.Statement}
      {closingSpan : SourceSpan}
      (notAtEnd : input.cursor < input.endIndex)
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (statementParsed : statementParses input statement afterStatement)
      (progress : input.cursor < afterStatement.cursor)
      (tail : CoreBlockItemsParses statementParses afterStatement statements
        closingSpan output) :
      CoreBlockItemsParses statementParses input (statement :: statements)
        closingSpan output

/-- A block-items derivation consumes at least its closing brace. -/
theorem CoreBlockItemsParses.cursor_lt
    {statementParses :
      Remainder → Syntax.Statement → Remainder → Prop}
    {input output : Remainder} {statements : List Syntax.Statement}
    {closingSpan : SourceSpan}
    (parsed : CoreBlockItemsParses statementParses input statements
      closingSpan output) :
    input.cursor < output.cursor := by
  induction parsed with
  | close closingSpan closingToken =>
      rcases closingToken with ⟨_, rfl⟩
      simp
  | next notAtEnd closingAbsent statementParsed progress tail
      inductionHypothesis =>
      exact Nat.lt_trans progress inductionHypothesis

/--
Block items preserve their active token window whenever the abstract statement
judgment does.
-/
theorem CoreBlockItemsParses.output_window
    {statementParses :
      Remainder → Syntax.Statement → Remainder → Prop}
    (statementWindow : ∀ {input statement output},
      statementParses input statement output →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {statements : List Syntax.Statement}
    {closingSpan : SourceSpan}
    (parsed : CoreBlockItemsParses statementParses input statements
      closingSpan output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  induction parsed with
  | close closingSpan closingToken =>
      rcases closingToken with ⟨_, rfl⟩
      exact ⟨rfl, rfl⟩
  | next notAtEnd closingAbsent statementParsed progress tail
      inductionHypothesis =>
      have step := statementWindow statementParsed
      exact ⟨inductionHypothesis.1.trans step.1,
        inductionHypothesis.2.trans step.2⟩

/-- Exact braces, covering span, source-order body, and tail policy of a block. -/
inductive CoreBlockParses
    (statementParses :
      Remainder → Syntax.Statement → Remainder → Prop)
    (policy : CoreBlockTailPolicy) :
    Remainder → Syntax.Block → Remainder → Prop where
  | parsed {input afterOpening output : Remainder}
      {body : List Syntax.Statement} (openingSpan closingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBrace)
        input openingSpan afterOpening)
      (bodyParsed : CoreBlockItemsParses statementParses afterOpening body
        closingSpan output)
      (tailsValid : CoreBlockTailsValid policy body) :
      CoreBlockParses statementParses policy input {
        span := SourceSpan.cover openingSpan closingSpan
        value := body
      } output

/-- Every raw Core block derivation makes strict cursor progress. -/
theorem CoreBlockParses.cursor_lt
    {statementParses :
      Remainder → Syntax.Statement → Remainder → Prop}
    {policy : CoreBlockTailPolicy} {input output : Remainder}
    {block : Syntax.Block}
    (parsed : CoreBlockParses statementParses policy input block output) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed openingSpan closingSpan openingToken bodyParsed tailsValid =>
      rcases openingToken with ⟨_, rfl⟩
      exact Nat.lt_trans (by simp) bodyParsed.cursor_lt

/--
A raw Core block preserves its active window whenever its statement judgment
does.
-/
theorem CoreBlockParses.output_window
    {statementParses :
      Remainder → Syntax.Statement → Remainder → Prop}
    (statementWindow : ∀ {input statement output},
      statementParses input statement output →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {policy : CoreBlockTailPolicy} {input output : Remainder}
    {block : Syntax.Block}
    (parsed : CoreBlockParses statementParses policy input block output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed openingSpan closingSpan openingToken bodyParsed tailsValid =>
      rcases openingToken with ⟨_, rfl⟩
      exact bodyParsed.output_window statementWindow

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreBlockTailTraceGrammar
/-! Independent source-ordered diagnostics for Core expression semicolons.
Non-final statements are checked under both policies. Only the final statement
is exempt under `allow`; every missing required semicolon contributes one event. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A mandatory statement-termination check emits exactly one constraint
report at the full statement span, or no report when termination is valid. -/
inductive CoreBlockStatementDiagnosticTrace (statement : Syntax.Statement) :
    List ParseDiagnostic → Prop where
  | clean (terminated : CoreBlockStatementTerminated statement) :
      CoreBlockStatementDiagnosticTrace statement []
  | missing (unterminated : ¬ CoreBlockStatementTerminated statement) :
      CoreBlockStatementDiagnosticTrace statement
        [{ span := statement.span, kind := .constraintViolation .expressionRequiresSemicolon }]

/-- Complete tail validation follows written statement order. The separate
singleton constructors make the final-statement policy explicit. -/
inductive CoreBlockTailsDiagnosticTrace :
    CoreBlockTailPolicy → List Syntax.Statement → List ParseDiagnostic → Prop where
  | nil {policy : CoreBlockTailPolicy} : CoreBlockTailsDiagnosticTrace policy [] []
  | lastAllowed {last : Syntax.Statement} : CoreBlockTailsDiagnosticTrace .allow [last] []
  | lastRequired {last : Syntax.Statement} {trace : List ParseDiagnostic}
      (checked : CoreBlockStatementDiagnosticTrace last trace) :
      CoreBlockTailsDiagnosticTrace .require [last] trace
  | cons {policy : CoreBlockTailPolicy} {first second : Syntax.Statement}
      {rest : List Syntax.Statement} {headTrace tailTrace : List ParseDiagnostic}
      (checked : CoreBlockStatementDiagnosticTrace first headTrace)
      (tail : CoreBlockTailsDiagnosticTrace policy (second :: rest) tailTrace) :
      CoreBlockTailsDiagnosticTrace policy (first :: second :: rest) (headTrace ++ tailTrace)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar
/-!
Parser-independent ordinary outcomes and exact rejection traces for generic
delimited lists.

The successful relation is intentionally allowed to be broader than a clean
grammar: transactional parsing can consume diagnosed elements before a later
ordinary rejection rewinds the whole attempt.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Deterministic, exclusive ordinary outcomes of one nested production. -/
structure DeterministicOutcomeSpec {α : Type}
    (ordinaryParses : Remainder → α → Remainder → Prop)
    (rejects : Remainder → Remainder → Prop) where
  successOutputUnique : ∀ {input : Remainder} {left right : α}
    {afterLeft afterRight : Remainder},
    ordinaryParses input left afterLeft →
    ordinaryParses input right afterRight →
    afterLeft = afterRight
  successRejectDisjoint : ∀ {input rejected : Remainder},
    rejects input rejected →
    ¬ ∃ value output, ordinaryParses input value output

/-- Evidence that a preferred immediate-close branch did not run. -/
inductive PreferredCloseNotTaken (closing : Symbol) :
    Bool → Remainder → Prop where
  | disabled {input : Remainder} :
      PreferredCloseNotTaken closing false input
  | absent {input : Remainder}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol closing)) :
      PreferredCloseNotTaken closing true input

/-- Exact ordinary-rejection trace after at least one delimited element. -/
inductive DelimitedTailRejects {α : Type} (closing : Symbol)
    (allowTrailing : Bool)
    (ordinaryParses : Remainder → α → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | delimiterMissing {input : Remainder}
      (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .comma))
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol closing)) :
      DelimitedTailRejects closing allowTrailing ordinaryParses nestedRejects
        input input
  | elementRejected {input rejected : Remainder} (commaSpan : SourceSpan)
      (commaToken : TokenAt input.tokens input.endIndex input.cursor {
        span := commaSpan
        value := .symbol .comma
      })
      (continues : PreferredCloseNotTaken closing allowTrailing
        { input with cursor := input.cursor + 1 })
      (nestedRejected : nestedRejects
        { input with cursor := input.cursor + 1 } rejected) :
      DelimitedTailRejects closing allowTrailing ordinaryParses nestedRejects
        input rejected
  | laterRejected {input afterElement rejected : Remainder}
      {element : α} (commaSpan : SourceSpan)
      (commaToken : TokenAt input.tokens input.endIndex input.cursor {
        span := commaSpan
        value := .symbol .comma
      })
      (continues : PreferredCloseNotTaken closing allowTrailing
        { input with cursor := input.cursor + 1 })
      (elementParsed : ordinaryParses
        { input with cursor := input.cursor + 1 } element afterElement)
      (progress : input.cursor + 1 < afterElement.cursor)
      (tailRejected : DelimitedTailRejects closing allowTrailing
        ordinaryParses nestedRejects afterElement rejected) :
      DelimitedTailRejects closing allowTrailing ordinaryParses nestedRejects
        input rejected

/-- Exact ordinary-rejection trace for a complete delimited-list attempt. -/
inductive DelimitedListRejects {α : Type} (opening closing : Symbol)
    (allowEmpty allowTrailing : Bool)
    (ordinaryParses : Remainder → α → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | openingMissing {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol opening)) :
      DelimitedListRejects opening closing allowEmpty allowTrailing
        ordinaryParses nestedRejects input input
  | firstRejected {input rejected : Remainder} (openingSpan : SourceSpan)
      (openingToken : TokenAt input.tokens input.endIndex input.cursor {
        span := openingSpan
        value := .symbol opening
      })
      (continues : PreferredCloseNotTaken closing allowEmpty
        { input with cursor := input.cursor + 1 })
      (nestedRejected : nestedRejects
        { input with cursor := input.cursor + 1 } rejected) :
      DelimitedListRejects opening closing allowEmpty allowTrailing
        ordinaryParses nestedRejects input rejected
  | tailRejected {input afterFirst rejected : Remainder} {first : α}
      (openingSpan : SourceSpan)
      (openingToken : TokenAt input.tokens input.endIndex input.cursor {
        span := openingSpan
        value := .symbol opening
      })
      (continues : PreferredCloseNotTaken closing allowEmpty
        { input with cursor := input.cursor + 1 })
      (firstParsed : ordinaryParses
        { input with cursor := input.cursor + 1 } first afterFirst)
      (progress : input.cursor + 1 < afterFirst.cursor)
      (tailRejected : DelimitedTailRejects closing allowTrailing
        ordinaryParses nestedRejects afterFirst rejected) :
      DelimitedListRejects opening closing allowEmpty allowTrailing
        ordinaryParses nestedRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExactOutcomeSpec
/-! Reusable full-functionality contract for declarative parser outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/--
A deterministic ordinary outcome whose successful value and rejecting
remainder are also unique. This strengthens `DeterministicOutcomeSpec`, whose
base contract intentionally fixes only successful remainders and branch
exclusion.
-/
structure ExactDeterministicOutcomeSpec {α : Type}
    (ordinaryParses : Remainder → α → Remainder → Prop)
    (rejects : Remainder → Remainder → Prop)
    extends DeterministicOutcomeSpec ordinaryParses rejects where
  successValueUnique : ∀ {input : Remainder} {left right : α}
    {afterLeft afterRight : Remainder},
    ordinaryParses input left afterLeft →
    ordinaryParses input right afterRight →
    left = right
  rejectOutputUnique : ∀ {input left right : Remainder},
    rejects input left → rejects input right → left = right

namespace ExactDeterministicOutcomeSpec

/-- Exact outcome functionality fixes the successful value and remainder. -/
theorem successResultUnique {α : Type}
    {ordinaryParses : Remainder → α → Remainder → Prop}
    {rejects : Remainder → Remainder → Prop}
    (spec : ExactDeterministicOutcomeSpec ordinaryParses rejects)
    {input : Remainder} {left right : α}
    {afterLeft afterRight : Remainder}
    (leftParsed : ordinaryParses input left afterLeft)
    (rightParsed : ordinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨spec.successValueUnique leftParsed rightParsed,
    spec.successOutputUnique leftParsed rightParsed⟩

end ExactDeterministicOutcomeSpec

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNestingOutcomeGrammar
/-!
Parser-independent exact outcomes for the bounded nesting preflight. The
relation scans tokens in source order and returns the first delimiter or
conditional overflow without exposing the executable scanner state.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Stable nesting limit of the canonical source grammar. -/
def canonicalNestingLimit : Nat := 128

/-- Declarative nesting context carried between source-order tokens. -/
structure NestingContext where
  delimiterDepth : Nat := 0
  conditionalDepth : Nat := 0
  conditionalBases : List Nat := []
  deriving Repr, BEq, DecidableEq

/-- Declarative recursive dimension checked by the nesting preflight. -/
inductive NestingDimension where
  | delimiter
  | conditional
  deriving Repr, BEq, DecidableEq

/-- Exact first token and bound of one declarative nesting overflow. -/
structure NestingOverflow where
  span : SourceSpan
  dimension : NestingDimension
  limit : Nat
  deriving Repr, BEq, DecidableEq

/-- Grammar-relevant effect of one token on bounded nesting. -/
inductive NestingAction where
  | conditional
  | groupOpen
  | blockOpen
  | close
  | reset
  | preserve
  deriving Repr, BEq, DecidableEq

/-- Classify one token by its declarative nesting effect. -/
def nestingAction : TokenKind → NestingAction
  | .keyword .ifKw => .conditional
  | .symbol .leftParen | .symbol .leftBracket => .groupOpen
  | .symbol .leftBrace => .blockOpen
  | .symbol .rightParen | .symbol .rightBracket |
      .symbol .rightBrace => .close
  | .symbol .comma | .symbol .semicolon => .reset
  | _ => .preserve

/-- Closing a delimiter restores the conditional base of its outer scope. -/
def NestingContext.closeDelimiter
    (context : NestingContext) : NestingContext := {
  delimiterDepth := context.delimiterDepth - 1
  conditionalDepth := context.conditionalBases.head?.getD 0
  conditionalBases := context.conditionalBases.tail
}

/-- A comma or semicolon restarts conditionals at the current scope base. -/
def NestingContext.resetConditional
    (context : NestingContext) : NestingContext := {
  context with
  conditionalDepth := context.conditionalBases.head?.getD 0
}

/-- Exact overflow generated at the first token beyond one bound. -/
def nestingOverflow (limit : Nat) (dimension : NestingDimension)
    (token : Token) : NestingOverflow := {
  span := token.span
  dimension
  limit
}

/-- Priority-ordered bounded nesting scan. Each continuation consumes exactly
one token; an exceeded constructor stops at the first overflowing token. -/
inductive NestingScans (limit : Nat) :
    NestingContext → List Token → Option NestingOverflow → Prop where
  | done {context : NestingContext} :
      NestingScans limit context [] none
  | conditionalExceeded {context : NestingContext} {token : Token}
      {rest : List Token}
      (action : nestingAction token.value = .conditional)
      (exceeds : limit < context.conditionalDepth + 1) :
      NestingScans limit context (token :: rest)
        (some (nestingOverflow limit .conditional token))
  | conditionalContinues {context : NestingContext} {token : Token}
      {rest : List Token} {result : Option NestingOverflow}
      (action : nestingAction token.value = .conditional)
      (within : context.conditionalDepth + 1 ≤ limit)
      (tail : NestingScans limit
        { context with conditionalDepth := context.conditionalDepth + 1 }
        rest result) :
      NestingScans limit context (token :: rest) result
  | groupExceeded {context : NestingContext} {token : Token}
      {rest : List Token}
      (action : nestingAction token.value = .groupOpen)
      (exceeds : limit < context.delimiterDepth + 1) :
      NestingScans limit context (token :: rest)
        (some (nestingOverflow limit .delimiter token))
  | groupContinues {context : NestingContext} {token : Token}
      {rest : List Token} {result : Option NestingOverflow}
      (action : nestingAction token.value = .groupOpen)
      (within : context.delimiterDepth + 1 ≤ limit)
      (tail : NestingScans limit {
        delimiterDepth := context.delimiterDepth + 1
        conditionalDepth := context.conditionalDepth
        conditionalBases := context.conditionalDepth ::
          context.conditionalBases
      } rest result) :
      NestingScans limit context (token :: rest) result
  | blockExceeded {context : NestingContext} {token : Token}
      {rest : List Token}
      (action : nestingAction token.value = .blockOpen)
      (exceeds : limit < context.delimiterDepth + 1) :
      NestingScans limit context (token :: rest)
        (some (nestingOverflow limit .delimiter token))
  | blockContinues {context : NestingContext} {token : Token}
      {rest : List Token} {result : Option NestingOverflow}
      (action : nestingAction token.value = .blockOpen)
      (within : context.delimiterDepth + 1 ≤ limit)
      (tail : NestingScans limit {
        delimiterDepth := context.delimiterDepth + 1
        conditionalDepth := 0
        conditionalBases := 0 :: context.conditionalBases
      } rest result) :
      NestingScans limit context (token :: rest) result
  | close {context : NestingContext} {token : Token}
      {rest : List Token} {result : Option NestingOverflow}
      (action : nestingAction token.value = .close)
      (tail : NestingScans limit context.closeDelimiter rest result) :
      NestingScans limit context (token :: rest) result
  | reset {context : NestingContext} {token : Token}
      {rest : List Token} {result : Option NestingOverflow}
      (action : nestingAction token.value = .reset)
      (tail : NestingScans limit context.resetConditional rest result) :
      NestingScans limit context (token :: rest) result
  | preserve {context : NestingContext} {token : Token}
      {rest : List Token} {result : Option NestingOverflow}
      (action : nestingAction token.value = .preserve)
      (tail : NestingScans limit context rest result) :
      NestingScans limit context (token :: rest) result

/-- Canonical whole-token nesting outcome from the root context. -/
def NestingOutcome (tokens : List Token)
    (result : Option NestingOverflow) : Prop :=
  NestingScans canonicalNestingLimit {} tokens result

/-- No token exceeds either canonical nesting bound. -/
def NestingClears (tokens : List Token) : Prop :=
  NestingOutcome tokens none

/-- Exact first canonical nesting violation. -/
def NestingExceeds (tokens : List Token)
    (overflow : NestingOverflow) : Prop :=
  NestingOutcome tokens (some overflow)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreIdentifierOutcomeGrammar
/-! Parser-independent exact rejection for one checked Core identifier. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- No ordinary identifier token occurs at the current grammar cursor. -/
def IdentifierAbsentAt (input : Remainder) : Prop :=
  ¬ ∃ span text, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .identifier text
  }

/-- Exact non-consuming rejection of the checked Core identifier primitive. -/
inductive IdentifierRejects : Remainder → Remainder → Prop where
  | absent {input : Remainder}
      (identifierAbsent : IdentifierAbsentAt input) :
      IdentifierRejects input input

end Solcore.Syntax.DeclarativeGrammar
end
