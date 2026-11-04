import Solcore.Syntax.Token
import Solcore.Syntax.Parser.State
import Solcore.Syntax.Parser.Diagnostic
import Solcore.Syntax.Foundation
import Solcore.Syntax.Parser.Primitive
import Solcore.Syntax.Source
import Solcore.Syntax.Literal
import Solcore.Syntax.Module

/-!
Parsers for names, literals, operators and delimited lists.

Main declarations: `qualifiedName`, `coreLiteral`, `selectorName`, `delimited`,
`delimitedNoTrailing`.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.Front.Name
set_option autoImplicit false

namespace Solcore.Syntax.Parser

/- Proof-visible qualified-name parser components. -/
namespace QualifiedNameInternals

/-- Finish a qualified name from its first, last, and reversed tail parts. -/
def finishQualifiedName (first last : Identifier)
    (tailRev : List Identifier) (state : State) : Reply QualifiedName :=
  .ok {
    span := SourceSpan.cover first.span last.span
    value := {
      components := {
        head := first
        tail := tailRev.reverse
      }
    }
  } state

/-- Fuel-bounded dotted tail used by the public qualified-name parser. -/
def qualifiedNameTail (context : ParseContext)
    (phase : ParserPhase) (first : Identifier) :
    Nat → Identifier → List Identifier → State → Reply QualifiedName
  | 0, _, _, state => .invariant (.fuelExhausted phase state.currentSpan)
  | fuel + 1, last, tailRev, state =>
      if isSymbol state .dot then
        match symbol .dot context state with
        | .ok _ afterDot =>
            match identifier context afterDot with
            | .ok component next =>
                qualifiedNameTail context phase first fuel component
                  (component :: tailRev) next
            | .reject failure next => .reject failure next
            | .invariant error => .invariant error
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        finishQualifiedName first last tailRev state

end QualifiedNameInternals

open QualifiedNameInternals

/-- Parse one nonempty dotted ordinary-identifier path. -/
def qualifiedName (context : ParseContext)
    (phase : ParserPhase) : Parser QualifiedName := fun state =>
  match identifier context state with
  | .ok first next =>
      qualifiedNameTail context phase first (next.remainingCount + 1)
        first [] next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.Literal
set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Parse one literal admitted by Core expressions and patterns. -/
def coreLiteral : Parser CoreLiteral := fun state =>
  match state.peek? with
  | some { span, value := .decimalLiteral spelling } =>
      .ok { span, value := .decimal spelling }
        { state with cursor := state.cursor + 1 }
  | some { span, value := .hexadecimalLiteral spelling } =>
      .ok { span, value := .hexadecimal spelling }
        { state with cursor := state.cursor + 1 }
  | some { span, value := .stringLiteral spelling } =>
      .ok { span, value := .string spelling }
        { state with cursor := state.cursor + 1 }
  | _ => rejectAt state { head := .coreLiteral, tail := [] } .expression

/-- Preserve `true` and `false` as identifier-shaped builtin values. -/
def booleanIdentifier : Parser Identifier := fun state =>
  match state.peek? with
  | some { span, value := .keyword .trueKw } =>
      .ok { span, value := "true" }
        { state with cursor := state.cursor + 1 }
  | some { span, value := .keyword .falseKw } =>
      .ok { span, value := "false" }
        { state with cursor := state.cursor + 1 }
  | _ => rejectAt state { head := .expression, tail := [] } .expression

def isCoreLiteral (state : State) : Bool :=
  match state.peekKind? with
  | some (.decimalLiteral _)
  | some (.hexadecimalLiteral _)
  | some (.stringLiteral _) => true
  | _ => false

def isBooleanValue (state : State) : Bool :=
  isKeyword state .trueKw || isKeyword state .falseKw

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.Operator
set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Exact operator-token subset accepted inside import/export parentheses. -/
def operatorPart? : TokenKind → Option String
  | .symbol .colonEqual => some ":="
  | .symbol .arrow => some "->"
  | .symbol .fatArrow => some "=>"
  | .symbol .equalEqual => some "=="
  | .symbol .notEqual => some "!="
  | .symbol .greaterEqual => some ">="
  | .symbol .lessEqual => some "<="
  | .symbol .logicalAnd => some "&&"
  | .symbol .logicalOr => some "||"
  | .symbol .plusEqual => some "+="
  | .symbol .minusEqual => some "-="
  | .symbol .starEqual => some "*="
  | .symbol .slashEqual => some "/="
  | .symbol .caretEqual => some "^="
  | .symbol .ampEqual => some "&="
  | .symbol .pipeEqual => some "|="
  | .symbol .percentEqual => some "%="
  | .symbol .tildeEqual => some "~="
  | .symbol .plus => some "+"
  | .symbol .minus => some "-"
  | .symbol .star => some "*"
  | .symbol .slash => some "/"
  | .symbol .percent => some "%"
  | .symbol .bang => some "!"
  | .symbol .tilde => some "~"
  | .symbol .less => some "<"
  | .symbol .greater => some ">"
  | .symbol .equal => some "="
  | .symbol .pipe => some "|"
  | .symbol .amp => some "&"
  | .symbol .caret => some "^"
  | .symbol .colon => some ":"
  | _ => none

def isOperatorPart (kind : TokenKind) : Bool :=
  (operatorPart? kind).isSome

namespace OperatorInternals

/-- Fuel-bounded token collector used by parenthesized operator selectors. -/
def operatorParts (context : ParseContext) :
    Nat → List String → State → Reply (List String)
  | 0, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, partsRev, state =>
      match state.peek? with
      | some token =>
          match operatorPart? token.value with
          | some spelling =>
              operatorParts context fuel (spelling :: partsRev)
                { state with cursor := state.cursor + 1 }
          | none =>
              if partsRev.isEmpty then
                rejectAt state { head := .selectorName, tail := [] } context
              else
                .ok partsRev.reverse state
      | none =>
          if partsRev.isEmpty then
            rejectAt state { head := .selectorName, tail := [] } context
          else
            .ok partsRev.reverse state

end OperatorInternals

open OperatorInternals

/-- Parse a nonempty parenthesized operator selector. -/
def operatorSelector (context : ParseContext) : Parser SelectorName := fun state =>
  match symbol .leftParen context state with
  | .ok opening afterOpening =>
      match operatorParts context (afterOpening.remainingCount + 1) []
          afterOpening with
      | .ok parts afterParts =>
          match symbol .rightParen context afterParts with
          | .ok closing next => .ok {
              span := SourceSpan.cover opening.span closing.span
              value := .operator (String.join parts)
            } next
          | .reject failure next => .reject failure next
          | .invariant error => .invariant error
      | .reject failure next => .reject failure next
      | .invariant error => .invariant error
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

/-- Parse either an ordinary identifier or a parenthesized operator. -/
def selectorName (context : ParseContext) : Parser SelectorName := fun state =>
  if isSymbol state .leftParen then
    operatorSelector context state
  else
    match identifier context state with
    | .ok name next => .ok {
        span := name.span
        value := .identifier name
      } next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.TopLevel
set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Synchronization starts shared with the pinned Rust top-level grammar. -/
def isTopItemStartKind : TokenKind → Bool
  | .keyword .importKw | .keyword .exportKw | .keyword .pragmaKw |
      .keyword .typeKw | .keyword .contractKw | .keyword .functionKw |
      .keyword .defaultKw | .symbol .hash => true
  | kind => kind.isContextual .enum || kind.isContextual .trait ||
      kind.isContextual .impl

def atTopItemStart (state : State) : Bool :=
  match state.peekKind? with
  | some kind => isTopItemStartKind kind
  | none => false

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.Delimited
set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Proof-visible closing step for generic delimited parser laws. -/
def closeDelimited {α : Type} (opening : Token)
    (closing : Symbol) (context : ParseContext)
    (elementsRev : List α) : Parser (DelimitedList α) := fun state =>
  match symbol closing context state with
  | .ok token next => .ok {
      span := SourceSpan.cover opening.span token.span
      elements := elementsRev.reverse
    } next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

/-- Proof-visible fuel loop for generic delimited parser laws. -/
def afterDelimitedElement {α : Type}
    (element : Parser α) (closing : Symbol)
    (allowTrailing : Bool)
    (context : ParseContext) (phase : ParserPhase)
    (opening : Token) :
    Nat → List α → State → Reply (DelimitedList α)
  | 0, _, state => .invariant (.fuelExhausted phase state.currentSpan)
  | fuel + 1, elementsRev, state =>
      if isSymbol state .comma then
        match symbol .comma context state with
        | .ok _ afterComma =>
            if allowTrailing && isSymbol afterComma closing then
              closeDelimited opening closing context elementsRev afterComma
            else
              let before := afterComma.cursor
              match element afterComma with
              | .ok value next =>
                  if next.cursor > before then
                    afterDelimitedElement element closing allowTrailing context phase opening
                      fuel (value :: elementsRev) next
                  else
                    .invariant (.noProgress phase next.currentSpan)
              | .reject failure next => .reject failure next
              | .invariant error => .invariant error
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else if isSymbol state closing then
        closeDelimited opening closing context elementsRev state
      else
        rejectAt state {
          head := .symbol .comma
          tail := [.symbol closing]
        } context

/--
Parse a comma-separated delimited sequence. Empty and trailing-comma policy is
selected by the caller; every accepted element must advance the cursor.
-/
def delimitedWithPolicy {α : Type} (opening closing : Symbol)
    (allowEmpty allowTrailing : Bool)
    (element : Parser α) (context : ParseContext)
    (phase : ParserPhase) : Parser (DelimitedList α) := fun state =>
  match symbol opening context state with
  | .ok openingToken afterOpening =>
      if allowEmpty && isSymbol afterOpening closing then
        closeDelimited openingToken closing context [] afterOpening
      else
        let before := afterOpening.cursor
        match element afterOpening with
        | .ok value next =>
            if next.cursor > before then
              afterDelimitedElement element closing allowTrailing context phase openingToken
                (afterOpening.remainingCount + 1) [value] next
            else
              .invariant (.noProgress phase next.currentSpan)
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

/-- Parse a delimited list whose final comma is accepted. -/
def delimited {α : Type} (opening closing : Symbol) (allowEmpty : Bool)
    (element : Parser α) (context : ParseContext)
    (phase : ParserPhase) : Parser (DelimitedList α) :=
  delimitedWithPolicy opening closing allowEmpty true element context phase

/-- Parse a delimited list whose final comma is rejected. -/
def delimitedNoTrailing {α : Type} (opening closing : Symbol)
    (allowEmpty : Bool) (element : Parser α) (context : ParseContext)
    (phase : ParserPhase) : Parser (DelimitedList α) :=
  delimitedWithPolicy opening closing allowEmpty false element context phase

end Solcore.Syntax.Parser
end
