import Solcore.Syntax.Parser.Primitive

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private def closeDelimited {α : Type} (opening : Token)
    (closing : Symbol) (context : ParseContext)
    (elementsRev : List α) : Parser (DelimitedList α) := fun state =>
  match symbol closing context state with
  | .ok token next => .ok {
      span := SourceSpan.cover opening.span token.span
      elements := elementsRev.reverse
    } next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

private def afterDelimitedElement {α : Type}
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
