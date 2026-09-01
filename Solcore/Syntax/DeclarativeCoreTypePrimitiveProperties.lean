import Solcore.Syntax.DeclarativeCoreTypeOutcomeGrammar

/-! Primitive functionality facts used by declarative Core-type outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem typeTokenAbsent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

theorem typeTokenAt_kind_eq {tokens : Array Token} {endIndex index : Nat}
    {leftKind rightKind : TokenKind} {leftSpan rightSpan : SourceSpan}
    (left : TokenAt tokens endIndex index {
      span := leftSpan
      value := leftKind
    })
    (right : TokenAt tokens endIndex index {
      span := rightSpan
      value := rightKind
    }) : leftKind = rightKind := by
  have tokenEq : ({ span := leftSpan, value := leftKind } : Token) =
      { span := rightSpan, value := rightKind } := by
    apply Option.some.inj
    rw [← left.2, ← right.2]
  exact congrArg (fun token : Token => token.value) tokenEq

theorem typeExactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (left : ExactTokenParses kind input leftSpan leftOutput)
    (right : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [left.2, right.2]

/-- Two consecutive exact tokens witness a contextual dispatch guard. -/
theorem contextualPair_present_of_exact
    {keyword : ContextualKeyword} {symbol : Symbol}
    {input afterMarker afterOpening : Remainder}
    {markerSpan openingSpan : SourceSpan}
    (markerParsed : ExactTokenParses (.identifier keyword.spelling) input
      markerSpan afterMarker)
    (openingParsed : ExactTokenParses (.symbol symbol) afterMarker
      openingSpan afterOpening) :
    ∃ markerSpan openingSpan,
      TokenAt input.tokens input.endIndex input.cursor {
        span := markerSpan
        value := .identifier keyword.spelling
      } ∧ TokenAt input.tokens input.endIndex (input.cursor + 1) {
        span := openingSpan
        value := .symbol symbol
      } := by
  refine ⟨markerSpan, openingSpan, markerParsed.1, ?_⟩
  simpa [markerParsed.2] using openingParsed.1

private theorem DottedIdentifierTailParses.output_unique
    {tokens : Array Token} {endIndex cursor : Nat}
    {left right : List Syntax.Identifier} {afterLeft afterRight : Nat}
    (leftParsed : DottedIdentifierTailParses tokens endIndex cursor left
      afterLeft)
    (rightParsed : DottedIdentifierTailParses tokens endIndex cursor right
      afterRight) : afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done cursor stopped =>
      cases rightParsed with
      | done => rfl
      | next dotSpan dotToken componentToken tail =>
          exact False.elim
            (typeTokenAbsent_conflicts_token stopped dotToken)
  | next dotSpan dotToken componentToken tail inductionHypothesis =>
      cases rightParsed with
      | done cursor stopped =>
          exact False.elim
            (typeTokenAbsent_conflicts_token stopped dotToken)
      | next => exact inductionHypothesis (by assumption)

/-- Qualified-name recognition has one output remainder. -/
theorem QualifiedNameParses.output_unique {input : Remainder}
    {left right : Syntax.QualifiedName} {afterLeft afterRight : Remainder}
    (leftParsed : QualifiedNameParses input left afterLeft)
    (rightParsed : QualifiedNameParses input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with
    ⟨leftTokens, leftEndIndex, leftFirst, leftTail, leftSpan⟩
  rcases rightParsed with
    ⟨rightTokens, rightEndIndex, rightFirst, rightTail, rightSpan⟩
  have cursorEq := DottedIdentifierTailParses.output_unique leftTail rightTail
  cases input
  cases afterLeft
  cases afterRight
  simp_all

/-- Every recursive type list exposes its exact opening token. -/
theorem TypeExprTrailingDelimitedListParses.opening_token
    {opening closing : Symbol} {input output : Remainder}
    {values : DelimitedList Syntax.TypeExpr}
    (parsed : TypeExprTrailingDelimitedListParses opening closing input values
      output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span
      value := .symbol opening
    } := by
  cases parsed with
  | empty openingSpan => exact ⟨openingSpan, by assumption⟩
  | nonempty openingSpan => exact ⟨openingSpan, by assumption⟩

end Solcore.Syntax.DeclarativeGrammar
