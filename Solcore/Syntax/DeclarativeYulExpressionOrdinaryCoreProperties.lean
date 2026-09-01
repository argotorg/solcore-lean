import Solcore.Syntax.DeclarativeDelimitedTrailingSuccessProperties
import Solcore.Syntax.DeclarativeYulExpressionOrdinaryGrammar
import Solcore.Syntax.DeclarativeYulNameOutcomeProperties

/-!
Functionality and clean-grammar embeddings for ordinary inline-Yul expression
cores.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- Every successful call-argument list exposes its opening delimiter. -/
theorem YulCallArgumentsParses.opening_present
    {nestedParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {input output : Remainder} {arguments : DelimitedList Syntax.YulExpr}
    (parsed : YulCallArgumentsParses nestedParses input arguments output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span
      value := .symbol .leftParen
    } := by
  cases parsed with
  | empty openingSpan closingSpan openingToken closingToken =>
      exact ⟨openingSpan, openingToken⟩
  | nonempty closingAbsent parsed =>
      rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
        tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
        elementsEq, spanEq⟩
      exact ⟨openingSpan, openingToken⟩

/-- Ordinary call-argument rejection excludes ordinary call-argument success. -/
theorem YulCallArgumentsRejects.disjointOrdinary
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input : Remainder}
    (rejected : YulCallArgumentsRejects ordinaryParses nestedRejects input) :
    ¬ ∃ arguments output,
      YulCallArgumentsParses ordinaryParses input arguments output := by
  rcases rejected with ⟨rejectedOutput, rejected⟩
  exact rejected.disjointAllowEmptyTrailing outcomes (fun parsed => parsed)

/-- Optional ordinary call arguments have a unique output remainder. -/
theorem OptionalYulCallArgumentsOrdinaryParses.output_unique
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input : Remainder}
    {left right : Option (DelimitedList Syntax.YulExpr)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalYulCallArgumentsOrdinaryParses ordinaryParses
      nestedRejects input left afterLeft)
    (rightParsed : OptionalYulCallArgumentsOrdinaryParses ordinaryParses
      nestedRejects input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | absent leftOpeningAbsent =>
      cases rightParsed with
      | absent => rfl
      | rewound => rfl
      | present rightPresent =>
          rcases YulCallArgumentsParses.opening_present rightPresent with
            ⟨span, token⟩
          exact False.elim
            (absent_conflicts_token leftOpeningAbsent token)
  | rewound openingSpan openingToken leftRejected =>
      cases rightParsed with
      | absent => rfl
      | rewound => rfl
      | present rightPresent =>
          exact False.elim
            (leftRejected.disjointOrdinary outcomes
              ⟨_, _, rightPresent⟩)
  | present leftPresent =>
      cases rightParsed with
      | absent rightOpeningAbsent =>
          rcases YulCallArgumentsParses.opening_present leftPresent with
            ⟨span, token⟩
          exact False.elim
            (absent_conflicts_token rightOpeningAbsent token)
      | rewound openingSpan openingToken rightRejected =>
          exact False.elim
            (rightRejected.disjointOrdinary outcomes
              ⟨_, _, leftPresent⟩)
      | present rightPresent =>
          exact TrailingDelimitedListParses.output_unique
            (elementParses := ordinaryParses)
            outcomes.successOutputUnique leftPresent rightPresent

/-- Ordinary named-or-called expressions have functional output. -/
theorem YulNamedExpressionOrdinaryParses.output_unique
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input : Remainder} {left right : Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulNamedExpressionOrdinaryParses ordinaryParses
      nestedRejects input left afterLeft)
    (rightParsed : YulNamedExpressionOrdinaryParses ordinaryParses
      nestedRejects input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | identifier leftNameParsed leftArgumentsParsed =>
      cases rightParsed with
      | identifier rightNameParsed rightArgumentsParsed
      | call rightNameParsed rightArgumentsParsed =>
          have afterNameEq := leftNameParsed.output_unique rightNameParsed
          subst afterNameEq
          exact leftArgumentsParsed.output_unique outcomes
            rightArgumentsParsed
  | call leftNameParsed leftArgumentsParsed =>
      cases rightParsed with
      | identifier rightNameParsed rightArgumentsParsed
      | call rightNameParsed rightArgumentsParsed =>
          have afterNameEq := leftNameParsed.output_unique rightNameParsed
          subst afterNameEq
          exact leftArgumentsParsed.output_unique outcomes
            rightArgumentsParsed

/-- Every ordinary Yul name begins at the public name lookahead. -/
theorem YulNameOrdinaryParses.public_startsAt {input output : Remainder}
    {name : Syntax.YulIdentifier}
    (parsed : YulNameOrdinaryParses input name output) :
    YulNameStartsAt input := by
  cases parsed with
  | marked token => exact Or.inr (Or.inl ⟨_, _, token⟩)
  | underscore token => exact Or.inr (Or.inr (Or.inl ⟨_, token⟩))
  | fallbackKeyword token => exact Or.inr (Or.inr (Or.inr ⟨_, token⟩))
  | identifier parsed => exact Or.inl ⟨_, _, parsed.1⟩

/-- Every ordinary named expression begins at the public name lookahead. -/
theorem YulNamedExpressionOrdinaryParses.startsAt
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {input output : Remainder} {expression : Syntax.YulExpr}
    (parsed : YulNamedExpressionOrdinaryParses ordinaryParses nestedRejects
      input expression output) :
    YulNameStartsAt input := by
  cases parsed with
  | identifier nameParsed argumentsParsed
  | call nameParsed argumentsParsed => exact nameParsed.public_startsAt

/-- Every Yul literal exposes the literal lookahead used by the core parser. -/
theorem YulLiteralParses.startsAt {input output : Remainder}
    {literal : Syntax.YulLiteral}
    (parsed : YulLiteralParses input literal output) :
    YulLiteralStartsAt input := by
  cases parsed with
  | decimal token => exact Or.inl ⟨_, _, token⟩
  | hexadecimal token => exact Or.inr (Or.inl ⟨_, _, token⟩)
  | string token => exact Or.inr (Or.inr (Or.inl ⟨_, _, token⟩))
  | trueKeyword token =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, token⟩)))
  | falseKeyword token =>
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, token⟩)))

/-- Literal parsing always consumes exactly the current token. -/
theorem YulLiteralParses.output_unique {input : Remainder}
    {left right : Syntax.YulLiteral} {afterLeft afterRight : Remainder}
    (leftParsed : YulLiteralParses input left afterLeft)
    (rightParsed : YulLiteralParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed <;> cases rightParsed <;> rfl

/-- Ordinary core expressions have a unique output remainder. -/
theorem YulExpressionCoreOrdinaryParses.output_unique
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input : Remainder} {left right : Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulExpressionCoreOrdinaryParses ordinaryParses
      nestedRejects input left afterLeft)
    (rightParsed : YulExpressionCoreOrdinaryParses ordinaryParses
      nestedRejects input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | literal leftLiteral =>
      cases rightParsed with
      | literal rightLiteral => exact leftLiteral.output_unique rightLiteral
      | named rightLiteralAbsent rightNamed =>
          exact False.elim (rightLiteralAbsent leftLiteral.startsAt)
      | metaBacktick rightLiteralAbsent =>
          exact False.elim (rightLiteralAbsent leftLiteral.startsAt)
      | metaInterpolation rightLiteralAbsent =>
          exact False.elim (rightLiteralAbsent leftLiteral.startsAt)
  | named leftLiteralAbsent leftNamed =>
      cases rightParsed with
      | literal rightLiteral =>
          exact False.elim (leftLiteralAbsent rightLiteral.startsAt)
      | named rightLiteralAbsent rightNamed =>
          exact leftNamed.output_unique outcomes rightNamed
      | metaBacktick rightLiteralAbsent rightNameAbsent =>
          exact False.elim (rightNameAbsent leftNamed.startsAt)
      | metaInterpolation rightLiteralAbsent rightNameAbsent =>
          exact False.elim (rightNameAbsent leftNamed.startsAt)
  | metaBacktick leftLiteralAbsent leftNameAbsent leftToken =>
      cases rightParsed with
      | literal rightLiteral =>
          exact False.elim (leftLiteralAbsent rightLiteral.startsAt)
      | named rightLiteralAbsent rightNamed =>
          exact False.elim (leftNameAbsent rightNamed.startsAt)
      | metaBacktick | metaInterpolation => rfl
  | metaInterpolation leftLiteralAbsent leftNameAbsent leftToken =>
      cases rightParsed with
      | literal rightLiteral =>
          exact False.elim (leftLiteralAbsent rightLiteral.startsAt)
      | named rightLiteralAbsent rightNamed =>
          exact False.elim (leftNameAbsent rightNamed.startsAt)
      | metaBacktick | metaInterpolation => rfl

/-- Clean optional call arguments embed into exact ordinary outcomes. -/
theorem OptionalYulCallArgumentsParses.toOrdinary
    {ordinaryParses cleanParses :
      Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanParses input value output → ordinaryParses input value output)
    {input output : Remainder}
    {arguments : Option (DelimitedList Syntax.YulExpr)}
    (parsed : OptionalYulCallArgumentsParses cleanParses
      (YulCallArgumentsFallbackSpec.ofOutcomes ordinaryParses cleanParses
        nestedRejects outcomes cleanToOrdinary)
      input arguments output) :
    OptionalYulCallArgumentsOrdinaryParses ordinaryParses nestedRejects
      input arguments output := by
  cases parsed with
  | absent openingAbsent => exact .absent openingAbsent
  | rewound openingSpan openingToken attemptRejected =>
      exact .rewound openingSpan openingToken attemptRejected
  | present parsed =>
      exact .present (parsed.mapElementRelation cleanToOrdinary)

/-- Clean named expressions embed into ordinary named expressions. -/
theorem YulNamedExpressionParses.toOrdinary
    {ordinaryParses cleanParses :
      Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanParses input value output → ordinaryParses input value output)
    {input output : Remainder} {expression : Syntax.YulExpr}
    (parsed : YulNamedExpressionParses cleanParses
      (YulCallArgumentsFallbackSpec.ofOutcomes ordinaryParses cleanParses
        nestedRejects outcomes cleanToOrdinary)
      input expression output) :
    YulNamedExpressionOrdinaryParses ordinaryParses nestedRejects input
      expression output := by
  cases parsed with
  | identifier nameParsed argumentsParsed =>
      exact .identifier nameParsed.toOrdinary
        (argumentsParsed.toOrdinary outcomes cleanToOrdinary)
  | call nameParsed argumentsParsed =>
      exact .call nameParsed.toOrdinary
        (argumentsParsed.toOrdinary outcomes cleanToOrdinary)

/-- Clean core expressions embed into ordinary core outcomes. -/
theorem YulExpressionCoreParses.toOrdinary
    {ordinaryParses cleanParses :
      Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanParses input value output → ordinaryParses input value output)
    {input output : Remainder} {expression : Syntax.YulExpr}
    (parsed : YulExpressionCoreParses cleanParses
      (YulCallArgumentsFallbackSpec.ofOutcomes ordinaryParses cleanParses
        nestedRejects outcomes cleanToOrdinary)
      input expression output) :
    YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects input
      expression output := by
  cases parsed with
  | literal parsed => exact .literal parsed
  | named literalAbsent parsed =>
      exact .named literalAbsent
        (parsed.toOrdinary outcomes cleanToOrdinary)

end Solcore.Syntax.DeclarativeGrammar
