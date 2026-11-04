import Solcore.Syntax.Internal.DelimitedExactness
import Solcore.Syntax.Grammar.Yul
import Solcore.Syntax.Internal.DelimitedOutcomes
import Solcore.Syntax.Internal.YulBlockOutcomes
import Solcore.Syntax.Grammar.Basics

/-!
Yul expressions at fuel, and the ordinary statements built on them.

The definitions rest on outcome lemmas, so those lemmas stay in this file. Main
declarations: `YulExpressionLevel`, `YulExpressionOrdinaryParsesWithFuel`,
`YulExpressionOrdinaryParses`, `YulAssignmentOrdinaryParses`,
`YulIfStatementOrdinaryParses`,
`YulForStatementOrdinaryParses`.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulExpressionOrdinaryGrammar
/-!
Parser-independent ordinary-success grammar for inline-Yul expressions.

Unlike the diagnostic-free grammar, this layer retains diagnosed Yul names,
forbidden source meta syntax, and recovered error expressions.  Transactional
call-argument rejection is recorded before the parser rewinds to `none`.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary outcomes of optional transactional Yul call arguments. -/
inductive OptionalYulCallArgumentsOrdinaryParses
    (ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Option (DelimitedList Syntax.YulExpr) → Remainder →
      Prop where
  | absent {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen)) :
      OptionalYulCallArgumentsOrdinaryParses ordinaryParses nestedRejects
        input none input
  | rewound {input : Remainder} (openingSpan : SourceSpan)
      (openingToken : TokenAt input.tokens input.endIndex input.cursor {
        span := openingSpan
        value := .symbol .leftParen
      })
      (attemptRejected : YulCallArgumentsRejects ordinaryParses nestedRejects
        input) :
      OptionalYulCallArgumentsOrdinaryParses ordinaryParses nestedRejects
        input none input
  | present {input output : Remainder}
      {arguments : DelimitedList Syntax.YulExpr}
      (parsed : TrailingDelimitedListParses .leftParen .rightParen
        ordinaryParses input arguments output) :
      OptionalYulCallArgumentsOrdinaryParses ordinaryParses nestedRejects
        input (some arguments) output

/-- Ordinary named-or-called inline-Yul expression grammar. -/
inductive YulNamedExpressionOrdinaryParses
    (ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.YulExpr → Remainder → Prop where
  | identifier {input afterName output : Remainder}
      {name : Syntax.YulIdentifier}
      (nameParsed : YulNameOrdinaryParses input name afterName)
      (argumentsParsed : OptionalYulCallArgumentsOrdinaryParses
        ordinaryParses nestedRejects afterName none output) :
      YulNamedExpressionOrdinaryParses ordinaryParses nestedRejects input {
        span := name.span
        value := .identifier name
      } output
  | call {input afterName output : Remainder}
      {name : Syntax.YulIdentifier}
      {arguments : DelimitedList Syntax.YulExpr}
      (nameParsed : YulNameOrdinaryParses input name afterName)
      (argumentsParsed : OptionalYulCallArgumentsOrdinaryParses
        ordinaryParses nestedRejects afterName (some arguments) output) :
      YulNamedExpressionOrdinaryParses ordinaryParses nestedRejects input {
        span := SourceSpan.cover name.span arguments.span
        value := .call name arguments
      } output

/-- Forbidden source-level Yul meta-token presence. -/
def YulMetaStartsAt (input : Remainder) : Prop :=
  (∃ span text, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .yulMetaBacktick text
  }) ∨
  ∃ span text, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .yulMetaInterpolation text
  }

/-- Exact ordinary outcomes of the literal-before-name core parser. -/
inductive YulExpressionCoreOrdinaryParses
    (ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.YulExpr → Remainder → Prop where
  | literal {input output : Remainder} {literal : Syntax.YulLiteral}
      (parsed : YulLiteralParses input literal output) :
      YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects input {
        span := literal.span
        value := .literal literal
      } output
  | named {input output : Remainder} {expression : Syntax.YulExpr}
      (literalAbsent : ¬ YulLiteralStartsAt input)
      (parsed : YulNamedExpressionOrdinaryParses ordinaryParses nestedRejects
        input expression output) :
      YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects input
        expression output
  | metaBacktick {input : Remainder} {span : SourceSpan} {text : String}
      (literalAbsent : ¬ YulLiteralStartsAt input)
      (nameAbsent : ¬ YulNameStartsAt input)
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .yulMetaBacktick text
      }) :
      YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects input {
        span
        value := .error
      } { input with cursor := input.cursor + 1 }
  | metaInterpolation {input : Remainder} {span : SourceSpan} {text : String}
      (literalAbsent : ¬ YulLiteralStartsAt input)
      (nameAbsent : ¬ YulNameStartsAt input)
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .yulMetaInterpolation text
      }) :
      YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects input {
        span
        value := .error
      } { input with cursor := input.cursor + 1 }

/-- Exact evidence that the final core `rejectAt` branch was selected. -/
inductive YulExpressionCoreFinalRejects : Remainder → Prop where
  | final {input : Remainder}
      (literalAbsent : ¬ YulLiteralStartsAt input)
      (nameAbsent : ¬ YulNameStartsAt input)
      (metaAbsent : ¬ YulMetaStartsAt input) :
      YulExpressionCoreFinalRejects input

/-- Exact scan performed after recovery has consumed its first token. -/
inductive YulExpressionRecoveryScanParses (first : SourceSpan) :
    SourceSpan → Remainder → Syntax.YulExpr → Remainder → Prop where
  | stop {last : SourceSpan} {input : Remainder}
      (stops : YulExpressionRejects input input) :
      YulExpressionRecoveryScanParses first last input {
        span := SourceSpan.cover first last
        value := .error
      } input
  | next {last : SourceSpan} {input output : Remainder} {token : Token}
      {expression : Syntax.YulExpr}
      (continues : ¬ YulExpressionRejects input input)
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (tail : YulExpressionRecoveryScanParses first token.span
        { input with cursor := input.cursor + 1 } expression output) :
      YulExpressionRecoveryScanParses first last input expression output

/-- Ordinary outcomes of one recovering inline-Yul expression layer. -/
inductive YulExpressionLayerOrdinaryParses
    (ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.YulExpr → Remainder → Prop where
  | core {input output : Remainder} {expression : Syntax.YulExpr}
      (parsed : YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects
        input expression output) :
      YulExpressionLayerOrdinaryParses ordinaryParses nestedRejects input
        expression output
  | recovered {input output : Remainder} {token : Token}
      {expression : Syntax.YulExpr}
      (coreRejected : YulExpressionCoreFinalRejects input)
      (continues : ¬ YulExpressionRejects input input)
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (scan : YulExpressionRecoveryScanParses token.span token.span
        { input with cursor := input.cursor + 1 } expression output) :
      YulExpressionLayerOrdinaryParses ordinaryParses nestedRejects input
        expression output

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulExpressionOrdinaryCoreProperties
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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulExpressionOrdinaryOutcomeProperties
/-!
Functionality, rejection exclusivity, and the deterministic outcome contract
for recovering ordinary inline-Yul expressions.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem tokenAt_unique {tokens : Array Token} {endIndex index : Nat}
    {left right : Token} (leftAt : TokenAt tokens endIndex index left)
    (rightAt : TokenAt tokens endIndex index right) : left = right := by
  exact Option.some.inj (leftAt.2.symm.trans rightAt.2)

private def tokenKindStartsOrdinaryYulExpression : TokenKind → Bool
  | .decimalLiteral _
  | .hexadecimalLiteral _
  | .stringLiteral _
  | .keyword .trueKw
  | .keyword .falseKw
  | .identifier _
  | .yulIdentifier _
  | .symbol .underscore
  | .keyword .fallbackKw
  | .yulMetaBacktick _
  | .yulMetaInterpolation _ => true
  | _ => false

/-- Every ordinary core success exposes a classified current token. -/
private theorem YulExpressionCoreOrdinaryParses.current_token
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {input output : Remainder} {expression : Syntax.YulExpr}
    (parsed : YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects
      input expression output) :
    ∃ token,
      TokenAt input.tokens input.endIndex input.cursor token ∧
        tokenKindStartsOrdinaryYulExpression token.value = true := by
  cases parsed with
  | literal parsed =>
      cases parsed with
      | decimal token
      | hexadecimal token
      | string token
      | trueKeyword token
      | falseKeyword token => exact ⟨_, token, rfl⟩
  | named literalAbsent parsed =>
      cases parsed with
      | identifier nameParsed argumentsParsed
      | call nameParsed argumentsParsed =>
          cases nameParsed with
          | marked token
          | underscore token
          | fallbackKeyword token => exact ⟨_, token, rfl⟩
          | identifier parsed => exact ⟨_, parsed.1, rfl⟩
  | metaBacktick literalAbsent nameAbsent token => exact ⟨_, token, rfl⟩
  | metaInterpolation literalAbsent nameAbsent token =>
      exact ⟨_, token, rfl⟩

/-- The final core rejection guard excludes every ordinary core success. -/
theorem YulExpressionCoreFinalRejects.disjointOrdinary
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {input : Remainder} (rejected : YulExpressionCoreFinalRejects input) :
    ¬ ∃ expression output,
      YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects input
        expression output := by
  rintro ⟨expression, output, parsed⟩
  cases rejected with
  | final literalAbsent nameAbsent metaAbsent =>
      cases parsed with
      | literal parsed => exact literalAbsent parsed.startsAt
      | named otherLiteralAbsent parsed => exact nameAbsent parsed.startsAt
      | metaBacktick otherLiteralAbsent otherNameAbsent token =>
          exact metaAbsent (Or.inl ⟨_, _, token⟩)
      | metaInterpolation otherLiteralAbsent otherNameAbsent token =>
          exact metaAbsent (Or.inr ⟨_, _, token⟩)

/-- A recovery scan has functional output from a fixed current remainder. -/
theorem YulExpressionRecoveryScanParses.output_unique :
    ∀ {first leftLast rightLast : SourceSpan} {input : Remainder}
      {left right : Syntax.YulExpr} {afterLeft afterRight : Remainder},
      YulExpressionRecoveryScanParses first leftLast input left afterLeft →
      YulExpressionRecoveryScanParses first rightLast input right afterRight →
      afterLeft = afterRight := by
  intro first leftLast rightLast input left right afterLeft afterRight
    leftParsed
  induction leftParsed generalizing rightLast right afterRight with
  | stop leftStops =>
      intro rightParsed
      cases rightParsed with
      | stop => rfl
      | next rightContinues rightCurrent rightTail =>
          exact False.elim (rightContinues leftStops)
  | next leftContinues leftCurrent leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | stop rightStops => exact False.elim (leftContinues rightStops)
      | next rightContinues rightCurrent rightTail =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact inductionHypothesis rightTail

/-- One ordinary recovering expression layer has functional output. -/
theorem YulExpressionLayerOrdinaryParses.output_unique
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input : Remainder} {left right : Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulExpressionLayerOrdinaryParses ordinaryParses
      nestedRejects input left afterLeft)
    (rightParsed : YulExpressionLayerOrdinaryParses ordinaryParses
      nestedRejects input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore => exact leftCore.output_unique outcomes rightCore
      | recovered rightRejected rightContinues rightCurrent rightScan =>
          exact False.elim
            (rightRejected.disjointOrdinary ⟨_, _, leftCore⟩)
  | recovered leftRejected leftContinues leftCurrent leftScan =>
      cases rightParsed with
      | core rightCore =>
          exact False.elim
            (leftRejected.disjointOrdinary ⟨_, _, rightCore⟩)
      | recovered rightRejected rightContinues rightCurrent rightScan =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact leftScan.output_unique rightScan

/-- Inline-Yul expression rejection is non-consuming. -/
theorem YulExpressionRejects.output_eq {input rejected : Remainder}
    (rejection : YulExpressionRejects input rejected) : rejected = input := by
  cases rejection <;> rfl

/-- Binary expression rejection excludes every ordinary core success. -/
theorem YulExpressionRejects.disjointCoreOrdinary
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : YulExpressionRejects input rejected) :
    ¬ ∃ expression output,
      YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects input
        expression output := by
  rintro ⟨expression, output, parsed⟩
  rcases parsed.current_token with ⟨current, currentAt, starts⟩
  cases rejection with
  | windowEnd atEnd => exact (Nat.not_lt_of_ge atEnd) currentAt.1
  | comma boundaryAt
  | rightParen boundaryAt
  | rightBrace boundaryAt =>
      have tokenEq := tokenAt_unique boundaryAt currentAt
      have kindEq := congrArg (fun token : Token => token.value) tokenEq
      rw [← kindEq] at starts
      simp [tokenKindStartsOrdinaryYulExpression] at starts
  | missingToken inside missing =>
      have found := currentAt.2
      rw [missing] at found
      contradiction

/-- Binary expression rejection excludes ordinary recovering-layer success. -/
theorem YulExpressionRejects.disjointLayerOrdinary
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : YulExpressionRejects input rejected) :
    ¬ ∃ expression output,
      YulExpressionLayerOrdinaryParses ordinaryParses nestedRejects input
        expression output := by
  rintro ⟨expression, output, parsed⟩
  cases parsed with
  | core parsed =>
      exact rejection.disjointCoreOrdinary ⟨_, _, parsed⟩
  | recovered coreRejected continues current scan =>
      have rejectedEq := rejection.output_eq
      subst rejected
      exact continues rejection

/-- A clean core expression is also a success of the ordinary recovery layer. -/
theorem YulExpressionCoreParses.toOrdinaryLayer
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
    YulExpressionLayerOrdinaryParses ordinaryParses nestedRejects input
      expression output :=
  .core (parsed.toOrdinary outcomes cleanToOrdinary)

/-- Construct the deterministic ordinary outcome contract for one recovering
inline-Yul expression layer. -/
theorem yulExpressionDeterministicOutcomeSpec
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects) :
    DeterministicOutcomeSpec
      (YulExpressionLayerOrdinaryParses ordinaryParses nestedRejects)
      YulExpressionRejects where
  successOutputUnique :=
    YulExpressionLayerOrdinaryParses.output_unique outcomes
  successRejectDisjoint := YulExpressionRejects.disjointLayerOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulExpressionFuelGrammar
/-!
Parser-independent fuel-indexed outcomes for recursive inline-Yul expressions.

Each level packages its clean grammar, its broader ordinary-success grammar,
its exact rejection relation, and the laws needed to construct the next level.
This avoids a recursive inductive definition containing proof-bearing fallback
specifications in a negative position.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One complete declarative approximation of recursive Yul expressions. -/
structure YulExpressionLevel where
  cleanParses : Remainder → Syntax.YulExpr → Remainder → Prop
  ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop
  rejects : Remainder → Remainder → Prop
  outcomes : DeterministicOutcomeSpec ordinaryParses rejects
  cleanToOrdinary : ∀ {input expression output},
    cleanParses input expression output →
      ordinaryParses input expression output

namespace YulExpressionLevel

/-- Fuel zero recognizes no success or rejection outcome. -/
def empty : YulExpressionLevel where
  cleanParses := fun _ _ _ => False
  ordinaryParses := fun _ _ _ => False
  rejects := fun _ _ => False
  outcomes := {
    successOutputUnique := by
      intro input left right afterLeft afterRight leftParsed
      exact False.elim leftParsed
    successRejectDisjoint := by
      intro input rejected rejection
      exact False.elim rejection
  }
  cleanToOrdinary := by
    intro input expression output parsed
    exact False.elim parsed

/-- Transactional call-argument fallback induced by one previous level. -/
def callArgumentsFallback (level : YulExpressionLevel) :
    YulCallArgumentsFallbackSpec level.cleanParses :=
  YulCallArgumentsFallbackSpec.ofOutcomes level.ordinaryParses
    level.cleanParses level.rejects level.outcomes level.cleanToOrdinary

/-- Add one recursive Yul-expression layer. -/
def next (previous : YulExpressionLevel) : YulExpressionLevel where
  cleanParses := YulExpressionCoreParses previous.cleanParses
    previous.callArgumentsFallback
  ordinaryParses := YulExpressionLayerOrdinaryParses
    previous.ordinaryParses previous.rejects
  rejects := YulExpressionRejects
  outcomes := yulExpressionDeterministicOutcomeSpec previous.outcomes
  cleanToOrdinary := by
    intro input expression output parsed
    exact parsed.toOrdinaryLayer previous.outcomes previous.cleanToOrdinary

end YulExpressionLevel

/-- Declarative recursive Yul-expression outcomes at exactly `fuel`. -/
def yulExpressionLevel : Nat → YulExpressionLevel
  | 0 => .empty
  | fuel + 1 => (yulExpressionLevel fuel).next

/-- Diagnostic-free recursive Yul-expression successes at one fuel. -/
def YulExpressionCleanParsesWithFuel (fuel : Nat) :
    Remainder → Syntax.YulExpr → Remainder → Prop :=
  (yulExpressionLevel fuel).cleanParses

/-- Ordinary recursive Yul-expression successes at one fuel. -/
def YulExpressionOrdinaryParsesWithFuel (fuel : Nat) :
    Remainder → Syntax.YulExpr → Remainder → Prop :=
  (yulExpressionLevel fuel).ordinaryParses

/-- Exact recursive Yul-expression rejection at one fuel. -/
def YulExpressionRejectsWithFuel (fuel : Nat) :
    Remainder → Remainder → Prop :=
  (yulExpressionLevel fuel).rejects

/-- Deterministic outcome laws at one recursive fuel. -/
theorem yulExpressionOutcomeSpecWithFuel (fuel : Nat) :
    DeterministicOutcomeSpec
      (YulExpressionOrdinaryParsesWithFuel fuel)
      (YulExpressionRejectsWithFuel fuel) :=
  (yulExpressionLevel fuel).outcomes

/-- Clean successes at a fuel are ordinary successes at that fuel. -/
theorem YulExpressionCleanParsesWithFuel.toOrdinary {fuel : Nat}
    {input output : Remainder} {expression : Syntax.YulExpr}
    (parsed : YulExpressionCleanParsesWithFuel fuel input expression
      output) :
    YulExpressionOrdinaryParsesWithFuel fuel input expression output :=
  (yulExpressionLevel fuel).cleanToOrdinary parsed

/-- Call-argument fallback selected by the preceding recursive level. -/
def yulExpressionCallArgumentsFallbackWithFuel (fuel : Nat) :
    YulCallArgumentsFallbackSpec
      (YulExpressionCleanParsesWithFuel fuel) :=
  (yulExpressionLevel fuel).callArgumentsFallback

@[simp] theorem YulExpressionCleanParsesWithFuel.zero
    {input output : Remainder} {expression : Syntax.YulExpr} :
    ¬ YulExpressionCleanParsesWithFuel 0 input expression output := by
  simp [YulExpressionCleanParsesWithFuel, yulExpressionLevel,
    YulExpressionLevel.empty]

@[simp] theorem YulExpressionOrdinaryParsesWithFuel.zero
    {input output : Remainder} {expression : Syntax.YulExpr} :
    ¬ YulExpressionOrdinaryParsesWithFuel 0 input expression output := by
  simp [YulExpressionOrdinaryParsesWithFuel, yulExpressionLevel,
    YulExpressionLevel.empty]

@[simp] theorem YulExpressionRejectsWithFuel.zero
    {input rejected : Remainder} :
    ¬ YulExpressionRejectsWithFuel 0 input rejected := by
  simp [YulExpressionRejectsWithFuel, yulExpressionLevel,
    YulExpressionLevel.empty]

@[simp] theorem YulExpressionCleanParsesWithFuel.succ_iff
    {fuel : Nat} {input output : Remainder}
    {expression : Syntax.YulExpr} :
    YulExpressionCleanParsesWithFuel (fuel + 1) input expression output ↔
      YulExpressionCoreParses (YulExpressionCleanParsesWithFuel fuel)
        (yulExpressionCallArgumentsFallbackWithFuel fuel)
        input expression output := by
  simp only [YulExpressionCleanParsesWithFuel, yulExpressionLevel,
    YulExpressionLevel.next, yulExpressionCallArgumentsFallbackWithFuel]

@[simp] theorem YulExpressionOrdinaryParsesWithFuel.succ_iff
    {fuel : Nat} {input output : Remainder}
    {expression : Syntax.YulExpr} :
    YulExpressionOrdinaryParsesWithFuel (fuel + 1) input expression output ↔
      YulExpressionLayerOrdinaryParses
        (YulExpressionOrdinaryParsesWithFuel fuel)
        (YulExpressionRejectsWithFuel fuel) input expression output := by
  simp only [YulExpressionOrdinaryParsesWithFuel,
    YulExpressionRejectsWithFuel, yulExpressionLevel,
    YulExpressionLevel.next]

@[simp] theorem YulExpressionRejectsWithFuel.succ_iff
    {fuel : Nat} {input rejected : Remainder} :
    YulExpressionRejectsWithFuel (fuel + 1) input rejected ↔
      YulExpressionRejects input rejected := by
  simp only [YulExpressionRejectsWithFuel, yulExpressionLevel,
    YulExpressionLevel.next]

/-- Fuel chosen by the public parser from a parser-independent remainder. -/
def yulExpressionPublicFuel (input : Remainder) : Nat :=
  input.endIndex - input.cursor + 1

/-- Public diagnostic-free recursive inline-Yul expression grammar. -/
def YulExpressionParses (input : Remainder) (expression : Syntax.YulExpr)
    (output : Remainder) : Prop :=
  YulExpressionCleanParsesWithFuel (yulExpressionPublicFuel input)
    input expression output

/-- Public ordinary-success recursive inline-Yul expression grammar. -/
def YulExpressionOrdinaryParses (input : Remainder)
    (expression : Syntax.YulExpr) (output : Remainder) : Prop :=
  YulExpressionOrdinaryParsesWithFuel (yulExpressionPublicFuel input)
    input expression output

/-- Public fuel-indexed rejection, definitionally the boundary rejection. -/
def YulExpressionPublicRejects (input rejected : Remainder) : Prop :=
  YulExpressionRejectsWithFuel (yulExpressionPublicFuel input) input rejected

@[simp] theorem yulExpressionPublicRejects_iff
    {input rejected : Remainder} :
    YulExpressionPublicRejects input rejected ↔
      YulExpressionRejects input rejected := by
  simp only [YulExpressionPublicRejects, yulExpressionPublicFuel,
    YulExpressionRejectsWithFuel, yulExpressionLevel,
    YulExpressionLevel.next]

/-- Deterministic ordinary outcomes of the public recursive grammar. -/
theorem yulExpressionPublicOutcomeSpec :
    DeterministicOutcomeSpec YulExpressionOrdinaryParses
      YulExpressionPublicRejects where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact (yulExpressionOutcomeSpecWithFuel
      (yulExpressionPublicFuel input)).successOutputUnique
        leftParsed rightParsed
  successRejectDisjoint := by
    intro input rejected rejection
    exact (yulExpressionOutcomeSpecWithFuel
      (yulExpressionPublicFuel input)).successRejectDisjoint rejection

/-- The public outcome contract stated with the concrete expression rejection
relation used by transactional consumers. -/
theorem yulExpressionPublicDeterministicOutcomeSpec :
    DeterministicOutcomeSpec YulExpressionOrdinaryParses
      YulExpressionRejects where
  successOutputUnique :=
    yulExpressionPublicOutcomeSpec.successOutputUnique
  successRejectDisjoint := by
    intro input rejected rejection
    exact yulExpressionPublicOutcomeSpec.successRejectDisjoint
      (yulExpressionPublicRejects_iff.mpr rejection)

/-- Public clean recursive expressions are public ordinary successes. -/
theorem YulExpressionParses.toOrdinary {input output : Remainder}
    {expression : Syntax.YulExpr} (parsed : YulExpressionParses input
      expression output) :
    YulExpressionOrdinaryParses input expression output :=
  YulExpressionCleanParsesWithFuel.toOrdinary parsed

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulStatementControlOutcomeGrammar
/-!
Parser-independent ordinary successes and exact rejection traces for inline-
Yul `if` and `for` primaries.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary `if` success reuses the exact control grammar with ordinary
recursive statement and public expression relations. -/
abbrev YulIfStatementOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop) :=
  YulIfStatementParses statementOrdinary YulExpressionOrdinaryParses

/-- Exact rejection stage of an inline-Yul `if` primary. -/
inductive YulIfStatementRejects
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .ifKw)) :
      YulIfStatementRejects statementOrdinary statementRejects input input
  | conditionRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .ifKw) input markerSpan
        afterMarker)
      (conditionRejected : YulExpressionRejects afterMarker rejected) :
      YulIfStatementRejects statementOrdinary statementRejects input rejected
  | bodyRejected {input afterMarker afterCondition rejected : Remainder}
      {condition : Syntax.YulExpr} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .ifKw) input markerSpan
        afterMarker)
      (conditionParsed : YulExpressionOrdinaryParses afterMarker condition
        afterCondition)
      (bodyRejected : YulBlockRejects statementOrdinary statementRejects
        afterCondition rejected) :
      YulIfStatementRejects statementOrdinary statementRejects input rejected

/-- Ordinary `for` success reuses the exact control grammar with ordinary
recursive statement and public expression relations. -/
abbrev YulForStatementOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop) :=
  YulForStatementParses statementOrdinary YulExpressionOrdinaryParses

/-- Exact rejection stage of an inline-Yul `for` primary. -/
inductive YulForStatementRejects
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .forKw)) :
      YulForStatementRejects statementOrdinary statementRejects input input
  | initializerRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (initializerRejected : YulBlockRejects statementOrdinary
        statementRejects afterMarker rejected) :
      YulForStatementRejects statementOrdinary statementRejects input rejected
  | conditionRejected
      {input afterMarker afterInitializer rejected : Remainder}
      {initializerSpan : SourceSpan}
      {initializer : List Syntax.YulStmt} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (initializerParsed : YulBlockOrdinaryParses statementOrdinary afterMarker
        initializerSpan initializer afterInitializer)
      (conditionRejected : YulExpressionRejects afterInitializer rejected) :
      YulForStatementRejects statementOrdinary statementRejects input rejected
  | postRejected
      {input afterMarker afterInitializer afterCondition rejected : Remainder}
      {initializerSpan : SourceSpan}
      {initializer : List Syntax.YulStmt} {condition : Syntax.YulExpr}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (initializerParsed : YulBlockOrdinaryParses statementOrdinary afterMarker
        initializerSpan initializer afterInitializer)
      (conditionParsed : YulExpressionOrdinaryParses afterInitializer condition
        afterCondition)
      (postRejected : YulBlockRejects statementOrdinary statementRejects
        afterCondition rejected) :
      YulForStatementRejects statementOrdinary statementRejects input rejected
  | bodyRejected
      {input afterMarker afterInitializer afterCondition afterPost rejected :
        Remainder}
      {initializerSpan postSpan : SourceSpan}
      {initializer post : List Syntax.YulStmt} {condition : Syntax.YulExpr}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (initializerParsed : YulBlockOrdinaryParses statementOrdinary afterMarker
        initializerSpan initializer afterInitializer)
      (conditionParsed : YulExpressionOrdinaryParses afterInitializer condition
        afterCondition)
      (postParsed : YulBlockOrdinaryParses statementOrdinary afterCondition
        postSpan post afterPost)
      (bodyRejected : YulBlockRejects statementOrdinary statementRejects
        afterPost rejected) :
      YulForStatementRejects statementOrdinary statementRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulAssignmentOrdinaryGrammar
/-!
Parser-independent ordinary-success grammar for public inline-Yul assignment.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact ordinary assignment success, retaining diagnosed names and ordinary
recursive expression success while preserving forward name order and AST
spans. -/
inductive YulAssignmentOrdinaryParses :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input afterNames afterOperator output : Remainder}
      {names : YulNamesOrdinaryValue} {value : Syntax.YulExpr}
      (operatorSpan : SourceSpan)
      (namesParsed : YulNamesOrdinaryParses input names afterNames)
      (operatorParsed : ExactTokenParses (.symbol .colonEqual) afterNames
        operatorSpan afterOperator)
      (valueParsed : YulExpressionOrdinaryParses afterOperator value output) :
      YulAssignmentOrdinaryParses input {
        span := SourceSpan.cover names.span value.span
        value := .assign names.names value
      } output

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulSwitchOutcomeGrammar
/-!
Parser-independent ordinary successes and exact rejection traces for inline-
Yul switch arms, case lists, optional defaults, and complete switches.

The executable empty-case branch is an ordinary diagnosed `.error` success,
not a rejection.  Its span and final remainder are retained exactly.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary case-arm success uses ordinary recursive statements. -/
abbrev YulCaseArmOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop) :=
  YulCaseArmParses statementOrdinary

/-- Exact sequential rejection stage of one `case` arm. -/
inductive YulCaseArmRejects
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .caseKw)) :
      YulCaseArmRejects statementOrdinary statementRejects input input
  | literalMissing {input afterMarker : Remainder} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .caseKw) input markerSpan
        afterMarker)
      (literalAbsent : ¬ YulLiteralStartsAt afterMarker) :
      YulCaseArmRejects statementOrdinary statementRejects input afterMarker
  | bodyRejected {input afterMarker afterLiteral rejected : Remainder}
      {literal : Syntax.YulLiteral} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .caseKw) input markerSpan
        afterMarker)
      (literalParsed : YulLiteralParses afterMarker literal afterLiteral)
      (bodyRejected : YulBlockRejects statementOrdinary statementRejects
        afterLiteral rejected) :
      YulCaseArmRejects statementOrdinary statementRejects input rejected

/-- Ordinary case-list success is the existing forward maximal list grammar. -/
abbrev YulCaseListOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop) :=
  YulCaseListParses statementOrdinary

/-- Exact rejection in a case-list iteration.

`firstRejected` records the loop guard separately.  This rules out the
standalone arm relation's marker-missing branch at a guarded iteration.
-/
inductive YulCaseListRejects
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | firstRejected {input rejected : Remainder}
      (casePresent : ∃ span, TokenAt input.tokens input.endIndex input.cursor
        { span, value := .keyword .caseKw })
      (armRejected : YulCaseArmRejects statementOrdinary statementRejects
        input rejected) :
      YulCaseListRejects statementOrdinary statementRejects input rejected
  | laterRejected {input afterArm rejected : Remainder}
      {arm : Syntax.YulCase}
      (armParsed : YulCaseArmOrdinaryParses statementOrdinary input arm
        afterArm)
      (progress : input.cursor < afterArm.cursor)
      (tailRejected : YulCaseListRejects statementOrdinary statementRejects
        afterArm rejected) :
      YulCaseListRejects statementOrdinary statementRejects input rejected

/-- Ordinary optional-default success uses ordinary recursive statements. -/
abbrev OptionalYulDefaultOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop) :=
  OptionalYulDefaultParses statementOrdinary

/-- The guarded optional default can reject only in its braced body. -/
inductive OptionalYulDefaultRejects
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | bodyRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .defaultKw) input markerSpan
        afterMarker)
      (bodyRejected : YulBlockRejects statementOrdinary statementRejects
        afterMarker rejected) :
      OptionalYulDefaultRejects statementOrdinary statementRejects input
        rejected

/-- Every ordinary complete-switch success, including the diagnosed empty-
case `.error` result. -/
inductive YulSwitchStatementOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | nonempty {input afterMarker afterScrutinee afterCases output : Remainder}
      {scrutinee : Syntax.YulExpr} {head : Syntax.YulCase}
      {tail : List Syntax.YulCase} {defaultSpan : Option SourceSpan}
      {defaultBody : Option (List Syntax.YulStmt)} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .switchKw) input markerSpan
        afterMarker)
      (scrutineeParsed : YulExpressionOrdinaryParses afterMarker scrutinee
        afterScrutinee)
      (casesParsed : YulCaseListOrdinaryParses statementOrdinary
        afterScrutinee (head :: tail) afterCases)
      (defaultParsed : OptionalYulDefaultOrdinaryParses statementOrdinary
        afterCases defaultSpan defaultBody output) :
      YulSwitchStatementOrdinaryParses statementOrdinary input {
        span := SourceSpan.cover markerSpan
          (yulSwitchEnd scrutinee.span (head :: tail) defaultSpan)
        value := .switch scrutinee { head, tail } defaultBody
      } output
  | empty {input afterMarker afterScrutinee afterCases output : Remainder}
      {scrutinee : Syntax.YulExpr} {defaultSpan : Option SourceSpan}
      {defaultBody : Option (List Syntax.YulStmt)} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .switchKw) input markerSpan
        afterMarker)
      (scrutineeParsed : YulExpressionOrdinaryParses afterMarker scrutinee
        afterScrutinee)
      (casesParsed : YulCaseListOrdinaryParses statementOrdinary
        afterScrutinee [] afterCases)
      (defaultParsed : OptionalYulDefaultOrdinaryParses statementOrdinary
        afterCases defaultSpan defaultBody output) :
      YulSwitchStatementOrdinaryParses statementOrdinary input {
        span := SourceSpan.cover markerSpan
          (yulSwitchEnd scrutinee.span [] defaultSpan)
        value := .error
      } output

/-- Exact sequential rejection stage of a complete switch. -/
inductive YulSwitchStatementRejects
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .switchKw)) :
      YulSwitchStatementRejects statementOrdinary statementRejects input input
  | scrutineeRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .switchKw) input markerSpan
        afterMarker)
      (scrutineeRejected : YulExpressionRejects afterMarker rejected) :
      YulSwitchStatementRejects statementOrdinary statementRejects input
        rejected
  | casesRejected {input afterMarker afterScrutinee rejected : Remainder}
      {scrutinee : Syntax.YulExpr} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .switchKw) input markerSpan
        afterMarker)
      (scrutineeParsed : YulExpressionOrdinaryParses afterMarker scrutinee
        afterScrutinee)
      (casesRejected : YulCaseListRejects statementOrdinary statementRejects
        afterScrutinee rejected) :
      YulSwitchStatementRejects statementOrdinary statementRejects input
        rejected
  | defaultRejected
      {input afterMarker afterScrutinee afterCases rejected : Remainder}
      {scrutinee : Syntax.YulExpr} {cases : List Syntax.YulCase}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .switchKw) input markerSpan
        afterMarker)
      (scrutineeParsed : YulExpressionOrdinaryParses afterMarker scrutinee
        afterScrutinee)
      (casesParsed : YulCaseListOrdinaryParses statementOrdinary
        afterScrutinee cases afterCases)
      (defaultRejected : OptionalYulDefaultRejects statementOrdinary
        statementRejects afterCases rejected) :
      YulSwitchStatementRejects statementOrdinary statementRejects input
        rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulLetOrdinaryGrammar
/-!
Parser-independent ordinary success and exact rejection for public inline-Yul
`let` declarations.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary optional initializer success with exact `:=` priority. -/
inductive YulLetInitializerOrdinaryParses :
    Remainder → Option Syntax.YulExpr → Remainder → Prop where
  | absent {input : Remainder}
      (operatorAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .colonEqual)) :
      YulLetInitializerOrdinaryParses input none input
  | present {input afterOperator output : Remainder}
      {value : Syntax.YulExpr} (operatorSpan : SourceSpan)
      (operatorParsed : ExactTokenParses (.symbol .colonEqual) input
        operatorSpan afterOperator)
      (valueParsed : YulExpressionOrdinaryParses afterOperator value output) :
      YulLetInitializerOrdinaryParses input (some value) output

/-- An optional initializer rejects only after a present `:=` when its public
expression rejects.  The rejected remainder is retained exactly. -/
inductive YulLetInitializerRejects : Remainder → Remainder → Prop where
  | expressionRejected
      {input afterOperator rejected : Remainder}
      (operatorSpan : SourceSpan)
      (operatorParsed : ExactTokenParses (.symbol .colonEqual) input
        operatorSpan afterOperator)
      (valueRejected : YulExpressionRejects afterOperator rejected) :
      YulLetInitializerRejects input rejected

/-- Ordinary public `let` success, retaining diagnosed names and expression
success while preserving its exact AST and covering span. -/
inductive YulLetStatementOrdinaryParses :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input afterMarker afterNames output : Remainder}
      {names : YulNamesOrdinaryValue}
      {initializer : Option Syntax.YulExpr}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (namesParsed : YulNamesOrdinaryParses afterMarker names afterNames)
      (initializerParsed : YulLetInitializerOrdinaryParses afterNames
        initializer output) :
      YulLetStatementOrdinaryParses input {
        span := SourceSpan.cover markerSpan
          (yulLetEnd names.span initializer)
        value := .letDecl names.names initializer
      } output

/-- Exact public `let` rejection at its marker, name sequence, or present
initializer expression. -/
inductive YulLetStatementRejects : Remainder → Remainder → Prop where
  | markerRejected {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .letKw)) :
      YulLetStatementRejects input input
  | namesRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (namesRejected : YulNamesRejects afterMarker rejected) :
      YulLetStatementRejects input rejected
  | initializerRejected
      {input afterMarker afterNames rejected : Remainder}
      {names : YulNamesOrdinaryValue}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (namesParsed : YulNamesOrdinaryParses afterMarker names afterNames)
      (initializerRejected : YulLetInitializerRejects afterNames rejected) :
      YulLetStatementRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulStatementBasicOutcomeGrammar
/-!
Parser-independent ordinary successes and exact rejection traces for the
nonrecursive expression, source-level `return(...)`, and keyword-only Yul
statement primaries.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary expression-statement success uses the public ordinary expression
relation and preserves the expression AST and span exactly. -/
abbrev YulExpressionStatementOrdinaryParses :=
  YulExpressionStatementParses YulExpressionOrdinaryParses

/-- Exact rejection of an inline-Yul expression statement. -/
inductive YulExpressionStatementRejects : Remainder → Remainder → Prop where
  | expressionRejected {input rejected : Remainder}
      (expressionRejected : YulExpressionRejects input rejected) :
      YulExpressionStatementRejects input rejected

/-- Ordinary source-level `return(...)` success reuses the exact synthesized
call grammar with public ordinary expressions. -/
abbrev YulReturnBuiltinOrdinaryParses :=
  YulReturnBuiltinParses YulExpressionOrdinaryParses

/-- Exact rejection stage of one source-level `return(...)` attempt. -/
inductive YulReturnBuiltinRejects : Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .returnKw)) :
      YulReturnBuiltinRejects input input
  | argumentsRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .returnKw) input markerSpan
        afterMarker)
      (argumentsRejected : DelimitedListRejects .leftParen .rightParen true true
        YulExpressionOrdinaryParses YulExpressionRejects afterMarker rejected) :
      YulReturnBuiltinRejects input rejected

/-- Ordinary keyword-only control success is already exact token parsing. -/
abbrev YulControlTokenOrdinaryParses
    (keyword : HardKeyword) (statementValue : Syntax.YulStmtValue) :=
  YulControlTokenParses keyword statementValue

/-- Exact nonconsuming rejection of one keyword-only Yul control token. -/
inductive YulControlTokenRejects (keyword : HardKeyword) :
    Remainder → Remainder → Prop where
  | keywordMissing {input : Remainder}
      (keywordAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword keyword)) :
      YulControlTokenRejects keyword input input

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulStatementLevelGrammar
/-!
Parser-independent level bundle for recursive inline-Yul statements.

One level packages clean success, broader ordinary success, exact rejection,
and the laws needed to use that level inside the next recursive block.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One complete declarative approximation of recursive Yul statements. -/
structure YulStatementLevel where
  cleanParses : Remainder → Syntax.YulStmt → Remainder → Prop
  ordinaryParses : Remainder → Syntax.YulStmt → Remainder → Prop
  rejects : Remainder → Remainder → Prop
  outcomes : DeterministicOutcomeSpec ordinaryParses rejects
  cleanToOrdinary : ∀ {input statement output},
    cleanParses input statement output →
      ordinaryParses input statement output

namespace YulStatementLevel

/-- Fuel zero recognizes no statement success or rejection outcome. -/
def empty : YulStatementLevel where
  cleanParses := fun _ _ _ => False
  ordinaryParses := fun _ _ _ => False
  rejects := fun _ _ => False
  outcomes := {
    successOutputUnique := by
      intro input left right afterLeft afterRight leftParsed
      exact False.elim leftParsed
    successRejectDisjoint := by
      intro input rejected rejection
      exact False.elim rejection
  }
  cleanToOrdinary := by
    intro input statement output parsed
    exact False.elim parsed

/-- Compose one core outcome with maximal optional termination and the outer
recovering statement layer. -/
def ofCore
    (cleanCore ordinaryCore :
      Remainder → Syntax.YulStmt → Remainder → Prop)
    (coreRejects : Remainder → Remainder → Prop)
    (coreOutcomes : DeterministicOutcomeSpec ordinaryCore coreRejects)
    (cleanCoreToOrdinary : ∀ {input statement output},
      cleanCore input statement output →
        ordinaryCore input statement output)
    (coreBoundaryDisjoint : ∀ {input rejected},
      YulStatementRejects input rejected →
        ¬ ∃ statement output, ordinaryCore input statement output) :
    YulStatementLevel where
  cleanParses := YulStatementTerminatedParses cleanCore
  ordinaryParses := YulStatementLayerOrdinaryParses
    (YulStatementTerminatedOrdinaryParses ordinaryCore)
    (YulStatementTerminatedRejects coreRejects)
  rejects := YulStatementRejects
  outcomes := yulStatementLayerDeterministicOutcomeSpec
    (yulStatementTerminatedDeterministicOutcomeSpec coreOutcomes)
    (YulStatementRejects.disjointTerminatedOrdinary coreBoundaryDisjoint)
  cleanToOrdinary := by
    intro input statement output parsed
    exact .terminated (parsed.toOrdinary cleanCoreToOrdinary)

end YulStatementLevel

end Solcore.Syntax.DeclarativeGrammar
end
