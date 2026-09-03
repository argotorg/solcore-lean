import Solcore.Syntax.DeclarativeCorePatternParenthesizedOutcomeProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact success values for parenthesized Core patterns and tuple tails. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem patternTuple_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- Exact nested patterns fix a tuple tail's forward list, closing span, and
final remainder, including its trailing-comma branch. -/
theorem ParenthesizedPatternTupleTailParses.result_unique
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects) :
    ∀ {input : Remainder} {left right : List Syntax.Pattern}
      {leftClosing rightClosing : SourceSpan}
      {afterLeft afterRight : Remainder},
      ParenthesizedPatternTupleTailParses nestedOrdinary input left
        leftClosing afterLeft →
      ParenthesizedPatternTupleTailParses nestedOrdinary input right
        rightClosing afterRight →
      left = right ∧ leftClosing = rightClosing ∧ afterLeft = afterRight := by
  intro input left right leftClosing rightClosing afterLeft afterRight leftParsed
  induction leftParsed generalizing right rightClosing afterRight with
  | trailing leftCommaSpan leftClosingSpan leftComma leftClosing =>
      intro rightParsed
      cases rightParsed <;>
        grind [ExactTokenParses.result_unique,
          patternTuple_absent_conflicts_exact]
  | final leftCommaSpan leftClosingSpan leftComma leftClosingAbsent
      leftElement leftProgress leftCommaAbsent leftClosing =>
      intro rightParsed
      cases rightParsed <;>
        grind [ExactTokenParses.result_unique,
          nestedOutcomes.successResultUnique,
          patternTuple_absent_conflicts_exact,
          ParenthesizedPatternTupleTailParses.comma_conflicts_absent]
  | next leftCommaSpan leftClosingSpan leftComma leftClosingAbsent
      leftElement leftProgress leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed <;>
        grind [ExactTokenParses.result_unique,
          nestedOutcomes.successResultUnique,
          patternTuple_absent_conflicts_exact,
          ParenthesizedPatternTupleTailParses.comma_conflicts_absent]

/-- Exact nested patterns fix the complete empty, group, or tuple AST. -/
theorem ParenthesizedPatternOrdinaryParses.value_unique
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : ParenthesizedPatternOrdinaryParses nestedOrdinary input left
      afterLeft)
    (rightParsed : ParenthesizedPatternOrdinaryParses nestedOrdinary input right
      afterRight) : left = right := by
  cases leftParsed <;> cases rightParsed <;>
    grind [ExactTokenParses.result_unique,
      nestedOutcomes.successResultUnique,
      ParenthesizedPatternTupleTailParses.result_unique nestedOutcomes,
      patternTuple_absent_conflicts_exact,
      ParenthesizedPatternTupleTailParses.comma_conflicts_absent]

/-- Parenthesized pattern success fixes its complete AST and final remainder. -/
theorem ParenthesizedPatternOrdinaryParses.result_unique
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : ParenthesizedPatternOrdinaryParses nestedOrdinary input left
      afterLeft)
    (rightParsed : ParenthesizedPatternOrdinaryParses nestedOrdinary input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique nestedOutcomes rightParsed,
    leftParsed.output_unique nestedOutcomes.toDeterministicOutcomeSpec
      rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
