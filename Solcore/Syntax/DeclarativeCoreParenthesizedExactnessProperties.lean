import Solcore.Syntax.DeclarativeCoreParenthesizedOutcomeProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact source-order elements, closing spans, and parenthesized Core ASTs. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- Exact nested expressions fix a tuple tail's forward elements, close, and output. -/
theorem ParenthesizedTupleTailParses.result_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects) :
    ∀ {input : Remainder} {left right : List Syntax.Expr}
      {leftClosing rightClosing : SourceSpan} {afterLeft afterRight : Remainder},
      ParenthesizedTupleTailParses nestedOrdinary input left leftClosing afterLeft →
      ParenthesizedTupleTailParses nestedOrdinary input right rightClosing afterRight →
      left = right ∧ leftClosing = rightClosing ∧ afterLeft = afterRight := by
  intro input left right leftClosing rightClosing afterLeft afterRight leftParsed
  induction leftParsed generalizing right rightClosing afterRight with
  | trailing leftCommaSpan leftClosingSpan leftComma leftClosing =>
      intro rightParsed
      cases rightParsed <;>
        grind [ExactTokenParses.result_unique, absent_conflicts_exact]
  | final leftCommaSpan leftClosingSpan leftComma leftClosingAbsent
      leftElement leftProgress leftCommaAbsent leftClosing =>
      intro rightParsed
      cases rightParsed <;>
        grind [ExactTokenParses.result_unique, outcomes.successResultUnique,
          absent_conflicts_exact, ParenthesizedTupleTailParses.comma_conflicts_absent]
  | next leftCommaSpan leftClosingSpan leftComma leftClosingAbsent
      leftElement leftProgress leftTail ih =>
      intro rightParsed
      cases rightParsed <;>
        grind [ExactTokenParses.result_unique, outcomes.successResultUnique,
          absent_conflicts_exact, ParenthesizedTupleTailParses.comma_conflicts_absent]

/-- Exact nested expressions fix empty/group/tuple choice and the complete AST. -/
theorem ParenthesizedExpressionOrdinaryParses.value_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : ParenthesizedExpressionOrdinaryParses nestedOrdinary input left afterLeft)
    (rightParsed : ParenthesizedExpressionOrdinaryParses nestedOrdinary input right afterRight) :
    left = right := by
  cases leftParsed <;> cases rightParsed <;>
    grind [ExactTokenParses.result_unique, outcomes.successResultUnique,
      ParenthesizedTupleTailParses.result_unique outcomes,
      absent_conflicts_exact, ParenthesizedTupleTailParses.comma_conflicts_absent]

/-- Parenthesized ordinary success fixes both the complete AST and remainder. -/
theorem ParenthesizedExpressionOrdinaryParses.result_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : ParenthesizedExpressionOrdinaryParses nestedOrdinary input left afterLeft)
    (rightParsed : ParenthesizedExpressionOrdinaryParses nestedOrdinary input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique outcomes rightParsed,
    leftParsed.output_unique outcomes.toDeterministicOutcomeSpec rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
