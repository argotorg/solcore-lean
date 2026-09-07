import Solcore.Syntax.DeclarativeParenthesizedTraceProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact child outcomes determine every forward element, close, remainder,
and diagnostic occurrence. Cover need not be injective in either endpoint. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

private theorem absent_conflicts_exact {kind : TokenKind} {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False := absent ⟨span, parsed.1⟩

theorem ParenthesizedTupleTailTraceParses.result_unique
    (unique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : List Syntax.Expr}
    {leftClosing rightClosing : SourceSpan} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ParenthesizedTupleTailTraceParses elementTrace source endByte input left leftClosing afterLeft leftTrace)
    (rightParsed : ParenthesizedTupleTailTraceParses elementTrace source endByte input right rightClosing afterRight rightTrace) :
    left = right ∧ leftClosing = rightClosing ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  induction leftParsed generalizing right rightClosing afterRight rightTrace with
  | trailing commaSpan closingSpan comma closing =>
      cases rightParsed <;> grind [ExactTokenParses.result_unique, absent_conflicts_exact]
  | final commaSpan closingSpan comma closingAbsent child progress commaAbsent closing =>
      cases rightParsed <;> grind [ExactTokenParses.result_unique,
        absent_conflicts_exact, ParenthesizedTupleTailTraceParses.comma_conflicts_absent]
  | next commaSpan closingSpan comma closingAbsent child progress tail ih =>
      cases rightParsed <;> grind [ExactTokenParses.result_unique,
        absent_conflicts_exact, ParenthesizedTupleTailTraceParses.comma_conflicts_absent]

theorem ParenthesizedExpressionTraceParses.result_unique
    (unique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Syntax.Expr} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ParenthesizedExpressionTraceParses elementTrace source endByte input left afterLeft leftTrace)
    (rightParsed : ParenthesizedExpressionTraceParses elementTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed <;> cases rightParsed <;>
    grind [ExactTokenParses.result_unique, ParenthesizedTupleTailTraceParses.result_unique unique,
      absent_conflicts_exact, ParenthesizedTupleTailTraceParses.comma_conflicts_absent]

end Solcore.Syntax.DeclarativeGrammar
