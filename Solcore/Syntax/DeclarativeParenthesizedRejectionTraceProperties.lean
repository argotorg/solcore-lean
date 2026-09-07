import Solcore.Syntax.DeclarativeParenthesizedRejectionTraceGrammar
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Erasure separates raw marker failures from the older selected grammars. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {ordinary : Remainder → Syntax.Expr → Remainder → Prop}
  {rejects : Remainder → Remainder → Prop} {source : SourceId} {endByte : Nat}

theorem ParenthesizedTupleTailTraceRejects.ordinary_of_comma_present
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ordinary input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      rejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ParenthesizedTupleTailTraceRejects elementTrace elementRejects source endByte input rejected report trace)
    (selected : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .comma }) :
    ParenthesizedTupleTailRejects ordinary rejects input rejected := by
  induction rejection with
  | commaMissing absent reported => exact False.elim (absent selected)
  | elementRejected span comma absent child => exact .elementRejected span comma absent (rejectErases child)
  | closingMissing span comma absent child progress commaAbsent closingAbsent reported =>
      exact .closingMissing span comma absent (successErases child) progress commaAbsent closingAbsent
  | laterRejected span nextSpan comma absent child progress nextComma tail ih =>
      exact .laterRejected span comma absent (successErases child) progress (ih ⟨nextSpan, nextComma⟩)

theorem ParenthesizedTupleTailTraceRejects.ordinary_cases
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ordinary input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      rejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ParenthesizedTupleTailTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    (TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .comma) ∧ rejected = input) ∨
      ParenthesizedTupleTailRejects ordinary rejects input rejected := by
  cases rejection with
  | commaMissing absent reported => exact .inl ⟨absent, rfl⟩
  | elementRejected span comma absent child => exact .inr (.elementRejected span comma absent (rejectErases child))
  | closingMissing span comma absent child progress commaAbsent closingAbsent reported =>
      exact .inr (.closingMissing span comma absent (successErases child) progress commaAbsent closingAbsent)
  | laterRejected span nextSpan comma absent child progress nextComma tail =>
      exact .inr (.laterRejected span comma absent (successErases child) progress
        (tail.ordinary_of_comma_present successErases rejectErases ⟨nextSpan, nextComma⟩))

theorem ParenthesizedExpressionTraceRejects.ordinary_cases
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ordinary input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      rejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ParenthesizedExpressionTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    (TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftParen) ∧ rejected = input) ∨
      ParenthesizedExpressionRejects ordinary rejects input rejected := by
  cases rejection with
  | openingMissing absent reported => exact .inl ⟨absent, rfl⟩
  | firstRejected span opening absent child => exact .inr (.firstRejected span opening absent (rejectErases child))
  | closingMissing span opening absent child progress commaAbsent closingAbsent reported =>
      exact .inr (.closingMissing span opening absent (successErases child) progress commaAbsent closingAbsent)
  | tailRejected span commaSpan opening absent child progress comma tail =>
      exact .inr (.tailRejected span opening absent (successErases child) progress
        (tail.ordinary_of_comma_present successErases rejectErases ⟨commaSpan, comma⟩))

theorem ParenthesizedExpressionTraceRejects.ordinary_of_opening_present
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ordinary input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      rejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ParenthesizedExpressionTraceRejects elementTrace elementRejects source endByte input rejected report trace)
    (selected : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .leftParen }) :
    ParenthesizedExpressionRejects ordinary rejects input rejected := by
  rcases rejection.ordinary_cases successErases rejectErases with ⟨absent, _⟩ | ordinary
  · exact False.elim (absent selected)
  · exact ordinary

end Solcore.Syntax.DeclarativeGrammar
