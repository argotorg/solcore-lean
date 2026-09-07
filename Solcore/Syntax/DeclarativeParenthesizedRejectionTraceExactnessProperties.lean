import Solcore.Syntax.DeclarativeParenthesizedRejectionTraceProperties

/-! Full rejection functionality from independent child functionality. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}
  (successUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
    elementTrace source endByte input left afterLeft leftTrace →
    elementTrace source endByte input right afterRight rightTrace →
      left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
  (rejectUnique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
    elementRejects source endByte input afterLeft leftReport leftTrace →
    elementRejects source endByte input afterRight rightReport rightTrace →
      afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace)
  (disjoint : ∀ {input rejected report trace},
    elementRejects source endByte input rejected report trace →
      ¬ ∃ value output events, elementTrace source endByte input value output events)

include successUnique rejectUnique disjoint in
theorem ParenthesizedTupleTailTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : ParenthesizedTupleTailTraceRejects elementTrace elementRejects source endByte input afterLeft leftReport leftTrace)
    (right : ParenthesizedTupleTailTraceRejects elementTrace elementRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  induction left generalizing afterRight rightReport rightTrace with
  | commaMissing absent reported =>
      cases right with
      | commaMissing _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | elementRejected span token _ _
      | closingMissing span token _ _ _ _ _ _
      | laterRejected span _ token _ _ _ _ _ => exact False.elim (absent ⟨span, token.1⟩)
  | elementRejected span token absent child =>
      cases right with
      | commaMissing absent _ => exact False.elim (absent ⟨span, token.1⟩)
      | elementRejected _ otherToken _ other =>
          cases token.output_unique otherToken
          exact rejectUnique child other
      | closingMissing _ otherToken _ other _ _ _ _
      | laterRejected _ _ otherToken _ other _ _ _ =>
          cases token.output_unique otherToken
          exact False.elim (disjoint child ⟨_, _, _, other⟩)
  | closingMissing span token absent child progress commaAbsent closingAbsent reported =>
      cases right with
      | commaMissing absent _ => exact False.elim (absent ⟨span, token.1⟩)
      | elementRejected _ otherToken _ other =>
          cases token.output_unique otherToken
          exact False.elim (disjoint other ⟨_, _, _, child⟩)
      | closingMissing _ otherToken _ other _ _ _ otherReport =>
          cases token.output_unique otherToken
          rcases successUnique child other with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, reported.diagnostic_unique otherReport, rfl⟩
      | laterRejected _ nextSpan otherToken _ other _ nextComma _ =>
          cases token.output_unique otherToken
          cases (successUnique child other).2.1
          exact False.elim (commaAbsent ⟨nextSpan, nextComma⟩)
  | laterRejected span nextSpan token absent child progress nextComma tail ih =>
      cases right with
      | commaMissing absent _ => exact False.elim (absent ⟨span, token.1⟩)
      | elementRejected _ otherToken _ other =>
          cases token.output_unique otherToken
          exact False.elim (disjoint other ⟨_, _, _, child⟩)
      | closingMissing _ otherToken _ other _ commaAbsent _ _ =>
          cases token.output_unique otherToken
          cases (successUnique child other).2.1
          exact False.elim (commaAbsent ⟨nextSpan, nextComma⟩)
      | laterRejected _ _ otherToken _ other _ _ otherTail =>
          cases token.output_unique otherToken
          rcases successUnique child other with ⟨rfl, rfl, rfl⟩
          rcases ih otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

include successUnique rejectUnique disjoint in
theorem ParenthesizedExpressionTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : ParenthesizedExpressionTraceRejects elementTrace elementRejects source endByte input afterLeft leftReport leftTrace)
    (right : ParenthesizedExpressionTraceRejects elementTrace elementRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | openingMissing absent reported =>
      cases right with
      | openingMissing _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | firstRejected span token _ _
      | closingMissing span token _ _ _ _ _ _
      | tailRejected span _ token _ _ _ _ _ => exact False.elim (absent ⟨span, token.1⟩)
  | firstRejected span token absent child =>
      cases right with
      | openingMissing absent _ => exact False.elim (absent ⟨span, token.1⟩)
      | firstRejected _ otherToken _ other =>
          cases token.output_unique otherToken
          exact rejectUnique child other
      | closingMissing _ otherToken _ other _ _ _ _
      | tailRejected _ _ otherToken _ other _ _ _ =>
          cases token.output_unique otherToken
          exact False.elim (disjoint child ⟨_, _, _, other⟩)
  | closingMissing span token absent child progress commaAbsent closingAbsent reported =>
      cases right with
      | openingMissing absent _ => exact False.elim (absent ⟨span, token.1⟩)
      | firstRejected _ otherToken _ other =>
          cases token.output_unique otherToken
          exact False.elim (disjoint other ⟨_, _, _, child⟩)
      | closingMissing _ otherToken _ other _ _ _ otherReport =>
          cases token.output_unique otherToken
          rcases successUnique child other with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, reported.diagnostic_unique otherReport, rfl⟩
      | tailRejected _ nextSpan otherToken _ other _ nextComma _ =>
          cases token.output_unique otherToken
          cases (successUnique child other).2.1
          exact False.elim (commaAbsent ⟨nextSpan, nextComma⟩)
  | tailRejected span nextSpan token absent child progress nextComma tail  =>
      cases right with
      | openingMissing absent _ => exact False.elim (absent ⟨span, token.1⟩)
      | firstRejected _ otherToken _ other =>
          cases token.output_unique otherToken
          exact False.elim (disjoint other ⟨_, _, _, child⟩)
      | closingMissing _ otherToken _ other _ commaAbsent _ _ =>
          cases token.output_unique otherToken
          cases (successUnique child other).2.1
          exact False.elim (commaAbsent ⟨nextSpan, nextComma⟩)
      | tailRejected _ _ otherToken _ other _ _ otherTail =>
          cases token.output_unique otherToken
          rcases successUnique child other with ⟨rfl, rfl, rfl⟩
          rcases tail.result_unique successUnique rejectUnique disjoint otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

end Solcore.Syntax.DeclarativeGrammar
