import Solcore.Syntax.DeclarativeParenthesizedRejectionTraceExactnessProperties

/-! Prioritized rejection and success are disjoint without parser execution. -/

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

private theorem tail_comma_present
    {input output : Remainder} {values : List Syntax.Expr} {span : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : ParenthesizedTupleTailTraceParses elementTrace source endByte input values span output trace) :
    ∃ commaSpan, TokenAt input.tokens input.endIndex input.cursor { span := commaSpan, value := .symbol .comma } := by
  cases parsed with
  | trailing commaSpan _ comma _
  | final commaSpan _ comma _ _ _ _ _
  | next commaSpan _ comma _ _ _ _ => exact ⟨commaSpan, comma.1⟩

include successUnique disjoint in
theorem ParenthesizedTupleTailTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ParenthesizedTupleTailTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ¬ ∃ values closingSpan output events,
      ParenthesizedTupleTailTraceParses elementTrace source endByte input values closingSpan output events := by
  induction rejection with
  | commaMissing absent reported =>
      rintro ⟨_, _, _, _, parsed⟩
      exact absent (tail_comma_present parsed)
  | elementRejected span token absent child =>
      rintro ⟨_, _, _, _, parsed⟩
      cases parsed with
      | trailing _ _ otherToken closing =>
          cases token.output_unique otherToken
          exact absent ⟨_, closing.1⟩
      | final _ _ otherToken _ other _ _ _
      | next _ _ otherToken _ other _ _ =>
          cases token.output_unique otherToken
          exact disjoint child ⟨_, _, _, other⟩
  | closingMissing span token absent child progress commaAbsent closingAbsent reported =>
      rintro ⟨_, _, _, _, parsed⟩
      cases parsed with
      | trailing _ _ otherToken closing =>
          cases token.output_unique otherToken
          exact absent ⟨_, closing.1⟩
      | final _ _ otherToken _ other _ _ closing =>
          cases token.output_unique otherToken
          cases (successUnique child other).2.1
          exact closingAbsent ⟨_, closing.1⟩
      | next _ _ otherToken _ other _ tail =>
          cases token.output_unique otherToken
          cases (successUnique child other).2.1
          exact commaAbsent (tail_comma_present tail)
  | laterRejected span nextSpan token absent child progress nextComma tail ih =>
      rintro ⟨_, _, _, _, parsed⟩
      cases parsed with
      | trailing _ _ otherToken closing =>
          cases token.output_unique otherToken
          exact absent ⟨_, closing.1⟩
      | final _ _ otherToken _ other _ commaAbsent _ =>
          cases token.output_unique otherToken
          cases (successUnique child other).2.1
          exact commaAbsent ⟨nextSpan, nextComma⟩
      | next _ _ otherToken _ other _ otherTail =>
          cases token.output_unique otherToken
          cases (successUnique child other).2.1
          exact ih ⟨_, _, _, _, otherTail⟩

include successUnique disjoint in
theorem ParenthesizedExpressionTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ParenthesizedExpressionTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, ParenthesizedExpressionTraceParses elementTrace source endByte input value output events := by
  rintro ⟨_, _, _, parsed⟩
  cases rejection with
  | openingMissing absent reported =>
      cases parsed with
      | empty span _ token _
      | group span _ token _ _ _ _ _
      | tuple span _ token _ _ _ _ => exact absent ⟨span, token.1⟩
  | firstRejected span token absent child =>
      cases parsed with
      | empty _ _ otherToken closing =>
          cases token.output_unique otherToken
          exact absent ⟨_, closing.1⟩
      | group _ _ otherToken _ other _ _ _
      | tuple _ _ otherToken _ other _ _ =>
          cases token.output_unique otherToken
          exact disjoint child ⟨_, _, _, other⟩
  | closingMissing span token absent child progress commaAbsent closingAbsent reported =>
      cases parsed with
      | empty _ _ otherToken closing =>
          cases token.output_unique otherToken
          exact absent ⟨_, closing.1⟩
      | group _ _ otherToken _ other _ _ closing =>
          cases token.output_unique otherToken
          cases (successUnique child other).2.1
          exact closingAbsent ⟨_, closing.1⟩
      | tuple _ _ otherToken _ other _ tail =>
          cases token.output_unique otherToken
          cases (successUnique child other).2.1
          exact commaAbsent (tail_comma_present tail)
  | tailRejected span nextSpan token absent child progress nextComma tail =>
      cases parsed with
      | empty _ _ otherToken closing =>
          cases token.output_unique otherToken
          exact absent ⟨_, closing.1⟩
      | group _ _ otherToken _ other _ commaAbsent _ =>
          cases token.output_unique otherToken
          cases (successUnique child other).2.1
          exact commaAbsent ⟨nextSpan, nextComma⟩
      | tuple _ _ otherToken _ other _ otherTail =>
          cases token.output_unique otherToken
          cases (successUnique child other).2.1
          exact tail.disjoint_success successUnique disjoint ⟨_, _, _, _, otherTail⟩

end Solcore.Syntax.DeclarativeGrammar
