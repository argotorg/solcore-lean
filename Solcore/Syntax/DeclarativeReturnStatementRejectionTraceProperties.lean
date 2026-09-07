import Solcore.Syntax.DeclarativeReturnStatementRejectionTraceGrammar
import Solcore.Syntax.DeclarativeReturnStatementTraceProperties
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties

/-! Exact first-return-failure outcomes under explicit expression laws.
Uncommitted reports and preceding event sequences are independently unique. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {expressionTrace : SourceId → Nat → Remainder → Syntax.Expr →
    Remainder → List ParseDiagnostic → Prop}
  {expressionRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
  {ordinaryRejects : Remainder → Remainder → Prop}
  {source : SourceId} {endByte : Nat}

theorem OptionalReturnValueTraceRejects.ordinary
    (rejectErases : ∀ {input rejected diagnostic trace},
      expressionRejects source endByte input rejected diagnostic trace → ordinaryRejects input rejected)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OptionalReturnValueTraceRejects expressionRejects source endByte
      input rejected diagnostic trace) : OptionalReturnValueRejects ordinaryRejects input rejected := by
  cases rejection with
  | expressionRejected absent rejected => exact .expressionRejected absent (rejectErases rejected)

theorem ReturnStatementTraceRejects.ordinary
    (successErases : ∀ {input value output trace},
      expressionTrace source endByte input value output trace → expressionOrdinary input value output)
    (rejectErases : ∀ {input rejected diagnostic trace},
      expressionRejects source endByte input rejected diagnostic trace → ordinaryRejects input rejected)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ReturnStatementTraceRejects expressionTrace expressionRejects source endByte
      input rejected diagnostic trace) :
    ReturnStatementRejects expressionOrdinary ordinaryRejects input rejected := by
  cases rejection with
  | markerRejected absent reported => exact .markerRejected absent
  | valueRejected span marker rejected => exact .valueRejected span marker (rejected.ordinary rejectErases)
  | semicolonRejected span marker value absent reported =>
      exact .semicolonRejected span marker (value.ordinary successErases) absent

variable
  (successUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
    expressionTrace source endByte input left afterLeft leftTrace →
    expressionTrace source endByte input right afterRight rightTrace →
      left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
  (rejectUnique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
    expressionRejects source endByte input afterLeft leftReport leftTrace →
    expressionRejects source endByte input afterRight rightReport rightTrace →
      afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace)
  (disjoint : ∀ {input rejected diagnostic trace},
    expressionRejects source endByte input rejected diagnostic trace →
      ¬ ∃ value output events, expressionTrace source endByte input value output events)

include rejectUnique in
theorem OptionalReturnValueTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : OptionalReturnValueTraceRejects expressionRejects source endByte
      input afterLeft leftReport leftTrace)
    (right : OptionalReturnValueTraceRejects expressionRejects source endByte
      input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | expressionRejected _ rejected =>
      cases right with
      | expressionRejected _ other => exact rejectUnique rejected other

include disjoint in
theorem OptionalReturnValueTraceRejects.disjoint_success
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OptionalReturnValueTraceRejects expressionRejects source endByte
      input rejected diagnostic trace) :
    ¬ ∃ value output events,
      OptionalReturnValueTraceParses expressionTrace source endByte input value output events := by
  rintro ⟨_, _, _, parsed⟩
  cases rejection with
  | expressionRejected absent rejected =>
      cases parsed with
      | absent span token => exact absent ⟨span, token⟩
      | present _ parsed => exact disjoint rejected ⟨_, _, _, parsed⟩

include successUnique rejectUnique disjoint in
theorem ReturnStatementTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : ReturnStatementTraceRejects expressionTrace expressionRejects source endByte
      input afterLeft leftReport leftTrace)
    (right : ReturnStatementTraceRejects expressionTrace expressionRejects source endByte
      input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | markerRejected absent reported =>
      cases right with
      | markerRejected _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | valueRejected span marker _ | semicolonRejected span marker _ _ _ =>
          exact False.elim (absent ⟨span, marker.1⟩)
  | valueRejected span marker rejected =>
      cases right with
      | markerRejected absent _ => exact False.elim (absent ⟨span, marker.1⟩)
      | valueRejected _ otherMarker other =>
          cases marker.output_unique otherMarker
          exact rejected.result_unique rejectUnique other
      | semicolonRejected _ otherMarker parsed _ _ =>
          cases marker.output_unique otherMarker
          exact False.elim (rejected.disjoint_success disjoint ⟨_, _, _, parsed⟩)
  | semicolonRejected span marker parsed absent reported =>
      cases right with
      | markerRejected missing _ => exact False.elim (missing ⟨span, marker.1⟩)
      | valueRejected _ otherMarker rejected =>
          cases marker.output_unique otherMarker
          exact False.elim (rejected.disjoint_success disjoint ⟨_, _, _, parsed⟩)
      | semicolonRejected _ otherMarker other _ otherReport =>
          cases marker.output_unique otherMarker
          rcases parsed.result_unique successUnique other with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, reported.diagnostic_unique otherReport, rfl⟩

include successUnique disjoint in
theorem ReturnStatementTraceRejects.disjoint_success
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ReturnStatementTraceRejects expressionTrace expressionRejects source endByte
      input rejected diagnostic trace) :
    ¬ ∃ statement output events,
      ReturnStatementTraceParses expressionTrace source endByte input statement output events := by
  rintro ⟨_, _, _, parsed⟩
  cases parsed with
  | parsed markerSpan semicolonSpan marker value semicolon =>
      cases rejection with
      | markerRejected absent _ => exact absent ⟨markerSpan, marker.1⟩
      | valueRejected _ otherMarker rejected =>
          cases marker.output_unique otherMarker
          exact rejected.disjoint_success disjoint ⟨_, _, _, value⟩
      | semicolonRejected _ otherMarker other absent _ =>
          cases marker.output_unique otherMarker
          cases (value.result_unique successUnique other).2.1
          exact absent ⟨semicolonSpan, semicolon.1⟩

end Solcore.Syntax.DeclarativeGrammar
