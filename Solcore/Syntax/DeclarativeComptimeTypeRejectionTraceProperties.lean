import Solcore.Syntax.DeclarativeComptimeTypeRejectionTraceGrammar
import Solcore.Syntax.DeclarativeComptimeTypeTraceProperties
import Solcore.Syntax.DeclarativeCoreTypeOutcomeGrammar
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties
import Solcore.Syntax.DeclarativeTraceOutcomeSpec

/-! Raw comptime failures include marker/opening failures. Erasure separates
them explicitly from the older positively selected comptime relation. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {ordinaryRejects : Remainder → Remainder → Prop} {source : SourceId} {endByte : Nat}

theorem ComptimeTypeTraceRejects.ordinary_cases
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ordinaryRejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ComptimeTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    (TokenKindAbsentAt input.tokens input.endIndex input.cursor (.identifier ContextualKeyword.comptime.spelling) ∧
      rejected = input) ∨
    (∃ markerSpan afterMarker, ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker ∧
      TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex afterMarker.cursor (.symbol .less) ∧
      rejected = afterMarker) ∨
    ComptimeTypeRejects ordinaryRejects input rejected := by
  cases rejection with
  | markerMissing absent => exact .inl ⟨absent, rfl⟩
  | openingMissing span marker absent => exact .inr (.inl ⟨span, _, marker, absent, rfl⟩)
  | innerRejected m o marker opening typed => exact .inr (.inr (.innerRejected m o marker opening (rejectErases typed)))
  | closingMissing m o marker opening typed absent =>
      exact .inr (.inr (.closingMissing m o marker opening (successErases typed) absent))

theorem ComptimeTypeTraceRejects.ordinary_of_prefix
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ordinaryRejects input rejected)
    {input afterMarker afterOpening rejected : Remainder} {markerSpan openingSpan : SourceSpan}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker)
    (opening : ExactTokenParses (.symbol .less) afterMarker openingSpan afterOpening)
    (rejection : ComptimeTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ComptimeTypeRejects ordinaryRejects input rejected := by
  rcases rejection.ordinary_cases successErases rejectErases with missing | missing | ordinary
  · exact False.elim (missing.1 ⟨markerSpan, marker.1⟩)
  · rcases missing with ⟨span, afterOther, other, absent, _⟩
    cases marker.output_unique other
    exact False.elim (absent ⟨openingSpan, opening.1⟩)
  · exact ordinary

private theorem comptime_absent_conflicts_token {kind : TokenKind} {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (token : ExactTokenParses kind input span output) : False := absent ⟨span, token.1⟩

variable
  (successUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
    elementTrace source endByte input left afterLeft leftTrace →
    elementTrace source endByte input right afterRight rightTrace →
      left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
  (rejectUnique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
    elementRejects source endByte input afterLeft leftReport leftTrace →
    elementRejects source endByte input afterRight rightReport rightTrace →
      afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace)
  (disjoint : ∀ {input rejected diagnostic trace},
    elementRejects source endByte input rejected diagnostic trace →
      ¬ ∃ value output events, elementTrace source endByte input value output events)

include successUnique rejectUnique disjoint in
theorem ComptimeTypeTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : ComptimeTypeTraceRejects elementTrace elementRejects source endByte input afterLeft leftReport leftTrace)
    (right : ComptimeTypeTraceRejects elementTrace elementRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left <;> cases right <;>
    grind (ematch := 12) only [ExactTokenParses.result_unique, comptime_absent_conflicts_token,
      RejectAtReports.diagnostic_unique]

include successUnique disjoint in
theorem ComptimeTypeTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ComptimeTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, ComptimeTypeTraceParses elementTrace source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases parsed
  cases rejection <;>
    grind (ematch := 12) only [ExactTokenParses.result_unique, comptime_absent_conflicts_token]

theorem ComptimeTypeTraceRejects.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (successProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ComptimeTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | markerMissing | openingMissing => exact .nil
  | innerRejected _ _ _ _ typed => exact rejectProtected typed
  | closingMissing _ _ _ _ typed => exact successProtected typed

theorem comptimeTypeTraceExactOutcomeSpec
    (types : TraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    TraceExactOutcomeSpec (ComptimeTypeTraceParses elementTrace)
      (ComptimeTypeTraceRejects elementTrace elementRejects) source endByte where
  successResultUnique := ComptimeTypeTraceParses.result_unique types.successResultUnique
  rejectResultUnique := ComptimeTypeTraceRejects.result_unique
    types.successResultUnique types.rejectResultUnique types.successRejectDisjoint
  successRejectDisjoint := ComptimeTypeTraceRejects.disjoint_success
    types.successResultUnique types.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
