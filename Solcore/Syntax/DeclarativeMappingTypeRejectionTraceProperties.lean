import Solcore.Syntax.DeclarativeMappingTypeRejectionTraceGrammar
import Solcore.Syntax.DeclarativeMappingTypeTraceGrammar
import Solcore.Syntax.DeclarativeCoreTypeOutcomeGrammar
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties

/-! Raw mapping failures include marker/opening failures. Erasure separates
them explicitly from the older positively selected mapping relation. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {ordinaryRejects : Remainder → Remainder → Prop} {source : SourceId} {endByte : Nat}

theorem MappingTypeTraceRejects.ordinary_cases
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ordinaryRejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : MappingTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    (TokenKindAbsentAt input.tokens input.endIndex input.cursor (.identifier ContextualKeyword.mapping.spelling) ∧
      rejected = input) ∨
    (∃ markerSpan afterMarker, ExactTokenParses (.identifier ContextualKeyword.mapping.spelling) input markerSpan afterMarker ∧
      TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex afterMarker.cursor (.symbol .leftParen) ∧
      rejected = afterMarker) ∨
    MappingTypeRejects ordinaryRejects input rejected := by
  cases rejection with
  | markerMissing absent => exact .inl ⟨absent, rfl⟩
  | openingMissing span marker absent => exact .inr (.inl ⟨span, _, marker, absent, rfl⟩)
  | keyRejected m o marker opening key => exact .inr (.inr (.keyRejected m o marker opening (rejectErases key)))
  | arrowMissing m o marker opening key absent =>
      exact .inr (.inr (.arrowMissing m o marker opening (successErases key) absent))
  | valueRejected m o a marker opening key arrow value =>
      exact .inr (.inr (.valueRejected m o a marker opening (successErases key) arrow (rejectErases value)))
  | closingMissing m o a marker opening key arrow value absent =>
      exact .inr (.inr (.closingMissing m o a marker opening (successErases key) arrow (successErases value) absent))

theorem MappingTypeTraceRejects.ordinary_of_prefix
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ordinaryRejects input rejected)
    {input afterMarker afterOpening rejected : Remainder} {markerSpan openingSpan : SourceSpan}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (marker : ExactTokenParses (.identifier ContextualKeyword.mapping.spelling) input markerSpan afterMarker)
    (opening : ExactTokenParses (.symbol .leftParen) afterMarker openingSpan afterOpening)
    (rejection : MappingTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    MappingTypeRejects ordinaryRejects input rejected := by
  rcases rejection.ordinary_cases successErases rejectErases with missing | missing | ordinary
  · exact False.elim (missing.1 ⟨markerSpan, marker.1⟩)
  · rcases missing with ⟨span, afterOther, other, absent, _⟩
    cases marker.output_unique other
    exact False.elim (absent ⟨openingSpan, opening.1⟩)
  · exact ordinary

private theorem mapping_absent_conflicts_token {kind : TokenKind} {input output : Remainder} {span : SourceSpan}
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
theorem MappingTypeTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : MappingTypeTraceRejects elementTrace elementRejects source endByte input afterLeft leftReport leftTrace)
    (right : MappingTypeTraceRejects elementTrace elementRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left <;> cases right <;>
    grind (ematch := 12) only [ExactTokenParses.result_unique, mapping_absent_conflicts_token,
      RejectAtReports.diagnostic_unique]

include successUnique disjoint in
theorem MappingTypeTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : MappingTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, MappingTypeTraceParses elementTrace source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases parsed
  cases rejection <;>
    grind (ematch := 12) only [ExactTokenParses.result_unique, mapping_absent_conflicts_token]

end Solcore.Syntax.DeclarativeGrammar
