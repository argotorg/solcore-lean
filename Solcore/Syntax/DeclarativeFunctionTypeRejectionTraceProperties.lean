import Solcore.Syntax.DeclarativeFunctionTypeRejectionTraceGrammar
import Solcore.Syntax.DeclarativeFunctionTypeTraceProperties
import Solcore.Syntax.DeclarativeFunctionReturnsRejectionTraceProperties
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties

/-! The raw keyword failure is separated from selected function rejection.
Successful parameter-carrier preservation is required only for ordinary erasure. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {ordinaryRejects : Remainder → Remainder → Prop} {source : SourceId} {endByte : Nat}

theorem FunctionTypeTraceRejects.ordinary_cases
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ordinaryRejects input rejected)
    (childWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    (TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword .functionKw) ∧ rejected = input) ∨
      FunctionTypeRejects ordinaryRejects input rejected := by
  cases rejection with
  | markerMissing absent => exact .inl ⟨absent, rfl⟩
  | parametersRejected span marker parameters =>
      exact .inr (.parametersRejected span marker (parameters.ordinary successErases rejectErases))
  | returnsRejected span marker parameters returns =>
      exact .inr (.returnsRejected span marker (parameters.ordinary successErases childWindow)
        (returns.ordinary successErases rejectErases))

theorem FunctionTypeTraceRejects.ordinary_of_marker_present
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ordinaryRejects input rejected)
    (childWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input afterKeyword rejected : Remainder} {keywordSpan : SourceSpan}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (marker : ExactTokenParses (.keyword .functionKw) input keywordSpan afterKeyword)
    (rejection : FunctionTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    FunctionTypeRejects ordinaryRejects input rejected := by
  rcases rejection.ordinary_cases successErases rejectErases childWindow with missing | ordinary
  · exact False.elim (missing.1 ⟨keywordSpan, marker.1⟩)
  · exact ordinary

private theorem function_absent_conflicts_token {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword .functionKw))
    (token : ExactTokenParses (.keyword .functionKw) input span output) : False := absent ⟨span, token.1⟩

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
theorem FunctionTypeTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : FunctionTypeTraceRejects elementTrace elementRejects source endByte input afterLeft leftReport leftTrace)
    (right : FunctionTypeTraceRejects elementTrace elementRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  have listUnique := @TrailingDelimitedListTraceParses.result_unique Syntax.TypeExpr
    .leftParen .rightParen true elementTrace source endByte successUnique
  have listRejectUnique := @TrailingDelimitedListTraceRejects.result_unique Syntax.TypeExpr
    elementTrace elementRejects source endByte .leftParen .rightParen true .typeExpr
    successUnique rejectUnique disjoint
  have listDisjoint := @TrailingDelimitedListTraceRejects.disjoint_success Syntax.TypeExpr
    elementTrace elementRejects source endByte .leftParen .rightParen true .typeExpr successUnique disjoint
  have returnUnique := @FunctionReturnsTraceRejects.result_unique elementTrace elementRejects
    source endByte successUnique rejectUnique disjoint
  cases left <;> cases right <;>
    grind (ematch := 12) only [ExactTokenParses.result_unique, function_absent_conflicts_token,
      RejectAtReports.diagnostic_unique]

include successUnique disjoint in
theorem FunctionTypeTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, FunctionTypeTraceParses elementTrace source endByte input value output events := by
  have listUnique := @TrailingDelimitedListTraceParses.result_unique Syntax.TypeExpr
    .leftParen .rightParen true elementTrace source endByte successUnique
  have listDisjoint := @TrailingDelimitedListTraceRejects.disjoint_success Syntax.TypeExpr
    elementTrace elementRejects source endByte .leftParen .rightParen true .typeExpr successUnique disjoint
  have returnDisjoint := @FunctionReturnsTraceRejects.disjoint_success elementTrace elementRejects
    source endByte successUnique disjoint
  rintro ⟨value, output, events, parsed⟩
  cases parsed
  cases rejection <;>
    grind (ematch := 12) only [ExactTokenParses.result_unique, function_absent_conflicts_token]

theorem FunctionTypeTraceRejects.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (successProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | markerMissing => exact .nil
  | parametersRejected _ _ parameters => exact parameters.cascadeFilters successProtected rejectProtected
  | returnsRejected _ _ parameters returns =>
      exact (parameters.cascadeFilters successProtected).append
        (returns.cascadeFilters successProtected rejectProtected)

theorem functionTypeTraceExactOutcomeSpec
    (types : TraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    TraceExactOutcomeSpec (FunctionTypeTraceParses elementTrace)
      (FunctionTypeTraceRejects elementTrace elementRejects) source endByte where
  successResultUnique := FunctionTypeTraceParses.result_unique types.successResultUnique
  rejectResultUnique := FunctionTypeTraceRejects.result_unique
    types.successResultUnique types.rejectResultUnique types.successRejectDisjoint
  successRejectDisjoint := FunctionTypeTraceRejects.disjoint_success
    types.successResultUnique types.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
