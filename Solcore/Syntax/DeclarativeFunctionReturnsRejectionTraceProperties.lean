import Solcore.Syntax.DeclarativeFunctionReturnsRejectionTraceGrammar
import Solcore.Syntax.DeclarativeFunctionReturnsTraceProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceProperties
import Solcore.Syntax.DeclarativeCoreTypeOutcomeGrammar
import Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceProtectionProperties
import Solcore.Syntax.DeclarativeTraceOutcomeSpec

/-! Optional return rejection requires its marker and delegates to the exact
list outcome. Absence remains disjoint success; independent child laws prove
ordinary erasure, uniqueness, disjointness, and event protection. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {ordinaryRejects : Remainder → Remainder → Prop} {source : SourceId} {endByte : Nat}

theorem FunctionReturnsTraceRejects.marker_present
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionReturnsTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .identifier ContextualKeyword.returns.spelling } := by
  cases rejection with
  | present span marker _ => exact ⟨span, marker.1⟩

theorem FunctionReturnsTraceRejects.ordinary
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ordinaryRejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionReturnsTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    FunctionTypeReturnsRejects ordinaryRejects input rejected := by
  cases rejection with
  | present span marker values =>
      exact .valuesRejected span marker (values.ordinary successErases rejectErases)

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
theorem FunctionReturnsTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : FunctionReturnsTraceRejects elementTrace elementRejects source endByte input afterLeft leftReport leftTrace)
    (right : FunctionReturnsTraceRejects elementTrace elementRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | present _ marker left =>
      cases right with
      | present _ otherMarker right =>
          cases marker.output_unique otherMarker
          exact left.result_unique successUnique rejectUnique disjoint right

include successUnique disjoint in
theorem FunctionReturnsTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionReturnsTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ¬ ∃ arguments output events, FunctionReturnsTraceParses elementTrace source endByte input arguments output events := by
  rintro ⟨arguments, output, events, parsed⟩
  cases rejection with
  | present span marker rejection =>
      cases parsed with
      | absent absent => exact absent ⟨span, marker.1⟩
      | present _ otherMarker parsed =>
          cases marker.output_unique otherMarker
          exact rejection.disjoint_success successUnique disjoint ⟨_, _, _, parsed⟩

theorem FunctionReturnsTraceRejects.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (successProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionReturnsTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | present _ _ values => exact values.cascadeFilters successProtected rejectProtected

theorem functionReturnsTraceExactOutcomeSpec
    (types : TraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    TraceExactOutcomeSpec (FunctionReturnsTraceParses elementTrace)
      (FunctionReturnsTraceRejects elementTrace elementRejects) source endByte where
  successResultUnique := FunctionReturnsTraceParses.result_unique types.successResultUnique
  rejectResultUnique := FunctionReturnsTraceRejects.result_unique
    types.successResultUnique types.rejectResultUnique types.successRejectDisjoint
  successRejectDisjoint := FunctionReturnsTraceRejects.disjoint_success
    types.successResultUnique types.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
