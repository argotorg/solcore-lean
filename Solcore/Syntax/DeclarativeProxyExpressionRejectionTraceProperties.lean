import Solcore.Syntax.DeclarativeProxyExpressionRejectionTraceGrammar
import Solcore.Syntax.DeclarativeProxyExpressionTraceProperties
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties
import Solcore.Syntax.DeclarativeTraceOutcomeSpec

/-! Independent raw rejection erasure, exactness, and event protection. The
older selected relation needs a marker guard; the outcome bundle proves only
uniqueness and disjointness, never type-parser totality or silent diagnostics. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop}
  {typeRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem ProxyExpressionTraceRejects.ordinary_cases
    {ordinaryRejects : Remainder → Remainder → Prop}
    (erases : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace → ordinaryRejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ProxyExpressionTraceRejects typeRejects source endByte input rejected report trace) :
    (TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .at) ∧ rejected = input) ∨
      ProxyExpressionRejects ordinaryRejects input rejected := by
  cases rejection with
  | markerMissing absent _ => exact .inl ⟨absent, rfl⟩
  | typeRejected span marker typed => exact .inr (.typeRejected span marker (erases typed))

theorem ProxyExpressionTraceRejects.ordinary_of_marker_present
    {ordinaryRejects : Remainder → Remainder → Prop}
    (erases : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace → ordinaryRejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (selected : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .at })
    (rejection : ProxyExpressionTraceRejects typeRejects source endByte input rejected report trace) :
    ProxyExpressionRejects ordinaryRejects input rejected := by
  rcases rejection.ordinary_cases erases with missing | ordinary
  · exact False.elim (missing.1 selected)
  · exact ordinary

theorem ProxyExpressionTraceRejects.result_unique
    (unique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
      typeRejects source endByte input afterLeft leftReport leftTrace →
      typeRejects source endByte input afterRight rightReport rightTrace →
        afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : ProxyExpressionTraceRejects typeRejects source endByte input afterLeft leftReport leftTrace)
    (right : ProxyExpressionTraceRejects typeRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | markerMissing absent reported =>
      cases right with
      | markerMissing _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | typeRejected span marker _ => exact False.elim (absent ⟨span, marker.1⟩)
  | typeRejected span marker typed =>
      cases right with
      | markerMissing absent _ => exact False.elim (absent ⟨span, marker.1⟩)
      | typeRejected _ otherMarker other =>
          cases marker.output_unique otherMarker
          exact unique typed other

theorem ProxyExpressionTraceRejects.disjoint_success
    (disjoint : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace →
        ¬ ∃ value output events, typeTrace source endByte input value output events)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ProxyExpressionTraceRejects typeRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, ProxyExpressionTraceParses typeTrace source endByte input value output events := by
  rintro ⟨_, _, _, success⟩
  cases success with
  | parsed span marker typed =>
      cases rejection with
      | markerMissing absent _ => exact absent ⟨span, marker.1⟩
      | typeRejected _ otherMarker rejectedType =>
          cases marker.output_unique otherMarker
          exact disjoint rejectedType ⟨_, _, _, typed⟩

theorem ProxyExpressionTraceRejects.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (childProtected : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ProxyExpressionTraceRejects typeRejects source endByte input rejected report trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | markerMissing => exact .nil
  | typeRejected _ _ typed => exact childProtected typed

theorem proxyExpressionTraceExactOutcomeSpec
    (types : TraceExactOutcomeSpec typeTrace typeRejects source endByte) :
    ExpressionTraceExactOutcomeSpec (ProxyExpressionTraceParses typeTrace)
      (ProxyExpressionTraceRejects typeRejects) source endByte where
  successResultUnique := ProxyExpressionTraceParses.result_unique types.successResultUnique
  rejectResultUnique := ProxyExpressionTraceRejects.result_unique types.rejectResultUnique
  successRejectDisjoint := ProxyExpressionTraceRejects.disjoint_success types.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
