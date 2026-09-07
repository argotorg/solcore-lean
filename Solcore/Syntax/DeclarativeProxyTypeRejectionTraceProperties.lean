import Solcore.Syntax.DeclarativeProxyTypeRejectionTraceGrammar
import Solcore.Syntax.DeclarativeProxyTypeTraceProperties
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties
import Solcore.Syntax.DeclarativeTraceOutcomeSpec

/-! Independent raw rejection erasure, exactness, and event protection. The
older selected relation needs a marker guard; the outcome bundle proves only
uniqueness and disjointness, never nested-parser totality or silent diagnostics. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop}
  {typeRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem ProxyTypeTraceRejects.ordinary_cases
    {ordinaryRejects : Remainder → Remainder → Prop}
    (erases : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace → ordinaryRejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ProxyTypeTraceRejects typeRejects source endByte input rejected report trace) :
    (TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .at) ∧ rejected = input) ∨
      ProxyTypeRejects ordinaryRejects input rejected := by
  cases rejection with
  | markerMissing absent _ => exact .inl ⟨absent, rfl⟩
  | innerRejected span marker typed => exact .inr (.innerRejected span marker (erases typed))

theorem ProxyTypeTraceRejects.ordinary_of_marker_present
    {ordinaryRejects : Remainder → Remainder → Prop}
    (erases : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace → ordinaryRejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (selected : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .at })
    (rejection : ProxyTypeTraceRejects typeRejects source endByte input rejected report trace) :
    ProxyTypeRejects ordinaryRejects input rejected := by
  rcases rejection.ordinary_cases erases with missing | ordinary
  · exact False.elim (missing.1 selected)
  · exact ordinary

theorem ProxyTypeTraceRejects.result_unique
    (unique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
      typeRejects source endByte input afterLeft leftReport leftTrace →
      typeRejects source endByte input afterRight rightReport rightTrace →
        afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : ProxyTypeTraceRejects typeRejects source endByte input afterLeft leftReport leftTrace)
    (right : ProxyTypeTraceRejects typeRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | markerMissing absent reported =>
      cases right with
      | markerMissing _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | innerRejected span marker _ => exact False.elim (absent ⟨span, marker.1⟩)
  | innerRejected span marker typed =>
      cases right with
      | markerMissing absent _ => exact False.elim (absent ⟨span, marker.1⟩)
      | innerRejected _ otherMarker other =>
          cases marker.output_unique otherMarker
          exact unique typed other

theorem ProxyTypeTraceRejects.disjoint_success
    (disjoint : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace →
        ¬ ∃ value output events, typeTrace source endByte input value output events)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ProxyTypeTraceRejects typeRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, ProxyTypeTraceParses typeTrace source endByte input value output events := by
  rintro ⟨_, _, _, success⟩
  cases success with
  | parsed span marker typed =>
      cases rejection with
      | markerMissing absent _ => exact absent ⟨span, marker.1⟩
      | innerRejected _ otherMarker rejectedType =>
          cases marker.output_unique otherMarker
          exact disjoint rejectedType ⟨_, _, _, typed⟩

theorem ProxyTypeTraceRejects.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (childProtected : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ProxyTypeTraceRejects typeRejects source endByte input rejected report trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | markerMissing => exact .nil
  | innerRejected _ _ typed => exact childProtected typed

theorem proxyTypeTraceExactOutcomeSpec
    (types : TraceExactOutcomeSpec typeTrace typeRejects source endByte) :
    TraceExactOutcomeSpec (ProxyTypeTraceParses typeTrace)
      (ProxyTypeTraceRejects typeRejects) source endByte where
  successResultUnique := ProxyTypeTraceParses.result_unique types.successResultUnique
  rejectResultUnique := ProxyTypeTraceRejects.result_unique types.rejectResultUnique
  successRejectDisjoint := ProxyTypeTraceRejects.disjoint_success types.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
