import Solcore.Syntax.DeclarativeProxyTypeTraceGrammar
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties
import Solcore.Syntax.DeclarativeParseDiagnosticCascadeProperties

/-! Independent raw structure, ordinary erasure, uniqueness, and protection.
Carrier preservation and progress each require their explicit child law;
neither is hidden in the trace relation or its execution contracts. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem ProxyTypeTraceParses.marker_present
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ProxyTypeTraceParses typeTrace source endByte input value output trace) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .at } := by
  cases parsed with
  | parsed span marker _ => exact ⟨span, marker.1⟩

theorem ProxyTypeTraceParses.ordinary_components
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    (erases : ∀ {input value output trace},
      typeTrace source endByte input value output trace → typeOrdinary input value output)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ProxyTypeTraceParses typeTrace source endByte input value output trace) :
    ∃ markerSpan afterMarker inner,
      ExactTokenParses (.symbol .at) input markerSpan afterMarker ∧
      typeOrdinary afterMarker inner output ∧
      value = { span := SourceSpan.cover markerSpan inner.span, value := .proxy markerSpan inner } := by
  cases parsed with
  | parsed span marker typed => exact ⟨span, _, _, marker, erases typed, rfl⟩

theorem ProxyTypeTraceParses.ordinary
    (erases : ∀ {input value output trace},
      typeTrace source endByte input value output trace → TypeExprParses input value output)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ProxyTypeTraceParses typeTrace source endByte input value output trace) :
    TypeExprParses input value output := by
  cases parsed with
  | parsed span marker typed => exact .proxy span marker rfl (erases typed)

theorem ProxyTypeTraceParses.output_window
    (childWindow : ∀ {input value output trace},
      typeTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ProxyTypeTraceParses typeTrace source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed span marker typed => simpa only [marker.2] using childWindow typed

theorem ProxyTypeTraceParses.cursor_lt
    (childProgress : ∀ {input value output trace},
      typeTrace source endByte input value output trace → input.cursor ≤ output.cursor)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ProxyTypeTraceParses typeTrace source endByte input value output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed span marker typed =>
      have progress := childProgress typed
      rw [marker.2] at progress
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) progress

theorem ProxyTypeTraceParses.result_unique
    (unique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      typeTrace source endByte input left afterLeft leftTrace →
      typeTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Syntax.TypeExpr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ProxyTypeTraceParses typeTrace source endByte input left afterLeft leftTrace)
    (rightParsed : ProxyTypeTraceParses typeTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed span marker typed =>
      cases rightParsed with
      | parsed otherSpan otherMarker otherTyped =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          rcases unique typed otherTyped with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem ProxyTypeTraceParses.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (childProtected : ∀ {input value output trace},
      typeTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ProxyTypeTraceParses typeTrace source endByte input value output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed _ _ typed => exact childProtected typed

end Solcore.Syntax.DeclarativeGrammar
