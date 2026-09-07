import Solcore.Syntax.DeclarativeComptimeTypeTraceGrammar
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties
import Solcore.Syntax.DeclarativeParseDiagnosticCascadeProperties

/-! Independent raw structure, erasure, exactness, and protected events.
Carrier preservation and progress are separate child laws, not grammar guards. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem ComptimeTypeTraceParses.ordinary_components
    {ordinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    (erases : ∀ {input value output trace},
      elementTrace source endByte input value output trace → ordinary input value output)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ComptimeTypeTraceParses elementTrace source endByte input value output trace) :
    ∃ markerSpan openingSpan closingSpan afterMarker afterOpening afterInner inner,
      ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker ∧
      ExactTokenParses (.symbol .less) afterMarker openingSpan afterOpening ∧
      ordinary afterOpening inner afterInner ∧
      ExactTokenParses (.symbol .greater) afterInner closingSpan output ∧
      value = comptimeTypeTraceValue markerSpan openingSpan closingSpan inner := by
  cases parsed with
  | parsed m o c marker opening typed closing => exact ⟨m, o, c, _, _, _, _, marker, opening, erases typed, closing, rfl⟩

theorem ComptimeTypeTraceParses.ordinary
    (erases : ∀ {input value output trace},
      elementTrace source endByte input value output trace → TypeExprParses input value output)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ComptimeTypeTraceParses elementTrace source endByte input value output trace) :
    TypeExprParses input value output := by
  cases parsed with
  | parsed m o c marker opening typed closing => exact .comptime m o c marker opening closing rfl (erases typed)

theorem ComptimeTypeTraceParses.output_window
    (childWindow : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ComptimeTypeTraceParses elementTrace source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed m o c marker opening typed closing =>
      simpa only [closing.2, opening.2, marker.2] using childWindow typed

theorem ComptimeTypeTraceParses.cursor_lt
    (childProgress : ∀ {input value output trace},
      elementTrace source endByte input value output trace → input.cursor ≤ output.cursor)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ComptimeTypeTraceParses elementTrace source endByte input value output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed m o c marker opening typed closing =>
      have progress := childProgress typed
      rw [opening.2, marker.2] at progress
      change input.cursor + 1 + 1 ≤ _ at progress
      rw [closing.2]
      change input.cursor < _ + 1
      omega

theorem ComptimeTypeTraceParses.result_unique
    (unique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Syntax.TypeExpr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ComptimeTypeTraceParses elementTrace source endByte input left afterLeft leftTrace)
    (rightParsed : ComptimeTypeTraceParses elementTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed m o c marker opening typed closing =>
      cases rightParsed with
      | parsed m' o' c' marker' opening' typed' closing' =>
          rcases marker.result_unique marker' with ⟨rfl, rfl⟩
          rcases opening.result_unique opening' with ⟨rfl, rfl⟩
          rcases unique typed typed' with ⟨rfl, rfl, rfl⟩
          rcases closing.result_unique closing' with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem ComptimeTypeTraceParses.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (childProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ComptimeTypeTraceParses elementTrace source endByte input value output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed _ _ _ _ _ typed _ => exact childProtected typed

end Solcore.Syntax.DeclarativeGrammar
