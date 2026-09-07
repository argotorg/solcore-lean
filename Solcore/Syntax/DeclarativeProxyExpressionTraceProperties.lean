import Solcore.Syntax.DeclarativeProxyExpressionTraceGrammar
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties
import Solcore.Syntax.DeclarativeParseDiagnosticCascadeProperties

/-! Structure, exactness, and protected-event composition are separate laws.
Ordinary erasure needs no token law; progress and carrier preservation explicitly
depend on the corresponding child laws, not on a validity assumption. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem ProxyExpressionTraceParses.marker_present
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ProxyExpressionTraceParses typeTrace source endByte input value output trace) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .at } := by
  cases parsed with
  | parsed span marker _ => exact ⟨span, marker.1⟩

theorem ProxyExpressionTraceParses.ordinary
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    (erases : ∀ {input value output trace},
      typeTrace source endByte input value output trace → typeOrdinary input value output)
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ProxyExpressionTraceParses typeTrace source endByte input value output trace) :
    ProxyExpressionOrdinaryParses typeOrdinary input value output := by
  cases parsed with
  | parsed span marker typed => exact .parsed span marker (erases typed)

theorem ProxyExpressionTraceParses.output_window
    (childWindow : ∀ {input value output trace},
      typeTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ProxyExpressionTraceParses typeTrace source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed span marker typed => simpa only [marker.2] using childWindow typed

theorem ProxyExpressionTraceParses.cursor_lt
    (childProgress : ∀ {input value output trace},
      typeTrace source endByte input value output trace → input.cursor ≤ output.cursor)
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ProxyExpressionTraceParses typeTrace source endByte input value output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed span marker typed =>
      have progress := childProgress typed
      rw [marker.2] at progress
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) progress

theorem ProxyExpressionTraceParses.result_unique
    (unique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      typeTrace source endByte input left afterLeft leftTrace →
      typeTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Syntax.Expr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ProxyExpressionTraceParses typeTrace source endByte input left afterLeft leftTrace)
    (rightParsed : ProxyExpressionTraceParses typeTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed span marker typed =>
      cases rightParsed with
      | parsed otherSpan otherMarker otherTyped =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          rcases unique typed otherTyped with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem ProxyExpressionTraceParses.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (childProtected : ∀ {input value output trace},
      typeTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ProxyExpressionTraceParses typeTrace source endByte input value output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed _ _ typed => exact childProtected typed

end Solcore.Syntax.DeclarativeGrammar
