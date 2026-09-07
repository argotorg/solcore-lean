import Solcore.Syntax.DeclarativeTypeExprTraceGrammar
import Solcore.Syntax.DeclarativeTypeDispatchTraceMonotonicityProperties

/-! The fixed type layer is monotone and its least relation supports exact
rolling/unrolling and simultaneous induction. Strong induction retains each
child's original derivation alongside the chosen induction property. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem TypeTraceLayer.mono {left right : TypeTraceQuery → Prop}
    (childMap : ∀ query, left query → right query) (query : TypeTraceQuery)
    (step : TypeTraceLayer left query) : TypeTraceLayer right query := by
  cases query with
  | success source endByte input value output trace =>
      exact TypeDispatchTraceParses.mono
        (fun {input value output trace} parsed =>
          childMap (.success source endByte input value output trace) parsed) step
  | rejection source endByte input rejected report trace =>
      exact TypeDispatchTraceRejects.mono
        (fun {input value output trace} parsed =>
          childMap (.success source endByte input value output trace) parsed)
        (fun {input rejected report trace} rejectedChild =>
          childMap (.rejection source endByte input rejected report trace) rejectedChild) step

theorem TypeTraceLeast.induction
    {candidate : TypeTraceQuery → Prop}
    (closed : ∀ query, TypeTraceLayer candidate query → candidate query)
    {query : TypeTraceQuery} (derivation : TypeTraceLeast query) : candidate query :=
  derivation candidate closed

theorem TypeTraceLeast.roll {query : TypeTraceQuery}
    (step : TypeTraceLayer TypeTraceLeast query) : TypeTraceLeast query := by
  intro candidate closed
  exact closed query (TypeTraceLayer.mono (fun _ derivation => derivation candidate closed) query step)

theorem TypeTraceLeast.unroll {query : TypeTraceQuery}
    (derivation : TypeTraceLeast query) : TypeTraceLayer TypeTraceLeast query := by
  apply derivation (TypeTraceLayer TypeTraceLeast)
  intro next step
  exact TypeTraceLayer.mono (fun _ nested => TypeTraceLeast.roll nested) next step

theorem TypeTraceLeast.strong_induction
    {candidate : TypeTraceQuery → Prop}
    (closed : ∀ query, TypeTraceLayer (fun query => TypeTraceLeast query ∧ candidate query) query → candidate query)
    {query : TypeTraceQuery} (derivation : TypeTraceLeast query) : candidate query := by
  have both : TypeTraceLeast query ∧ candidate query := derivation
    (fun query => TypeTraceLeast query ∧ candidate query) (by
    intro next step
    exact ⟨TypeTraceLeast.roll (TypeTraceLayer.mono (fun _ pair => pair.1) next step), closed next step⟩)
  exact both.2

theorem TypeExprTraceParses.unroll_iff {source : SourceId} {endByte : Nat}
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic} :
    TypeExprTraceParses source endByte input value output trace ↔
      TypeDispatchTraceParses TypeExprTraceParses source endByte input value output trace := by
  change TypeTraceLeast (.success source endByte input value output trace) ↔
    TypeTraceLayer TypeTraceLeast (.success source endByte input value output trace)
  exact ⟨TypeTraceLeast.unroll, TypeTraceLeast.roll⟩

theorem TypeExprTraceRejects.unroll_iff {source : SourceId} {endByte : Nat}
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    TypeExprTraceRejects source endByte input rejected report trace ↔
      TypeDispatchTraceRejects TypeExprTraceParses TypeExprTraceRejects
        source endByte input rejected report trace := by
  change TypeTraceLeast (.rejection source endByte input rejected report trace) ↔
    TypeTraceLayer TypeTraceLeast (.rejection source endByte input rejected report trace)
  exact ⟨TypeTraceLeast.unroll, TypeTraceLeast.roll⟩

theorem TypeExprTraceParses.roll {source : SourceId} {endByte : Nat}
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (step : TypeDispatchTraceParses TypeExprTraceParses source endByte input value output trace) :
    TypeExprTraceParses source endByte input value output trace :=
  TypeExprTraceParses.unroll_iff.mpr step

theorem TypeExprTraceRejects.roll {source : SourceId} {endByte : Nat}
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (step : TypeDispatchTraceRejects TypeExprTraceParses TypeExprTraceRejects
      source endByte input rejected report trace) :
    TypeExprTraceRejects source endByte input rejected report trace :=
  TypeExprTraceRejects.unroll_iff.mpr step

end Solcore.Syntax.DeclarativeGrammar
