import Solcore.Syntax.DeclarativeTypeExprTraceInductionProperties
import Solcore.Syntax.DeclarativeTypeDispatchTraceOrdinaryProperties

/-! Fuel-free recursive trace structure: successful ordinary erasure preserves
the complete token carrier and active end index; both outcomes retain protected
events. These laws do not assert execution, completeness, or outcome existence. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private def successStructure : TypeTraceQuery → Prop
  | .success _ _ input value output _ =>
      TypeExprParses input value output ∧
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex
  | .rejection _ _ _ _ _ _ => True

private theorem successStructure_closed (query : TypeTraceQuery)
    (step : TypeTraceLayer successStructure query) : successStructure query := by
  cases query with
  | success source endByte input value output trace =>
      exact ⟨TypeDispatchTraceParses.ordinary (fun child => child.1)
        (fun child => child.2) step,
        TypeDispatchTraceParses.output_window (fun child => child.2) step⟩
  | rejection => trivial

theorem TypeExprTraceParses.ordinary
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TypeExprTraceParses source endByte input value output trace) :
    TypeExprParses input value output :=
  (TypeTraceLeast.induction successStructure_closed parsed).1

theorem TypeExprTraceParses.output_window
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TypeExprTraceParses source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex :=
  (TypeTraceLeast.induction successStructure_closed parsed).2

private def protectedEvents (text : String) (lexical : List SourceSpan) : TypeTraceQuery → Prop
  | .success _ _ _ _ _ trace => ParseDiagnosticCascadeFilters text lexical trace trace
  | .rejection _ _ _ _ _ trace => ParseDiagnosticCascadeFilters text lexical trace trace

private theorem protectedEvents_closed (text : String) (lexical : List SourceSpan)
    (query : TypeTraceQuery) (step : TypeTraceLayer (protectedEvents text lexical) query) :
    protectedEvents text lexical query := by
  cases query with
  | success => exact TypeDispatchTraceParses.cascadeFilters (fun child => child) step
  | rejection => exact TypeDispatchTraceRejects.cascadeFilters (fun child => child) (fun child => child) step

theorem TypeExprTraceParses.cascadeFilters
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TypeExprTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace :=
  TypeTraceLeast.induction (protectedEvents_closed text lexical) parsed

theorem TypeExprTraceRejects.cascadeFilters
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TypeExprTraceRejects source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace :=
  TypeTraceLeast.induction (protectedEvents_closed text lexical) rejection

end Solcore.Syntax.DeclarativeGrammar
