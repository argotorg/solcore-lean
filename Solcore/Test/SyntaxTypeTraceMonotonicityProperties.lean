import Solcore.Syntax.DeclarativeTypeDispatchTraceMonotonicityProperties
import Solcore.Syntax.DeclarativeTypeDispatchTraceProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties

/-! Forgetting child proof annotations does not forget any diagnostic event.
The enriched relation simultaneously supplies an exact underlying type trace
and duplicate-preserving normalization after arbitrary earlier reports. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxTypeTraceMonotonicityProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

variable
  {elementTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem success_forgets_annotations_but_keeps_events
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {input output : Remainder} {value : TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TypeDispatchTraceParses
      (fun source endByte input value output trace =>
        elementTrace source endByte input value output trace ∧
          ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
      source endByte input value output trace) :
    TypeDispatchTraceParses elementTrace source endByte input value output trace ∧
      filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  refine ⟨parsed.mono (fun child => child.1), ?_⟩
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical (parsed.cascadeFilters (fun child => child.2)))

theorem rejection_forgets_annotations_but_keeps_report_and_events
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TypeDispatchTraceRejects
      (fun source endByte input value output trace =>
        elementTrace source endByte input value output trace ∧
          ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
      (fun source endByte input rejected report trace =>
        elementRejects source endByte input rejected report trace ∧
          ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
      source endByte input rejected report trace) :
    TypeDispatchTraceRejects elementTrace elementRejects source endByte input rejected report trace ∧
      filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  refine ⟨rejection.mono (fun child => child.1) (fun child => child.1), ?_⟩
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical
      (rejection.cascadeFilters (fun child => child.2) (fun child => child.2)))

end Solcore.Test.SyntaxTypeTraceMonotonicityProperties
