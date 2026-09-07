import Solcore.Syntax.DeclarativeTypeDispatchTraceProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties

/-! Conditional protection lifts through every selected raw form without
reordering or deduplicating the event suffix. Final reports are uncommitted;
the final branch contributes an empty suffix for every nested trace relation. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedTypeDispatchTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

variable
  {elementTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem success_keeps_protected_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {value : TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TypeDispatchTraceParses elementTrace source endByte input value output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical (parsed.cascadeFilters childProtected))

theorem rejection_keeps_protected_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (successProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    (rejectProtected : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TypeDispatchTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical
      (rejection.cascadeFilters successProtected rejectProtected))

theorem final_report_contributes_no_event
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (selection : TypeDispatchSelects input .final)
    (rejection : TypeDispatchTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    rejected = input ∧ trace = [] ∧
      filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior := by
  rcases (TypeDispatchTraceRejects.final_iff selection).mp rejection with ⟨rfl, _, rfl⟩
  exact ⟨rfl, rfl, by simp only [List.append_nil]⟩

end Solcore.Test.SyntaxProtectedTypeDispatchTraceProperties
