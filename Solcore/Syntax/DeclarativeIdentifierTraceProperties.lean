import Solcore.Syntax.DeclarativeIdentifierTraceGrammar
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact identifier values, endpoints, and spelling-dependent event sequences. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Character membership agrees with the executable spelling test. -/
theorem identifierHyphenSpelling_iff_contains (text : String) :
    IdentifierHyphenSpelling text ↔ text.toList.contains '-' = true := by
  simp [IdentifierHyphenSpelling]

/-- Every identifier spelling selects one complete diagnostic sequence. -/
theorem identifierDiagnosticTrace_total (name : Syntax.Identifier) :
    ∃ trace, IdentifierDiagnosticTrace name trace := by
  by_cases hyphen : IdentifierHyphenSpelling name.value
  · exact ⟨_, .hyphen hyphen⟩
  · exact ⟨_, .clean hyphen⟩

/-- The spelling determines the complete diagnostic sequence uniquely. -/
theorem IdentifierDiagnosticTrace.trace_unique {name : Syntax.Identifier}
    {left right : List ParseDiagnostic}
    (leftTrace : IdentifierDiagnosticTrace name left)
    (rightTrace : IdentifierDiagnosticTrace name right) : left = right := by
  cases leftTrace <;> cases rightTrace <;> first | rfl | contradiction

/-- Raw trace erasure preserves the existing token grammar and empty trace. -/
theorem rawIdentifierTraceParses_iff
    {input output : Remainder} {name : Syntax.Identifier}
    {trace : List ParseDiagnostic} :
    RawIdentifierTraceParses input name output trace ↔
      IdentifierParses input name output ∧ trace = [] := by
  constructor
  · intro parsed
    cases parsed with
    | parsed ordinary => exact ⟨ordinary, rfl⟩
  · rintro ⟨ordinary, rfl⟩
    exact .parsed ordinary

/-- Checked trace erasure preserves both token and spelling evidence. -/
theorem identifierTraceParses_iff
    {input output : Remainder} {name : Syntax.Identifier}
    {trace : List ParseDiagnostic} :
    IdentifierTraceParses input name output trace ↔
      IdentifierParses input name output ∧ IdentifierDiagnosticTrace name trace := by
  constructor
  · intro parsed
    cases parsed with
    | parsed ordinary diagnostics => exact ⟨ordinary, diagnostics⟩
  · rintro ⟨ordinary, diagnostics⟩
    exact .parsed ordinary diagnostics

/-- A raw token derivation fixes its full AST, remainder, and trace. -/
theorem RawIdentifierTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.Identifier}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : RawIdentifierTraceParses input left afterLeft leftTrace)
    (rightParsed : RawIdentifierTraceParses input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed leftOrdinary =>
      cases rightParsed with
      | parsed rightOrdinary =>
          rcases leftOrdinary.result_unique rightOrdinary with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

/-- Checked identifiers also fix every located diagnostic event exactly. -/
theorem IdentifierTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.Identifier}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : IdentifierTraceParses input left afterLeft leftTrace)
    (rightParsed : IdentifierTraceParses input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed leftOrdinary leftDiagnostics =>
      cases rightParsed with
      | parsed rightOrdinary rightDiagnostics =>
          rcases leftOrdinary.result_unique rightOrdinary with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, leftDiagnostics.trace_unique rightDiagnostics⟩

end Solcore.Syntax.DeclarativeGrammar
