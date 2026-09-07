import Solcore.Syntax.DeclarativeCoreBlockTailTraceGrammar
import Solcore.Syntax.DeclarativeParseDiagnosticCascadeProperties

/-! Total, unique, protected statement-termination traces. Empty traces recover
the existing diagnostic-free tail predicate without imposing it on all parses. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every statement has a mandatory-termination diagnostic trace. -/
theorem CoreBlockStatementDiagnosticTrace.exists_trace (statement : Syntax.Statement) :
    ∃ trace, CoreBlockStatementDiagnosticTrace statement trace := by
  classical
  by_cases terminated : CoreBlockStatementTerminated statement
  · exact ⟨[], .clean terminated⟩
  · exact ⟨_, .missing terminated⟩

/-- The statement's own span and termination status determine its entire trace. -/
theorem CoreBlockStatementDiagnosticTrace.output_unique
    {statement : Syntax.Statement} {left right : List ParseDiagnostic}
    (leftParsed : CoreBlockStatementDiagnosticTrace statement left)
    (rightParsed : CoreBlockStatementDiagnosticTrace statement right) : left = right := by
  cases leftParsed with
  | clean terminated =>
      cases rightParsed with
      | clean => rfl
      | missing absent => exact False.elim (absent terminated)
  | missing absent =>
      cases rightParsed with
      | clean terminated => exact False.elim (absent terminated)
      | missing => rfl

/-- A mandatory check is silent exactly when statement termination is valid. -/
theorem CoreBlockStatementDiagnosticTrace.empty_iff
    {statement : Syntax.Statement} {trace : List ParseDiagnostic}
    (parsed : CoreBlockStatementDiagnosticTrace statement trace) :
    trace = [] ↔ CoreBlockStatementTerminated statement := by
  cases parsed with
  | clean terminated => exact ⟨fun _ => terminated, fun _ => rfl⟩
  | missing absent => simp only [List.cons_ne_self, false_iff]; exact absent

/-- Constraint reports are protected regardless of the lexical error context. -/
theorem CoreBlockStatementDiagnosticTrace.cascadeFilters
    {statement : Syntax.Statement} {trace : List ParseDiagnostic}
    (parsed : CoreBlockStatementDiagnosticTrace statement trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | clean => exact .nil
  | missing => exact .keep (fun suppressed => suppressed.1) .nil

/-- Every statement list and final-expression policy has a complete trace. -/
theorem CoreBlockTailsDiagnosticTrace.exists_trace
    (policy : CoreBlockTailPolicy) (statements : List Syntax.Statement) :
    ∃ trace, CoreBlockTailsDiagnosticTrace policy statements trace := by
  induction statements with
  | nil => exact ⟨[], .nil⟩
  | cons first rest ih =>
      cases rest with
      | nil =>
          cases policy with
          | allow => exact ⟨[], .lastAllowed⟩
          | require =>
              rcases CoreBlockStatementDiagnosticTrace.exists_trace first with ⟨trace, parsed⟩
              exact ⟨trace, .lastRequired parsed⟩
      | cons second rest =>
          rcases CoreBlockStatementDiagnosticTrace.exists_trace first with ⟨headTrace, head⟩
          rcases ih with ⟨tailTrace, tail⟩
          exact ⟨headTrace ++ tailTrace, .cons head tail⟩

/-- Tail validation has exactly one ordered trace, including all duplicates. -/
theorem CoreBlockTailsDiagnosticTrace.output_unique
    {policy : CoreBlockTailPolicy} {statements : List Syntax.Statement}
    {left right : List ParseDiagnostic}
    (leftParsed : CoreBlockTailsDiagnosticTrace policy statements left)
    (rightParsed : CoreBlockTailsDiagnosticTrace policy statements right) : left = right := by
  induction leftParsed generalizing right with
  | nil => cases rightParsed; rfl
  | lastAllowed => cases rightParsed; rfl
  | lastRequired checked =>
      cases rightParsed with
      | lastRequired other => exact checked.output_unique other
  | cons checked tail ih =>
      cases rightParsed with
      | cons other otherTail => rw [checked.output_unique other, ih otherTail]

/-- A complete trace is empty precisely under the original tail-validity
predicate, including the exemption for the final allowed expression. -/
theorem CoreBlockTailsDiagnosticTrace.empty_iff
    {policy : CoreBlockTailPolicy} {statements : List Syntax.Statement}
    {trace : List ParseDiagnostic}
    (parsed : CoreBlockTailsDiagnosticTrace policy statements trace) :
    trace = [] ↔ CoreBlockTailsValid policy statements := by
  induction parsed with
  | nil => simp only [CoreBlockTailsValid, iff_self]
  | lastAllowed => simp only [CoreBlockTailsValid, iff_self]
  | lastRequired checked => exact checked.empty_iff
  | cons checked tail ih =>
      simp only [List.append_eq_nil_iff, checked.empty_iff, ih, CoreBlockTailsValid]

/-- Every emitted constraint survives lexical normalization in source order. -/
theorem CoreBlockTailsDiagnosticTrace.cascadeFilters
    {policy : CoreBlockTailPolicy} {statements : List Syntax.Statement}
    {trace : List ParseDiagnostic}
    (parsed : CoreBlockTailsDiagnosticTrace policy statements trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  induction parsed with
  | nil | lastAllowed => exact .nil
  | lastRequired checked => exact checked.cascadeFilters text lexical
  | cons checked tail ih => exact (checked.cascadeFilters text lexical).append ih

end Solcore.Syntax.DeclarativeGrammar
