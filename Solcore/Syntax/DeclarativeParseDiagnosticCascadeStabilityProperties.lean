import Solcore.Syntax.DeclarativeParseDiagnosticCascadeProperties

/-! Normalized diagnostic traces are stable under the same lexical context. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every retained report lacks an independent suppression witness. -/
theorem ParseDiagnosticCascadeFilters.retained_not_suppressed
    {source : String} {lexical : List SourceSpan} {raw kept : List ParseDiagnostic}
    (filtered : ParseDiagnosticCascadeFilters source lexical raw kept) :
    ∀ diagnostic ∈ kept, ¬ ParseDiagnosticCascadeSuppresses source lexical diagnostic := by
  induction filtered with
  | nil => simp
  | keep retained tail ih =>
      intro diagnostic member
      rcases List.mem_cons.mp member with rfl | inTail
      · exact retained
      · exact ih diagnostic inTail
  | drop suppressed tail ih => exact ih

/-- A trace consisting entirely of retained reports normalizes to itself. -/
theorem parseDiagnosticCascadeFilters_of_retained (source : String)
    (lexical : List SourceSpan) {trace : List ParseDiagnostic}
    (retained : ∀ diagnostic ∈ trace,
      ¬ ParseDiagnosticCascadeSuppresses source lexical diagnostic) :
    ParseDiagnosticCascadeFilters source lexical trace trace := by
  induction trace with
  | nil => exact .nil
  | cons diagnostic trace ih =>
      exact .keep (retained diagnostic (by simp))
        (ih (fun member found => retained member (List.mem_cons_of_mem _ found)))

/-- Reapplying normalization cannot delete a previously retained occurrence. -/
theorem ParseDiagnosticCascadeFilters.stable
    {source : String} {lexical : List SourceSpan} {raw kept : List ParseDiagnostic}
    (filtered : ParseDiagnosticCascadeFilters source lexical raw kept) :
    ParseDiagnosticCascadeFilters source lexical kept kept :=
  parseDiagnosticCascadeFilters_of_retained source lexical filtered.retained_not_suppressed

end Solcore.Syntax.DeclarativeGrammar
