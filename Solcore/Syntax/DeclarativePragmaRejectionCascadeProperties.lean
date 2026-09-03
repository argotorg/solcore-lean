import Solcore.Syntax.DeclarativePragmaRejectionTraceProperties

/-! Independent filtering after a caller commits a pragma's failure report.
The rejecting grammar's raw trace still excludes that report; only the explicit
appended event is classified here. Every earlier protected occurrence is kept. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Committing an unsuppressed failure appends it after every protected event,
without collapsing equal reports or changing their metadata. -/
theorem PragmaDeclTraceRejects.committedCascadeFilters_of_retained
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : PragmaDeclTraceRejects source endByte input rejected diagnostic trace)
    (text : String) (lexical : List SourceSpan)
    (retained : ¬ ParseDiagnosticCascadeSuppresses text lexical diagnostic) :
    ParseDiagnosticCascadeFilters text lexical
      (trace ++ [diagnostic]) (trace ++ [diagnostic]) :=
  (traced.cascadeFilters text lexical).append (.keep retained .nil)

/-- Suppression removes only the newly committed failure, never the earlier
checked-item trace, even when it contains repeated identical reports. -/
theorem PragmaDeclTraceRejects.committedCascadeFilters_of_suppressed
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : PragmaDeclTraceRejects source endByte input rejected diagnostic trace)
    (text : String) (lexical : List SourceSpan)
    (suppressed : ParseDiagnosticCascadeSuppresses text lexical diagnostic) :
    ParseDiagnosticCascadeFilters text lexical (trace ++ [diagnostic]) trace := by
  simpa only [List.append_nil] using
    (traced.cascadeFilters text lexical).append (.drop suppressed .nil)

/-- Exact classification of a committed rejection: all raw prefix events
survive, and only the final full failure report may be suppressed. -/
theorem PragmaDeclTraceRejects.committedCascadeFilters_iff
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace kept : List ParseDiagnostic}
    (traced : PragmaDeclTraceRejects source endByte input rejected diagnostic trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical (trace ++ [diagnostic]) kept ↔
      (¬ ParseDiagnosticCascadeSuppresses text lexical diagnostic ∧
        kept = trace ++ [diagnostic]) ∨
      (ParseDiagnosticCascadeSuppresses text lexical diagnostic ∧ kept = trace) := by
  classical
  constructor
  · intro filtered
    by_cases suppressed : ParseDiagnosticCascadeSuppresses text lexical diagnostic
    · exact Or.inr ⟨suppressed, filtered.output_unique
        (traced.committedCascadeFilters_of_suppressed text lexical suppressed)⟩
    · exact Or.inl ⟨suppressed, filtered.output_unique
        (traced.committedCascadeFilters_of_retained text lexical suppressed)⟩
  · rintro (⟨retained, rfl⟩ | ⟨suppressed, rfl⟩)
    · exact traced.committedCascadeFilters_of_retained text lexical retained
    · exact traced.committedCascadeFilters_of_suppressed text lexical suppressed

end Solcore.Syntax.DeclarativeGrammar
