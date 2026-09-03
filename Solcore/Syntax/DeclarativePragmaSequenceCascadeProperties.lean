import Solcore.Syntax.DeclarativePragmaSequenceTraceGrammar
import Solcore.Syntax.DeclarativePragmaCascadeProperties

/-! Every event in an independently parsed pragma sequence is protected from
lexical-cascade suppression. Empty sequences and repeated events are retained. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordered concatenation of pragma traces preserves every complete report. -/
theorem PragmaSequenceTraceParses.cascadeFilters
    {input output : Remainder} {declarations : List Syntax.PragmaDecl}
    {trace : List ParseDiagnostic}
    (parsed : PragmaSequenceTraceParses input declarations output trace)
    (source : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters source lexical trace trace := by
  induction parsed with
  | done atEnd => exact .nil
  | cons head tail ih => exact (head.cascadeFilters source lexical).append ih

/-- Independent filtering cannot change even one event of a pragma sequence. -/
theorem PragmaSequenceTraceParses.cascadeFilters_iff
    {input output : Remainder} {declarations : List Syntax.PragmaDecl}
    {trace kept : List ParseDiagnostic}
    (parsed : PragmaSequenceTraceParses input declarations output trace)
    (source : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters source lexical trace kept ↔ kept = trace := by
  constructor
  · intro filtered
    exact filtered.output_unique (parsed.cascadeFilters source lexical)
  · intro same
    subst kept
    exact parsed.cascadeFilters source lexical

end Solcore.Syntax.DeclarativeGrammar
