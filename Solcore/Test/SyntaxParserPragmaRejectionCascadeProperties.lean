import Solcore.Syntax.DeclarativePragmaRejectionCascadeProperties

/-! Independent consumers distinguish the raw prefix from a committed failure.
Whole-list equalities preserve repeated reports, their order, and all payloads. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaRejectionCascadeProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat} {input rejected : Remainder}
  {diagnostic : ParseDiagnostic} {trace kept : List ParseDiagnostic}
  (traced : PragmaDeclTraceRejects source endByte input rejected diagnostic trace)
  (text : String) (lexical : List SourceSpan)

example (filtered : ParseDiagnosticCascadeFilters text lexical
    (trace ++ [diagnostic]) kept) :
    (¬ ParseDiagnosticCascadeSuppresses text lexical diagnostic ∧
      kept = trace ++ [diagnostic]) ∨
      (ParseDiagnosticCascadeSuppresses text lexical diagnostic ∧ kept = trace) :=
  (traced.committedCascadeFilters_iff text lexical).mp filtered

example (choice :
    (¬ ParseDiagnosticCascadeSuppresses text lexical diagnostic ∧
      kept = trace ++ [diagnostic]) ∨
      (ParseDiagnosticCascadeSuppresses text lexical diagnostic ∧ kept = trace)) :
    ParseDiagnosticCascadeFilters text lexical (trace ++ [diagnostic]) kept :=
  (traced.committedCascadeFilters_iff text lexical).mpr choice

/-- Dropping the committed report preserves all three earlier occurrences,
including an identical repeated event after a different event. -/
theorem repeated_prefix_survives_suppression
    {first second : ParseDiagnostic}
    (prefixTraced : PragmaDeclTraceRejects source endByte input rejected diagnostic
      [first, second, first])
    (suppressed : ParseDiagnosticCascadeSuppresses text lexical diagnostic) :
    ParseDiagnosticCascadeFilters text lexical
      [first, second, first, diagnostic] [first, second, first] :=
  prefixTraced.committedCascadeFilters_of_suppressed text lexical suppressed

/-- Keeping the committed report leaves it last; the protected prefix's order
and duplicates remain unchanged instead of becoming a set of spans. -/
theorem repeated_prefix_precedes_retained_failure
    {first second : ParseDiagnostic}
    (prefixTraced : PragmaDeclTraceRejects source endByte input rejected diagnostic
      [first, second, first])
    (retained : ¬ ParseDiagnosticCascadeSuppresses text lexical diagnostic) :
    ParseDiagnosticCascadeFilters text lexical
      [first, second, first, diagnostic] [first, second, first, diagnostic] :=
  prefixTraced.committedCascadeFilters_of_retained text lexical retained

include traced in
/-- Filtering cannot introduce a third possibility or silently remove a
protected occurrence from the rejecting declaration's earlier trace. -/
theorem committed_output_has_only_two_shapes
    (filtered : ParseDiagnosticCascadeFilters text lexical (trace ++ [diagnostic]) kept) :
    kept = trace ++ [diagnostic] ∨ kept = trace := by
  rcases (traced.committedCascadeFilters_iff text lexical).mp filtered with
    ⟨_, same⟩ | ⟨_, same⟩
  · exact Or.inl same
  · exact Or.inr same

/-- Before the caller commits its failure, only the raw prefix is filtered;
no failure event is invented by the rejecting grammar or its protection law. -/
example : ParseDiagnosticCascadeFilters text lexical trace trace :=
  traced.cascadeFilters text lexical

end Solcore.Test.SyntaxParserPragmaRejectionCascadeProperties
