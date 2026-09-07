import Solcore.Syntax.DeclarativeCoreBlockTailCascadeProperties

/-! Consumers preserve the protected validation suffix after filtering an
arbitrary event prefix. Full reports remain ordered, including duplicates. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCoreBlockTailCascadeProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar

variable {policy : CoreBlockTailPolicy} {statements : List Statement}
  {text : String} {lexical : List SourceSpan}

example {tailTrace events keptEvents : List ParseDiagnostic}
    (parsed : CoreBlockTailsDiagnosticTrace policy statements tailTrace)
    (filtered : ParseDiagnosticCascadeFilters text lexical events keptEvents) :
    ParseDiagnosticCascadeFilters text lexical
      (events ++ tailTrace) (keptEvents ++ tailTrace) :=
  parsed.append_cascadeFilters filtered

example {tailTrace events kept : List ParseDiagnostic}
    (parsed : CoreBlockTailsDiagnosticTrace policy statements tailTrace) :
    ParseDiagnosticCascadeFilters text lexical (events ++ tailTrace) kept ↔
      ∃ keptEvents, ParseDiagnosticCascadeFilters text lexical events keptEvents ∧
        kept = keptEvents ++ tailTrace := parsed.append_cascadeFilters_iff text lexical

/-- Suppressing the middle prefix event preserves both retained prefix
occurrences before both identical tail reports, without crossing the boundary. -/
theorem suppressed_middle_preserves_duplicate_groups
    {retainedEvent suppressedEvent tailEvent : ParseDiagnostic}
    (parsed : CoreBlockTailsDiagnosticTrace policy statements [tailEvent, tailEvent])
    (retained : ¬ ParseDiagnosticCascadeSuppresses text lexical retainedEvent)
    (suppressed : ParseDiagnosticCascadeSuppresses text lexical suppressedEvent) :
    ParseDiagnosticCascadeFilters text lexical
      [retainedEvent, suppressedEvent, retainedEvent, tailEvent, tailEvent]
      [retainedEvent, retainedEvent, tailEvent, tailEvent] :=
  parsed.append_cascadeFilters (.keep retained (.drop suppressed (.keep retained .nil)))

/-- Even deleting every repeated prefix event cannot remove either repeated
validation report. The iff forces every result to be this unchanged suffix. -/
theorem fully_suppressed_prefix_leaves_exact_tail
    {suppressedEvent tailEvent : ParseDiagnostic} {kept : List ParseDiagnostic}
    (parsed : CoreBlockTailsDiagnosticTrace policy statements [tailEvent, tailEvent])
    (suppressed : ParseDiagnosticCascadeSuppresses text lexical suppressedEvent) :
    ParseDiagnosticCascadeFilters text lexical
      [suppressedEvent, suppressedEvent, tailEvent, tailEvent] kept ↔
      kept = [tailEvent, tailEvent] := by
  have prefixFiltered : ParseDiagnosticCascadeFilters text lexical
      [suppressedEvent, suppressedEvent] [] := .drop suppressed (.drop suppressed .nil)
  constructor
  · intro filtered
    rcases (parsed.append_cascadeFilters_iff
      (events := [suppressedEvent, suppressedEvent]) text lexical).mp filtered with
      ⟨keptEvents, leading, same⟩
    rw [leading.output_unique prefixFiltered] at same
    exact same
  · intro same
    subst kept
    exact parsed.append_cascadeFilters prefixFiltered

end Solcore.Test.SyntaxCoreBlockTailCascadeProperties
