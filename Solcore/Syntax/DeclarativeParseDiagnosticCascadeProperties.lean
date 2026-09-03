import Solcore.Syntax.DeclarativeParseDiagnosticCascadeGrammar

/-! Total, unique, order-preserving normalization of complete diagnostic traces. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem ParseDiagnosticCascadeFilters.output_unique
    {source : String} {lexical : List SourceSpan} {raw left right : List ParseDiagnostic}
    (leftFiltered : ParseDiagnosticCascadeFilters source lexical raw left)
    (rightFiltered : ParseDiagnosticCascadeFilters source lexical raw right) :
    left = right := by
  induction leftFiltered generalizing right with
  | nil => cases rightFiltered; rfl
  | keep retained tail ih =>
      cases rightFiltered with
      | keep _ rightTail => rw [ih rightTail]
      | drop suppressed _ => exact False.elim (retained suppressed)
  | drop suppressed tail ih =>
      cases rightFiltered with
      | keep retained _ => exact False.elim (retained suppressed)
      | drop _ rightTail => exact ih rightTail

theorem parseDiagnosticCascadeFilters_total (source : String)
    (lexical : List SourceSpan) (raw : List ParseDiagnostic) :
    ∃ kept, ParseDiagnosticCascadeFilters source lexical raw kept := by
  classical
  induction raw with
  | nil => exact ⟨[], .nil⟩
  | cons diagnostic raw ih =>
      rcases ih with ⟨kept, filtered⟩
      by_cases suppressed : ParseDiagnosticCascadeSuppresses source lexical diagnostic
      · exact ⟨kept, .drop suppressed filtered⟩
      · exact ⟨diagnostic :: kept, .keep suppressed filtered⟩

/-- A protected kind survives even if its source span matches a lexical error. -/
theorem parseDiagnosticCascadeFilters_protected_cons
    {source : String} {lexical : List SourceSpan} {diagnostic : ParseDiagnostic}
    {raw kept : List ParseDiagnostic}
    (protectedKind : ¬ LexicalCascadeCandidate diagnostic.kind)
    (tail : ParseDiagnosticCascadeFilters source lexical raw kept) :
    ParseDiagnosticCascadeFilters source lexical (diagnostic :: raw) (diagnostic :: kept) :=
  .keep (fun suppressed => protectedKind suppressed.1) tail

/-- Retained occurrences remain ordered, without inventing reports. -/
theorem ParseDiagnosticCascadeFilters.sublist
    {source : String} {lexical : List SourceSpan} {raw kept : List ParseDiagnostic}
    (filtered : ParseDiagnosticCascadeFilters source lexical raw kept) :
    kept.Sublist raw := by
  induction filtered with
  | nil => exact .slnil
  | keep _ _ ih => exact .cons_cons _ ih
  | drop _ _ ih => exact .cons _ ih

theorem parseDiagnosticCascadeFilters_nil_lexical (source : String)
    (raw : List ParseDiagnostic) : ParseDiagnosticCascadeFilters source [] raw raw := by
  induction raw with
  | nil => exact .nil
  | cons diagnostic raw ih =>
      exact .keep (by simp [ParseDiagnosticCascadeSuppresses, LexicalCascadeSuppresses]) ih

/-- Independent filtering composes without reordering the concatenated traces. -/
theorem ParseDiagnosticCascadeFilters.append
    {source : String} {lexical : List SourceSpan}
    {left right keptLeft keptRight : List ParseDiagnostic}
    (leading : ParseDiagnosticCascadeFilters source lexical left keptLeft)
    (trailing : ParseDiagnosticCascadeFilters source lexical right keptRight) :
    ParseDiagnosticCascadeFilters source lexical (left ++ right) (keptLeft ++ keptRight) := by
  induction leading with
  | nil => exact trailing
  | keep retained tail ih => exact .keep retained ih
  | drop suppressed tail ih => exact .drop suppressed ih

/-- An entirely protected trace survives regardless of lexical error locations. -/
theorem parseDiagnosticCascadeFilters_of_protected (source : String)
    (lexical : List SourceSpan) {trace : List ParseDiagnostic}
    (protectedKinds : ∀ diagnostic ∈ trace, ¬ LexicalCascadeCandidate diagnostic.kind) :
    ParseDiagnosticCascadeFilters source lexical trace trace := by
  induction trace with
  | nil => exact .nil
  | cons diagnostic trace ih =>
      exact parseDiagnosticCascadeFilters_protected_cons
        (protectedKinds diagnostic (by simp))
        (ih (fun member found => protectedKinds member (List.mem_cons_of_mem _ found)))

end Solcore.Syntax.DeclarativeGrammar
