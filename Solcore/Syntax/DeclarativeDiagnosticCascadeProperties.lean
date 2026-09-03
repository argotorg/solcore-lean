import Solcore.Syntax.DeclarativeDiagnosticCascadeGrammar

/-! Totality and exact retained-list uniqueness for independent cascade filtering. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem LexicalCascadeFilters.output_unique
    {source : String} {lexical raw left right : List SourceSpan}
    (leftFiltered : LexicalCascadeFilters source lexical raw left)
    (rightFiltered : LexicalCascadeFilters source lexical raw right) :
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

theorem lexicalCascadeFilters_total (source : String)
    (lexical raw : List SourceSpan) :
    ∃ kept, LexicalCascadeFilters source lexical raw kept := by
  classical
  induction raw with
  | nil => exact ⟨[], .nil⟩
  | cons span raw ih =>
      rcases ih with ⟨kept, filtered⟩
      by_cases suppressed : LexicalCascadeSuppresses source lexical span
      · exact ⟨kept, .drop suppressed filtered⟩
      · exact ⟨span :: kept, .keep suppressed filtered⟩

theorem lexicalCascadeFilters_nil_lexical (source : String)
    (raw : List SourceSpan) : LexicalCascadeFilters source [] raw raw := by
  induction raw with
  | nil => exact .nil
  | cons span raw ih => exact .keep (by simp [LexicalCascadeSuppresses]) ih

theorem lexicalCascadeFilters_singleton_iff
    {source : String} {lexical kept : List SourceSpan} {span : SourceSpan} :
    LexicalCascadeFilters source lexical [span] kept ↔
      (LexicalCascadeSuppresses source lexical span ∧ kept = []) ∨
      (¬ LexicalCascadeSuppresses source lexical span ∧ kept = [span]) := by
  constructor
  · intro filtered
    cases filtered with
    | keep retained tail => cases tail; exact Or.inr ⟨retained, rfl⟩
    | drop suppressed tail => cases tail; exact Or.inl ⟨suppressed, rfl⟩
  · rintro (⟨suppressed, rfl⟩ | ⟨retained, rfl⟩)
    · exact .drop suppressed .nil
    · exact .keep retained .nil

end Solcore.Syntax.DeclarativeGrammar
