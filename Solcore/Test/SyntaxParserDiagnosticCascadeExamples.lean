import Solcore.Syntax.Parser.DiagnosticCascadeProperties

/-! Concrete independent cascade-policy regressions. Computation uses kernel
reduction only; filtering preserves the input order and duplicate events. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDiagnosticCascadeExamples

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals

private def owner : SourceId := { origin := .main, path := "cascade.sol" }
private def span (start ending : Nat) : SourceSpan := {
  source := owner, startByte := start, endByte := ending
}
private def foreignSpan (start ending : Nat) : SourceSpan := {
  span start ending with source := { origin := .standard, path := "cascade.sol" }
}
private def file (content : String) : SourceFile := { id := owner, content }
private def lexical (start ending : Nat) : LexicalDiagnostic := {
  span := span start ending, kind := .invalidToken
}

private theorem gap_rejected_of_slice {source gap : String}
    {lexicalSpan parsedSpan : SourceSpan}
    (slice : Trivia.utf8Slice? source lexicalSpan.endByte parsedSpan.startByte = some gap)
    (notHorizontal : (gap.toList.all fun character =>
      Trivia.isRustWhitespace character && character != '\n' && character != '\r') = false) :
    ¬ HorizontalWhitespaceGap source lexicalSpan parsedSpan := by
  rintro ⟨_, other, otherSlice, horizontal⟩
  have gapEq := Option.some.inj (slice.symm.trans otherSlice)
  cases gapEq
  rw [notHorizontal] at horizontal
  contradiction

private theorem singleton_not_suppressed {source : String}
    {lexicalSpan parsedSpan : SourceSpan}
    (retained : ¬ LexicalSpanSuppresses source lexicalSpan parsedSpan) :
    ¬ LexicalCascadeSuppresses source [lexicalSpan] parsedSpan := by
  rintro ⟨current, member, suppressed⟩
  have equal := List.mem_singleton.mp member
  cases equal
  exact retained suppressed

/-- Same-LF-line suppression does not require overlap or a whitespace gap. -/
theorem sameLfLine_nonAdjacent_suppressed :
    LexicalSpanSuppresses "a xyz b" (span 0 1) (span 6 7) :=
  ⟨rfl, Or.inl (by decide)⟩

theorem sameLfLine_nonAdjacent_gap_rejected :
    ¬ HorizontalWhitespaceGap "a xyz b" (span 0 1) (span 6 7) :=
  gap_rejected_of_slice (gap := " xyz ") (by decide) (by decide)

/-- Even coincident byte ranges do not suppress events owned by another source. -/
theorem differentSource_retained :
    ¬ LexicalSpanSuppresses "a" (span 0 1) (foreignSpan 0 1) := by
  rintro ⟨sameOwner, _⟩
  exact (by decide : (span 0 1).source ≠ (foreignSpan 0 1).source) sameOwner

theorem differentSource_filters :
    LexicalCascadeFilters "a" [span 0 1] [foreignSpan 0 1] [foreignSpan 0 1] :=
  .keep (singleton_not_suppressed differentSource_retained) .nil

/-- CR is not counted as a line break by this policy, whereas LF is. -/
theorem lineIndex_counts_lf_not_cr :
    cascadeLineIndex "a\rb" 2 = 0 ∧ cascadeLineIndex "a\nb" 2 = 1 := by
  decide

theorem cr_gap_rejected :
    ¬ HorizontalWhitespaceGap "a\rb" (span 0 1) (span 2 3) :=
  gap_rejected_of_slice (gap := "\r") (by decide) (by decide)

theorem lf_gap_rejected :
    ¬ HorizontalWhitespaceGap "a\nb" (span 0 1) (span 2 3) :=
  gap_rejected_of_slice (gap := "\n") (by decide) (by decide)

/-- Rejecting a CR gap does not disable the separate same-LF-line rule. -/
theorem acrossCr_still_suppressed :
    LexicalSpanSuppresses "a\rb" (span 0 1) (span 2 3) :=
  ⟨rfl, Or.inl (by decide)⟩

/-- At a lexical endpoint, inclusive containment succeeds despite distinct
LF lines and the strict overlap test failing. -/
theorem inclusive_lexical_end_suppressed :
    LexicalSpanSuppresses "a\nb" (span 0 2) (span 2 3) :=
  ⟨rfl, Or.inr (Or.inr (Or.inl ⟨by decide, by decide⟩))⟩

theorem inclusive_end_has_no_strict_overlap :
    cascadeLineIndex "a\nb" 0 ≠ cascadeLineIndex "a\nb" 2 ∧
      ¬ ((span 0 2).startByte < (span 2 3).endByte ∧
        (span 2 3).startByte < (span 0 2).endByte) := by
  decide

private def unicodeGap : String := String.singleton (Char.ofNat 0x2028)
private def unicodeSource : String := "a" ++ unicodeGap ++ "b"

/-- U+2028 is Rust whitespace but is neither CR nor LF, so the gap is admitted. -/
theorem unicode_line_separator_gap_allowed :
    HorizontalWhitespaceGap unicodeSource (span 0 1) (span 4 5) :=
  ⟨by decide, unicodeGap, by decide, by decide⟩

/-- Mid-codepoint and out-of-range prefixes both follow the documented zero fallback. -/
theorem invalid_utf8_prefix_is_line_zero :
    Trivia.utf8Slice? "é\nx" 0 1 = none ∧
      cascadeLineIndex "é\nx" 1 = 0 ∧
      cascadeLineIndex "é\nx" 5 = 0 ∧
      cascadeLineIndex "é\nx" 3 = 1 := by
  decide

private theorem secondLine_retained :
    ¬ LexicalSpanSuppresses "a\nb\nc" (span 0 1) (span 2 3) := by
  rintro ⟨_, sameLine | overlap | inside | gap⟩
  · exact (by decide : cascadeLineIndex "a\nb\nc" 0 ≠
      cascadeLineIndex "a\nb\nc" 2) sameLine
  · exact (by decide : ¬ ((span 0 1).startByte < (span 2 3).endByte ∧
      (span 2 3).startByte < (span 0 1).endByte)) overlap
  · exact (by decide : ¬ ((span 0 1).startByte ≤ (span 2 3).startByte ∧
      (span 2 3).startByte ≤ (span 0 1).endByte)) inside
  · exact gap_rejected_of_slice (gap := "\n") (by decide) (by decide) gap

private theorem thirdLine_retained :
    ¬ LexicalSpanSuppresses "a\nb\nc" (span 0 1) (span 4 5) := by
  rintro ⟨_, sameLine | overlap | inside | gap⟩
  · exact (by decide : cascadeLineIndex "a\nb\nc" 0 ≠
      cascadeLineIndex "a\nb\nc" 4) sameLine
  · exact (by decide : ¬ ((span 0 1).startByte < (span 4 5).endByte ∧
      (span 4 5).startByte < (span 0 1).endByte)) overlap
  · exact (by decide : ¬ ((span 0 1).startByte ≤ (span 4 5).startByte ∧
      (span 4 5).startByte ≤ (span 0 1).endByte)) inside
  · exact gap_rejected_of_slice (gap := "\nb\n") (by decide) (by decide) gap

/-- Filtering drops the first event but retains both equal middle events and
their order relative to the final event. -/
theorem order_and_duplicates_filters :
    LexicalCascadeFilters "a\nb\nc" [span 0 1]
      [span 0 1, span 2 3, span 2 3, span 4 5]
      [span 2 3, span 2 3, span 4 5] :=
  .drop ⟨span 0 1, by simp, ⟨rfl, Or.inl rfl⟩⟩
    (.keep (singleton_not_suppressed secondLine_retained)
      (.keep (singleton_not_suppressed secondLine_retained)
        (.keep (singleton_not_suppressed thirdLine_retained) .nil)))

/-- The executable normalization agrees with the independently built trace. -/
theorem order_and_duplicates_executable :
    filterParseDiagnostics (file "a\nb\nc") [lexical 0 1]
      (topItemRecoveryDiagnostics [span 0 1, span 2 3, span 2 3, span 4 5]) =
      topItemRecoveryDiagnostics [span 2 3, span 2 3, span 4 5] :=
  filterParseDiagnostics_recoveredTopItems_of_filters _ _ order_and_duplicates_filters

theorem sameLfLine_executable :
    filterParseDiagnostics (file "a xyz b") [lexical 0 1]
      (topItemRecoveryDiagnostics [span 6 7]) = [] := by
  decide

theorem differentSource_executable :
    filterParseDiagnostics (file "a") [lexical 0 1]
      (topItemRecoveryDiagnostics [foreignSpan 0 1]) =
      topItemRecoveryDiagnostics [foreignSpan 0 1] := by
  decide

theorem lf_gap_executable_retained :
    filterParseDiagnostics (file "a\nb") [lexical 0 1]
      (topItemRecoveryDiagnostics [span 2 3]) =
      topItemRecoveryDiagnostics [span 2 3] := by
  decide

theorem cr_gap_executable_suppressed :
    filterParseDiagnostics (file "a\rb") [lexical 0 1]
      (topItemRecoveryDiagnostics [span 2 3]) = [] := by
  decide

theorem inclusive_endpoint_executable :
    filterParseDiagnostics (file "a\nb") [lexical 0 2]
      (topItemRecoveryDiagnostics [span 2 3]) = [] := by
  decide

theorem unicode_gap_executable :
    filterParseDiagnostics (file unicodeSource) [lexical 0 1]
      (topItemRecoveryDiagnostics [span 4 5]) = [] := by
  decide

end Solcore.Test.SyntaxParserDiagnosticCascadeExamples
