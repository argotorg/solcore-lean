import Solcore
import Solcore.Syntax.Parser.Internal.DiagnosticTrace
import Solcore.Syntax.Parser.Internal.SourceFileTrace
import Solcore.Syntax.Parser
import Solcore.Syntax.Parser.Internal.FileProofs
import Solcore.Syntax.Parser.Internal.ExpressionAtomTrace
import Solcore.Syntax.Parser.Internal.ExpressionAtomProofs
import Solcore.Syntax.Parser.Internal.DelimitedTrace

/-!
# Parser diagnostics tests

Diagnostic suppression and cascades, rejection of legacy forms, the preflight pass, upstream
fixtures with their diagnostic policy, and the trace completeness derived from soundness.
-/

section
-- leanmerge: from Solcore.Test.SyntaxDiagnosticFilterProperties
/-! External compile consumers for canonical diagnostic-filter laws. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @filterParseDiagnostics_single_nestingExceeded

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    (parsed : List ParseDiagnostic) (diagnostic : ParseDiagnostic)
    (member : diagnostic ∈ filterParseDiagnostics file lexical parsed) :
    diagnostic ∈ parsed :=
  mem_of_mem_filterParseDiagnostics file lexical parsed diagnostic member

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    (parsed : List ParseDiagnostic)
    (valid : ∀ diagnostic ∈ parsed, diagnostic.span.ValidFor file) :
    ∀ diagnostic ∈ filterParseDiagnostics file lexical parsed,
      diagnostic.span.ValidFor file :=
  filterParseDiagnostics_spans_validFor file lexical parsed valid

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserCompositionalDiagnosticTraceProperties
/-! Executable combinator consumers. Nonempty earlier and rejected-branch
diagnostics make retention versus transactional rollback observable. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCompositionalDiagnosticTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @emitDiagnostic_success_trace
example := @bind_success_trace
example := @bind_reject_right_trace
example := @bind_reject_left_trace
example := @map_success_trace
example := @map_reject_trace
example := @bind_invariant_left_exact
example := @orElse_eq_right_of_reject
example := @orElse_success_left_trace
example := @orElse_success_right_trace
example := @orElse_reject_right_trace
example := @orElse_invariant_left_exact
example := @orElse_invariant_right_exact

private def emitValue (diagnostic : ParseDiagnostic) (value : Nat) : Parser Nat := do
  emitDiagnostic diagnostic
  pure value

private def emitReject (diagnostic : ParseDiagnostic) (failure : Failure) : Parser Nat := do
  emitDiagnostic diagnostic
  fun state => .reject failure state

private theorem emit_nonempty (input : State) (diagnostic : ParseDiagnostic) :
    (input.emit diagnostic).diagnostics ≠ [] := by
  simp [State.emit, State.diagnostics]

/-- Sequencing preserves a nonempty prior prefix and both new events in order. -/
theorem sequencing_success_order (input : State)
    (prior firstEvent nextEvent : ParseDiagnostic) :
    ((emitValue firstEvent 3) >>= fun _ => emitValue nextEvent 7) (input.emit prior) =
      .ok 7 (((input.emit prior).emit firstEvent).emit nextEvent) ∧
      (((input.emit prior).emit firstEvent).emit nextEvent).diagnostics =
        input.diagnostics ++ [prior, firstEvent, nextEvent] := by
  have result := bind_success_trace
    (first := emitValue firstEvent 3) (next := fun _ => emitValue nextEvent 7)
    (input := input.emit prior) rfl
    (emitDiagnostic_success_trace firstEvent (input.emit prior)).2 rfl
    (emitDiagnostic_success_trace nextEvent ((input.emit prior).emit firstEvent)).2
  refine ⟨result.1, ?_⟩
  simpa only [(emitDiagnostic_success_trace prior input).2, List.append_assoc,
    List.singleton_append] using result.2

/-- A later ordinary rejection does not roll back the earlier successful event. -/
theorem sequencing_reject_retains_both (input : State)
    (prior firstEvent nextEvent : ParseDiagnostic) (failure : Failure) :
    ((emitValue firstEvent 3) >>= fun _ => emitReject nextEvent failure) (input.emit prior) =
      .reject failure (((input.emit prior).emit firstEvent).emit nextEvent) ∧
      (((input.emit prior).emit firstEvent).emit nextEvent).diagnostics =
        input.diagnostics ++ [prior, firstEvent, nextEvent] := by
  have result := bind_reject_right_trace
    (first := emitValue firstEvent 3) (next := fun _ => emitReject nextEvent failure)
    (input := input.emit prior) rfl
    (emitDiagnostic_success_trace firstEvent (input.emit prior)).2 rfl
    (emitDiagnostic_success_trace nextEvent ((input.emit prior).emit firstEvent)).2
  refine ⟨result.1, ?_⟩
  simpa only [(emitDiagnostic_success_trace prior input).2, List.append_assoc,
    List.singleton_append] using result.2

/-- First-stage rejection never runs an arbitrary continuation. -/
theorem sequencing_first_reject_stops (input : State)
    (prior event : ParseDiagnostic) (failure : Failure) (next : Nat → Parser Nat) :
    (emitReject event failure >>= next) (input.emit prior) =
      .reject failure ((input.emit prior).emit event) ∧
      ((input.emit prior).emit event).diagnostics = input.diagnostics ++ [prior, event] := by
  have result := bind_reject_left_trace next
    (first := emitReject event failure) (input := input.emit prior) rfl
    (emitDiagnostic_success_trace event (input.emit prior)).2
  refine ⟨result.1, ?_⟩
  simpa only [(emitDiagnostic_success_trace prior input).2, List.append_assoc,
    List.singleton_append] using result.2

/-- Mapping the returned value cannot reorder or remove the diagnostic event. -/
theorem mapping_success_preserves_trace (input : State)
    (prior event : ParseDiagnostic) :
    (Nat.succ <$> emitValue event 7) (input.emit prior) =
      .ok 8 ((input.emit prior).emit event) ∧
      ((input.emit prior).emit event).diagnostics = input.diagnostics ++ [prior, event] := by
  have result := map_success_trace Nat.succ
    (parser := emitValue event 7) (input := input.emit prior) rfl
    (emitDiagnostic_success_trace event (input.emit prior)).2
  refine ⟨result.1, ?_⟩
  simpa only [(emitDiagnostic_success_trace prior input).2, List.append_assoc,
    List.singleton_append] using result.2

/-- Mapping also preserves a rejected payload and its nonempty raw trace. -/
theorem mapping_reject_preserves_trace (input : State)
    (prior event : ParseDiagnostic) (failure : Failure) :
    (Nat.succ <$> emitReject event failure) (input.emit prior) =
      .reject failure ((input.emit prior).emit event) ∧
      ((input.emit prior).emit event).diagnostics = input.diagnostics ++ [prior, event] := by
  have result := map_reject_trace Nat.succ
    (parser := emitReject event failure) (input := input.emit prior) rfl
    (emitDiagnostic_success_trace event (input.emit prior)).2
  refine ⟨result.1, ?_⟩
  simpa only [(emitDiagnostic_success_trace prior input).2, List.append_assoc,
    List.singleton_append] using result.2

/-- Both the original and failed-left diagnostic sequences are nonempty.
Fallback discards the left event but retains the prior prefix and right event. -/
theorem choice_nonempty_rollback_success (input : State)
    (prior leftEvent rightEvent : ParseDiagnostic) (failure : Failure) :
    (input.emit prior).diagnostics ≠ [] ∧
      ((input.emit prior).emit leftEvent).diagnostics ≠ [] ∧
      orElse (emitReject leftEvent failure) (emitValue rightEvent 7) (input.emit prior) =
        .ok 7 ((input.emit prior).emit rightEvent) ∧
      ((input.emit prior).emit rightEvent).diagnostics =
        input.diagnostics ++ [prior, rightEvent] := by
  have result := orElse_success_right_trace
    (first := emitReject leftEvent failure) (second := emitValue rightEvent 7)
    (input := input.emit prior) rfl rfl
    (emitDiagnostic_success_trace rightEvent (input.emit prior)).2
  refine ⟨emit_nonempty input prior, emit_nonempty (input.emit prior) leftEvent, result.1, ?_⟩
  simpa only [(emitDiagnostic_success_trace prior input).2, List.append_assoc,
    List.singleton_append] using result.2

/-- Even when both alternatives reject after emitting, only the right failure
and its event survive; the original nonempty diagnostic prefix is retained. -/
theorem choice_nonempty_rollback_reject (input : State)
    (prior leftEvent rightEvent : ParseDiagnostic) (leftFailure rightFailure : Failure) :
    (input.emit prior).diagnostics ≠ [] ∧
      ((input.emit prior).emit leftEvent).diagnostics ≠ [] ∧
      orElse (emitReject leftEvent leftFailure) (emitReject rightEvent rightFailure)
        (input.emit prior) = .reject rightFailure ((input.emit prior).emit rightEvent) ∧
      ((input.emit prior).emit rightEvent).diagnostics =
        input.diagnostics ++ [prior, rightEvent] := by
  have result := orElse_reject_right_trace
    (first := emitReject leftEvent leftFailure) (second := emitReject rightEvent rightFailure)
    (input := input.emit prior) rfl rfl
    (emitDiagnostic_success_trace rightEvent (input.emit prior)).2
  refine ⟨emit_nonempty input prior, emit_nonempty (input.emit prior) leftEvent, result.1, ?_⟩
  simpa only [(emitDiagnostic_success_trace prior input).2, List.append_assoc,
    List.singleton_append] using result.2

/-- A successful left branch retains its own event and ignores any right parser. -/
theorem choice_left_success_keeps_trace (input : State)
    (prior event : ParseDiagnostic) (second : Parser Nat) :
    orElse (emitValue event 3) second (input.emit prior) =
      .ok 3 ((input.emit prior).emit event) ∧
      ((input.emit prior).emit event).diagnostics = input.diagnostics ++ [prior, event] := by
  have result := orElse_success_left_trace second
    (first := emitValue event 3) (input := input.emit prior) rfl
    (emitDiagnostic_success_trace event (input.emit prior)).2
  refine ⟨result.1, ?_⟩
  simpa only [(emitDiagnostic_success_trace prior input).2, List.append_assoc,
    List.singleton_append] using result.2

end Solcore.Test.SyntaxParserCompositionalDiagnosticTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDiagnosticCascadeExamples
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
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDiagnosticCascadeProperties
/-! Consumers of independent keep/drop decisions and exact diagnostic lists. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDiagnosticCascadeProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    (raw kept : List SourceSpan)
    (filtered : LexicalCascadeFilters file.content (lexical.map (·.span)) raw kept) :
    filterParseDiagnostics file lexical (topItemRecoveryDiagnostics raw) =
      topItemRecoveryDiagnostics kept :=
  (filterParseDiagnostics_recoveredTopItems_iff file lexical raw kept).mp filtered

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    (raw kept : List SourceSpan)
    (result : filterParseDiagnostics file lexical (topItemRecoveryDiagnostics raw) =
      topItemRecoveryDiagnostics kept) :
    LexicalCascadeFilters file.content (lexical.map (·.span)) raw kept :=
  (filterParseDiagnostics_recoveredTopItems_iff file lexical raw kept).mpr result

example (file : SourceFile) (lexical : List LexicalDiagnostic) (span : SourceSpan)
    (suppressed : LexicalCascadeSuppresses file.content (lexical.map (·.span)) span) :
    filterParseDiagnostics file lexical (topItemRecoveryDiagnostics [span]) = [] :=
  filterParseDiagnostics_recoveredTopItems_of_filters file lexical (.drop suppressed .nil)

example (file : SourceFile) (lexical : List LexicalDiagnostic) (span : SourceSpan)
    (retained : ¬ LexicalCascadeSuppresses file.content (lexical.map (·.span)) span) :
    filterParseDiagnostics file lexical (topItemRecoveryDiagnostics [span, span]) =
      topItemRecoveryDiagnostics [span, span] :=
  filterParseDiagnostics_recoveredTopItems_of_filters file lexical
    (.keep retained (.keep retained .nil))

example (source : String) (lexical raw : List SourceSpan) :
    ∃ kept, LexicalCascadeFilters source lexical raw kept ∧
      ∀ other, LexicalCascadeFilters source lexical raw other → other = kept := by
  rcases lexicalCascadeFilters_total source lexical raw with ⟨kept, filtered⟩
  exact ⟨kept, filtered, fun _ other => other.output_unique filtered⟩

end Solcore.Test.SyntaxParserDiagnosticCascadeProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDiagnosticCascadeStabilityProperties
/-! Repeated and partitioned normalization retains the same complete reports. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDiagnosticCascadeStabilityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

example := @ParseDiagnosticCascadeFilters.retained_not_suppressed
example := @parseDiagnosticCascadeFilters_of_retained
example := @ParseDiagnosticCascadeFilters.stable
example := @filterParseDiagnostics_idempotent
example := @filterParseDiagnostics_append

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    {raw kept again : List ParseDiagnostic}
    (first : ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) raw kept)
    (second : ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) kept again) :
    again = kept :=
  second.output_unique first.stable

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    (left right : List ParseDiagnostic) :
    filterParseDiagnostics file lexical
      (filterParseDiagnostics file lexical left ++ filterParseDiagnostics file lexical right) =
      filterParseDiagnostics file lexical (left ++ right) := by
  rw [filterParseDiagnostics_append, filterParseDiagnostics_idempotent,
    filterParseDiagnostics_idempotent, filterParseDiagnostics_append]

end Solcore.Test.SyntaxParserDiagnosticCascadeStabilityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDiagnosticSuppression
/-! Regression coverage for lexical-to-parse diagnostic cascade suppression. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private abbrev ByteRange := Nat × Nat

private def diagnosticSource : SourceId := {
  origin := .main
  path := "parser-diagnostic-suppression.sol"
}

private def assertEqual {alpha : Type} [BEq alpha] [Repr alpha]
    (actual expected : alpha) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def byteRange (span : SourceSpan) : ByteRange :=
  (span.startByte, span.endByte)

private def checkedParse (label content : String) : IO ParseOutput := do
  let file : SourceFile := { id := diagnosticSource, content }
  let output ← match Parser.parse file with
    | .ok value => pure value
    | .error error => throw (IO.userError
        s!"{label}: parser invariant failed: {reprStr error}")
  unless output.lexicalDiagnostics.all
      (fun diagnostic => diagnostic.span.isValidFor file) do
    throw (IO.userError s!"{label}: invalid lexical diagnostic span")
  unless output.parseDiagnostics.all
      (fun diagnostic => diagnostic.span.isValidFor file) do
    throw (IO.userError s!"{label}: invalid parse diagnostic span")
  pure output

private def assertOneInvalidToken
    (output : ParseOutput) (label : String) : IO Unit := do
  match output.lexicalDiagnostics with
  | [{ kind := .invalidToken, .. }] => pure ()
  | diagnostics => throw (IO.userError
      s!"{label}: expected one invalid-token diagnostic, got \
        {reprStr diagnostics}")

private def aliasName? (item : TopItem) : Option String :=
  match item.value with
  | .typeAlias declaration => some declaration.value.name.value
  | _ => none

private def assertSingleErrorExpression
    (body : Block) (label : String) : IO Unit :=
  match body.value with
  | [{ value := .expression { value := .error, .. } true, .. }] => pure ()
  | statements => throw (IO.userError
      s!"{label}: expected one recovered expression, got {reprStr statements}")

private def testSameLineSuppression : IO Unit := do
  let output ← checkedParse "same-line cascade" "§ type Broken = ;"
  assertOneInvalidToken output "same-line cascade"
  assertEqual output.parseDiagnostics []
    "same-line parse cascade suppression"
  assertEqual output.parsed.items.length 0
    "same-line failed declaration"

private def testOverlappingSuppression : IO Unit := do
  let content := "type Broken = ;"
  let file : SourceFile := { id := diagnosticSource, content }
  let lexed ← match Lexer.lex file with
    | .ok value => pure value
    | .error error => throw (IO.userError
        s!"overlap setup lexer invariant failed: {reprStr error}")
  let semicolon ← match lexed.tokens.getLast? with
    | some token => pure token
    | none => throw (IO.userError "overlap setup has no semicolon token")
  let overlapping : LexedFile := {
    lexed with
    diagnostics := [{
      span := semicolon.span
      kind := .invalidToken
    }]
  }
  let output ← match Parser.parseLexed file overlapping with
    | .ok value => pure value
    | .error error => throw (IO.userError
        s!"overlap parse invariant failed: {reprStr error}")
  assertOneInvalidToken output "overlap"
  assertEqual output.parseDiagnostics []
    "overlapping parse cascade suppression"
  assertEqual output.parsed.items.length 0
    "overlap failed declaration"

private def testSpaceOnlyAdjacencySuppression : IO Unit := do
  let output ← checkedParse "space-only adjacency"
    "type Broken = §   ;"
  assertOneInvalidToken output "space-only adjacency"
  assertEqual (output.lexicalDiagnostics.map fun diagnostic =>
      byteRange diagnostic.span) [(14, 16)]
    "space-only lexical span"
  assertEqual output.parseDiagnostics []
    "space-only adjacent parse cascade suppression"

private def testNextLineDiagnosticSurvives : IO Unit := do
  let output ← checkedParse "next-line top-level error"
    "§\n;\ntype Kept = word;"
  assertOneInvalidToken output "next-line top-level error"
  match output.parseDiagnostics with
  | [{ span, kind := .recovered .topItem }] =>
      assertEqual (byteRange span) (3, 4)
        "independent next-line diagnostic span"
  | diagnostics => throw (IO.userError
      s!"independent next-line diagnostic changed: {reprStr diagnostics}")
  match output.parsed.items with
  | [{ value := .error, .. }, kept] =>
      assertEqual (aliasName? kept) (some "Kept")
        "item after independent next-line error"
  | items => throw (IO.userError
      s!"next-line recovery items changed: {reprStr items}")

private def testBodyIsolationSuppressesLexCascade : IO Unit := do
  let source := String.intercalate "\n" [
    "function bad() { let x = §; }",
    "type Kept = word;"
  ]
  let output ← checkedParse "body lexical cascade" source
  assertOneInvalidToken output "body lexical cascade"
  assertEqual output.parseDiagnostics []
    "body parse cascade suppression"
  match output.parsed.items with
  | [
      { value := .function bad, .. },
      kept
    ] =>
      assertEqual bad.value.signature.name.value "bad"
        "isolated function name"
      assertSingleErrorExpression bad.value.body
        "lexically broken fallback body"
      assertEqual (aliasName? kept) (some "Kept")
        "item after lexically broken body"
  | items => throw (IO.userError
      s!"body lexical isolation items changed: {reprStr items}")

private def testBodyNextLineDiagnosticSurvives : IO Unit := do
  let source := String.intercalate "\n" [
    "function bad() {",
    "  §",
    "  let x = ;",
    "}",
    "type Kept = word;"
  ]
  let output ← checkedParse "body next-line error" source
  assertOneInvalidToken output "body next-line error"
  match output.parseDiagnostics with
  | [{ span, kind := .unexpected (some (.symbol .semicolon)) _ .expression }] =>
      assertEqual (byteRange span) (32, 33)
        "independent body diagnostic span"
  | diagnostics => throw (IO.userError
      s!"independent body diagnostic changed: {reprStr diagnostics}")
  match output.parsed.items with
  | [{ value := .function bad, .. }, kept] =>
      assertSingleErrorExpression bad.value.body
        "independently bad fallback body"
      assertEqual (aliasName? kept) (some "Kept")
        "item after independently bad body"
  | items => throw (IO.userError
      s!"body next-line items changed: {reprStr items}")

private def testTopRecoveryDoesNotDuplicateLexError : IO Unit := do
  let output ← checkedParse "top recovery duplication"
    "§ ;\ntype Kept = word;"
  assertOneInvalidToken output "top recovery duplication"
  assertEqual output.parseDiagnostics []
    "top recovery duplicate diagnostic"
  match output.parsed.items with
  | [{ value := .error, .. }, kept] =>
      assertEqual (aliasName? kept) (some "Kept")
        "item after suppressed top recovery"
  | items => throw (IO.userError
      s!"suppressed top recovery items changed: {reprStr items}")

private def testContractRecoveryDoesNotDuplicateLexError : IO Unit := do
  let source := String.intercalate "\n" [
    "contract C { § ; function good() {} }",
    "type Kept = word;"
  ]
  let output ← checkedParse "contract recovery duplication" source
  assertOneInvalidToken output "contract recovery duplication"
  assertEqual output.parseDiagnostics []
    "contract recovery duplicate diagnostic"
  match output.parsed.items with
  | [
      { value := .contract contract, .. },
      kept
    ] =>
      assertEqual (aliasName? kept) (some "Kept")
        "item after suppressed contract recovery"
      match contract.value.members with
      | [
          { value := .error, .. },
          { value := .function good, .. }
        ] =>
          assertEqual good.value.signature.name.value "good"
            "member after suppressed contract recovery"
      | members => throw (IO.userError
          s!"contract recovery members changed: {reprStr members}")
  | items => throw (IO.userError
      s!"contract recovery items changed: {reprStr items}")

private def testLexFreeRecoveryPairsRemain : IO Unit := do
  let core ← checkedParse "lex-free Core recovery"
    "function core() { return pair(+ -, 0); }"
  assertEqual core.lexicalDiagnostics [] "lex-free Core lexical diagnostics"
  assertEqual (core.parseDiagnostics.map (fun diagnostic => diagnostic.kind)) [
    .unexpected (some (.symbol .plus))
      { head := .expression, tail := [] } .expression,
    .recovered .expressionAtom
  ] "lex-free Core recovery pair"

  let yul ← checkedParse "lex-free Yul recovery"
    "function yul() { assembly { let x := pair(+ -, 0) } }"
  assertEqual yul.lexicalDiagnostics [] "lex-free Yul lexical diagnostics"
  assertEqual (yul.parseDiagnostics.map (fun diagnostic => diagnostic.kind)) [
    .unexpected (some (.symbol .plus))
      { head := .yulIdentifier, tail := [.yulLiteral] } .yulExpression,
    .recovered .yulExpression
  ] "lex-free Yul recovery pair"

/-- Run lexical-to-parse diagnostic cascade suppression regressions. -/
def testSyntaxParserDiagnosticSuppression : IO Unit := do
  testSameLineSuppression
  testOverlappingSuppression
  testSpaceOnlyAdjacencySuppression
  testNextLineDiagnosticSurvives
  testBodyIsolationSuppressesLexCascade
  testBodyNextLineDiagnosticSurvives
  testTopRecoveryDoesNotDuplicateLexError
  testContractRecoveryDoesNotDuplicateLexError
  testLexFreeRecoveryPairsRemain

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserLegacyRejection
/-!
Focused compatibility-boundary regressions for the canonical syntax pinned by
ADR-0153.  These spellings belonged to the replaced frontend or to Solidity;
the canonical parser must diagnose them instead of silently accepting a second
source language.
-/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private structure SpellingCase where
  label : String
  legacy : String
  canonical : String

private def sourceId (label : String) : SourceId := {
  origin := .main
  path := "legacy-rejection-" ++ label ++ ".sol"
}

private def parseTotal (label source : String) : IO ParseOutput := do
  let file : SourceFile := { id := sourceId label, content := source }
  match Parser.parse file with
  | .error error => throw (IO.userError
      s!"{label}: source parsing failed with an invariant error: {reprStr error}")
  | .ok output =>
      unless output.parsed.span.isValidFor file do
        throw (IO.userError s!"{label}: parsed-file span escaped the source")
      unless output.lexicalDiagnostics.all
          (fun diagnostic => diagnostic.span.isValidFor file) do
        throw (IO.userError s!"{label}: lexical diagnostic span escaped the source")
      unless output.parseDiagnostics.all
          (fun diagnostic => diagnostic.span.isValidFor file) do
        throw (IO.userError s!"{label}: parse diagnostic span escaped the source")
      pure output

private def assertRejected (case : SpellingCase) : IO Unit := do
  let output ← parseTotal (case.label ++ "-legacy") case.legacy
  if output.lexicalDiagnostics.isEmpty && output.parseDiagnostics.isEmpty then
    throw (IO.userError
      s!"{case.label}: legacy spelling parsed without a diagnostic: {case.legacy}")

private def assertCanonicalAccepted (case : SpellingCase) : IO Unit := do
  let output ← parseTotal (case.label ++ "-canonical") case.canonical
  unless output.lexicalDiagnostics.isEmpty do
    throw (IO.userError (
      s!"{case.label}: canonical counterpart has lexical diagnostics: " ++
        reprStr output.lexicalDiagnostics))
  unless output.parseDiagnostics.isEmpty do
    throw (IO.userError (
      s!"{case.label}: canonical counterpart has parse diagnostics: " ++
        reprStr output.parseDiagnostics))

private def spellingCases : List SpellingCase := [
  {
    label := "data-declaration"
    legacy := "data Option(T) = None;"
    canonical := "enum Option<T> { None }"
  },
  {
    label := "class-declaration"
    legacy := "class Eq(T) {}"
    canonical := "trait Eq<T> {}"
  },
  {
    label := "instance-declaration"
    legacy := "instance Eq: word {}"
    canonical := "impl Eq<word> {}"
  },
  {
    label := "forall-declaration-prefix"
    legacy := "forall T. function id(x: T) -> T { return x; }"
    canonical :=
      "function id<T>(x: T) returns (T) { return x; }"
  },
  {
    label := "prefix-public-function"
    legacy := "public function exposed() -> word { return 0; }"
    canonical :=
      "contract C { function exposed() public returns (word) { return 0; } }"
  },
  {
    label := "arrow-return"
    legacy := "function arrowResult() -> word { return 0; }"
    canonical :=
      "function arrowResult() returns (word) { return 0; }"
  },
  {
    label := "string-import"
    legacy := "import \"old/module.sol\";"
    canonical := "import old.module;"
  },
  {
    label := "postfix-selective-import"
    legacy := "import old.module.{item};"
    canonical := "import {item} from old.module;"
  },
  {
    label := "core-colon-equals-let"
    legacy := "function invalid() { let value := 1; }"
    canonical := "function valid() { let value = 1; }"
  },
  {
    label := "core-colon-equals-assignment"
    legacy := "function invalid() { value := 1; }"
    canonical := "function valid() { let value = 0; value = 1; }"
  },
  {
    label := "nullary-generic-arguments"
    legacy := "function emptyArgs(x: Box<>) {}"
    canonical := "function value<T>(x: Box<T>) {}"
  }
]

private def testLegacyBoundary : IO Unit := do
  for case in spellingCases do
    assertRejected case
    assertCanonicalAccepted case

private def testColonEqualsRemainsYulSyntax : IO Unit := do
  let output ← parseTotal "yul-colon-equals"
    "function valid() { assembly { let value := 1 value := add(value, 1) } }"
  unless output.lexicalDiagnostics.isEmpty && output.parseDiagnostics.isEmpty do
    throw (IO.userError (
      s!"Yul `:=` counterpart was rejected: {reprStr output.lexicalDiagnostics}; " ++
        reprStr output.parseDiagnostics))

/-- Run focused rejection checks for spellings removed by ADR-0153. -/
def testSyntaxParserLegacyRejection : IO Unit := do
  testLegacyBoundary
  testColonEqualsRemainsYulSyntax

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserParseDiagnosticCascadeProperties
/-! Mixed complete-report normalization, including protected metadata and duplicates. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserParseDiagnosticCascadeProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

example := @ParseDiagnosticCascadeFilters.output_unique
example := @parseDiagnosticCascadeFilters_total
example := @parseDiagnosticCascadeFilters_protected_cons
example := @ParseDiagnosticCascadeFilters.sublist
example := @parseDiagnosticCascadeFilters_nil_lexical
example := @filterParseDiagnostics_cons_of_suppressed
example := @filterParseDiagnostics_cons_of_retained

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    (raw kept : List ParseDiagnostic)
    (filtered : ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) raw kept) :
    filterParseDiagnostics file lexical raw = kept :=
  filterParseDiagnostics_eq_of_cascadeFilters file lexical filtered

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    (raw kept : List ParseDiagnostic)
    (result : filterParseDiagnostics file lexical raw = kept) :
    ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) raw kept :=
  (filterParseDiagnostics_eq_iff_cascadeFilters file lexical raw kept).mp result

/-- Equal spans do not make protected metadata removable. The original order
and the repeated identifier report survive between heterogeneous failures. -/
theorem mixed_protected_reports_retained
    (file : SourceFile) (lexical : List LexicalDiagnostic) (span : SourceSpan)
    (text : String) (constraint : ParseConstraint) (nesting : NestingKind) (limit : Nat)
    (found : Option TokenKind) (expected : NonemptyList ParseExpectation)
    (context : ParseContext) (site : RecoverySite)
    (suppressed : LexicalCascadeSuppresses file.content (lexical.map (·.span)) span) :
    filterParseDiagnostics file lexical [
      { span, kind := .invalidIdentifierHyphen text },
      { span, kind := .unexpected found expected context },
      { span, kind := .constraintViolation constraint },
      { span, kind := .recovered site },
      { span, kind := .nestingExceeded nesting limit },
      { span, kind := .invalidIdentifierHyphen text }
    ] = [
      { span, kind := .invalidIdentifierHyphen text },
      { span, kind := .constraintViolation constraint },
      { span, kind := .nestingExceeded nesting limit },
      { span, kind := .invalidIdentifierHyphen text }
    ] := by
  apply filterParseDiagnostics_eq_of_cascadeFilters
  exact .keep (fun h => h.1) (.drop ⟨trivial, suppressed⟩
    (.keep (fun h => h.1) (.drop ⟨trivial, suppressed⟩
      (.keep (fun h => h.1) (.keep (fun h => h.1) .nil)))))

/-- Distinct expectations at one retained span cannot be collapsed into a
single span-only event. Every payload and repeated report survives exactly. -/
theorem mixed_expectations_retained
    (file : SourceFile) (lexical : List LexicalDiagnostic) (span : SourceSpan)
    (leftFound rightFound : Option TokenKind)
    (leftExpected rightExpected : NonemptyList ParseExpectation)
    (leftContext rightContext : ParseContext)
    (retained : ¬ LexicalCascadeSuppresses file.content (lexical.map (·.span)) span) :
    filterParseDiagnostics file lexical [
      { span, kind := .unexpected leftFound leftExpected leftContext },
      { span, kind := .unexpected rightFound rightExpected rightContext },
      { span, kind := .unexpected leftFound leftExpected leftContext }
    ] = [
      { span, kind := .unexpected leftFound leftExpected leftContext },
      { span, kind := .unexpected rightFound rightExpected rightContext },
      { span, kind := .unexpected leftFound leftExpected leftContext }
    ] := by
  apply filterParseDiagnostics_eq_of_cascadeFilters
  exact .keep (fun h => retained h.2)
    (.keep (fun h => retained h.2) (.keep (fun h => retained h.2) .nil))

end Solcore.Test.SyntaxParserParseDiagnosticCascadeProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserUnexpectedDiagnosticCascadeProperties
/-! Consumers retain the complete expectation metadata across cascade filtering. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserUnexpectedDiagnosticCascadeProperties

open Solcore
open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    (found : Option TokenKind) (expected : NonemptyList ParseExpectation)
    (context : ParseContext) (raw kept : List SourceSpan)
    (filtered : LexicalCascadeFilters file.content (lexical.map (·.span)) raw kept) :
    filterParseDiagnostics file lexical (unexpectedDiagnostics found expected context raw) =
      unexpectedDiagnostics found expected context kept :=
  (filterParseDiagnostics_unexpected_iff file lexical found expected context raw kept).mp
    filtered

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    (found : Option TokenKind) (expected : NonemptyList ParseExpectation)
    (context : ParseContext) (raw kept : List SourceSpan)
    (result : filterParseDiagnostics file lexical
      (unexpectedDiagnostics found expected context raw) =
        unexpectedDiagnostics found expected context kept) :
    LexicalCascadeFilters file.content (lexical.map (·.span)) raw kept :=
  (filterParseDiagnostics_unexpected_iff file lexical found expected context raw kept).mpr
    result

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    (found : Option TokenKind) (expected : NonemptyList ParseExpectation)
    (context : ParseContext) (span : SourceSpan)
    (retained : ¬ LexicalCascadeSuppresses file.content (lexical.map (·.span)) span) :
    filterParseDiagnostics file lexical [{ span, kind := .unexpected found expected context }] =
      [{ span, kind := .unexpected found expected context }] :=
  filterParseDiagnostics_unexpected_of_filters file lexical found expected context
    (.keep retained .nil)

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    (found : Option TokenKind) (expected : NonemptyList ParseExpectation)
    (context : ParseContext) (span : SourceSpan)
    (suppressed : LexicalCascadeSuppresses file.content (lexical.map (·.span)) span) :
    filterParseDiagnostics file lexical [{ span, kind := .unexpected found expected context }] =
      [] :=
  filterParseDiagnostics_unexpected_of_filters file lexical found expected context
    (.drop suppressed .nil)

end Solcore.Test.SyntaxParserUnexpectedDiagnosticCascadeProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserUpstreamDiagnosticPolicy
/-!
Compatibility regressions for the four pinned upstream malformed fixtures for
which Solcore Lean deliberately retains an additional recovery diagnostic.
-/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private def policySource (name : String) : SourceId := {
  origin := .main
  path := s!"upstream/parse/{name}/main.sol"
}

private def assemblyUnclosedCall : String := String.intercalate "\n" [
  "function f() returns (word) {",
  "    let r : word;",
  "    assembly {",
  "        r := add(1,",
  "    }",
  "    return r;",
  "}",
  ""
]

private def twoErrorsRecovery : String := String.intercalate "\n" [
  "function f() returns (word) {",
  "    let x = ;",
  "    return 0;",
  "}",
  "",
  "function g(y: word) returns (word) {",
  "    if ( y ) { return 1; }",
  "    return 0;",
  "}",
  "",
  "function h() returns (word) {",
  "    return (1;",
  "}",
  ""
]

private def parameterRecovery : String := String.intercalate "\n" [
  "function bad(x:, y: U) {}",
  "function ok() {}",
  ""
]

private def signatureMissingType : String := String.intercalate "\n" [
  "function bad(x: ) {}",
  ""
]

private def assertEqual_variant {α : Type} [BEq α] [Repr α]
    (actual expected : α) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def diagnosticShape (diagnostic : ParseDiagnostic) :
    ByteRange × ParseDiagnosticKind :=
  ((diagnostic.span.startByte, diagnostic.span.endByte), diagnostic.kind)

private def checkedParse_variant (name source : String) : IO ParseOutput := do
  let file : SourceFile := { id := policySource name, content := source }
  match Parser.parse file with
  | .error error => throw (IO.userError
      s!"{name}: parser invariant failed: {reprStr error}")
  | .ok output =>
      assertEqual_variant output.lexicalDiagnostics [] s!"{name} lexical diagnostics"
      unless output.parseDiagnostics.all
          (fun diagnostic => diagnostic.span.isValidFor file) do
        throw (IO.userError s!"{name}: invalid parse diagnostic span")
      pure output

private def unexpected (found : TokenKind)
    (head : ParseExpectation) (tail : List ParseExpectation)
    (context : ParseContext) : ParseDiagnosticKind :=
  .unexpected (some found) { head, tail } context

private def functionName? (item : TopItem) : Option String :=
  match item.value with
  | .function declaration => some declaration.value.signature.name.value
  | _ => none

private def testAssemblyUnclosedCall : IO Unit := do
  let output ← checkedParse_variant "ergo_assembly_unclosed_call" assemblyUnclosedCall
  assertEqual_variant (output.parseDiagnostics.map diagnosticShape) [
    ((79, 80), unexpected (.symbol .leftParen)
      .yulIdentifier [.yulLiteral] .yulExpression),
    ((79, 81), .recovered .yulExpression),
    ((81, 82), unexpected (.symbol .comma)
      .yulIdentifier [.yulLiteral] .yulExpression),
    ((81, 82), .recovered .yulStatement)
  ] "assembly diagnostic policy"
  match output.parsed.items with
  | [{ value := .function declaration, .. }] =>
      assertEqual_variant declaration.value.signature.name.value "f"
        "assembly function name"
      match declaration.value.body.value with
      | [
          { value := .letDecl .., .. },
          { value := .assembly [
              { value := .assign .., .. },
              { value := .expression { value := .error, .. }, .. },
              { value := .error, .. }
            ], .. },
          { value := .returnStmt .., .. }
        ] => pure ()
      | body => throw (IO.userError
          s!"assembly recovery AST changed: {reprStr body}")
  | items => throw (IO.userError
      s!"assembly items changed: {reprStr items}")

private def testTwoErrorsRecovery : IO Unit := do
  let output ← checkedParse_variant "ergo_two_errors_recovery" twoErrorsRecovery
  assertEqual_variant (output.parseDiagnostics.map diagnosticShape) [
    ((42, 43), unexpected (.symbol .semicolon)
      .expression [] .expression),
    ((185, 186), unexpected (.symbol .semicolon)
      (.symbol .rightParen) [] .expression),
    ((183, 185), .recovered .expressionAtom)
  ] "two-error diagnostic policy"
  assertEqual_variant (output.parsed.items.map functionName?)
    [some "f", some "g", some "h"] "two-error declaration retention"
  match output.parsed.items with
  | [
      { value := .function first, .. },
      { value := .function middle, .. },
      { value := .function last, .. }
    ] =>
      match first.value.body.value, middle.value.body.value,
          last.value.body.value with
      | [
          { value := .expression { value := .error, .. } true, .. },
          { value := .returnStmt .., .. }
        ], [
          { value := .ifThen .., .. },
          { value := .returnStmt .., .. }
        ], [
          { value := .returnStmt (some { value := .error, .. }), .. }
        ] => pure ()
      | firstBody, middleBody, lastBody => throw (IO.userError
          s!"two-error recovery AST changed: {reprStr firstBody}; \
            {reprStr middleBody}; {reprStr lastBody}")
  | items => throw (IO.userError
      s!"two-error items changed: {reprStr items}")

private def testParameterRecovery : IO Unit := do
  let output ← checkedParse_variant "function_param_recovery" parameterRecovery
  assertEqual_variant (output.parseDiagnostics.map diagnosticShape) [
    ((15, 16), unexpected (.symbol .comma) .typeExpr [] .typeExpr),
    ((13, 15), .recovered .functionParameter)
  ] "parameter diagnostic policy"
  assertEqual_variant (output.parsed.items.map functionName?)
    [some "bad", some "ok"] "parameter declaration retention"
  match output.parsed.items with
  | [
      { value := .function bad, .. },
      { value := .function good, .. }
    ] =>
      match bad.value.signature.parameters.elements,
          good.value.signature.parameters.elements with
      | [
          { value := .error, .. },
          { value := .typed none { value := "y", .. } _, .. }
        ], [] => pure ()
      | badParameters, goodParameters => throw (IO.userError
          s!"parameter recovery AST changed: {reprStr badParameters}; \
            {reprStr goodParameters}")
  | items => throw (IO.userError
      s!"parameter recovery items changed: {reprStr items}")

private def testSignatureMissingType : IO Unit := do
  let output ← checkedParse_variant "function_signature_missing_type"
    signatureMissingType
  assertEqual_variant (output.parseDiagnostics.map diagnosticShape) [
    ((16, 17), unexpected (.symbol .rightParen) .typeExpr [] .typeExpr),
    ((13, 15), .recovered .functionParameter)
  ] "missing-type diagnostic policy"
  match output.parsed.items with
  | [{ value := .function declaration, .. }] =>
      assertEqual_variant declaration.value.signature.name.value "bad"
        "missing-type function name"
      match declaration.value.signature.parameters.elements with
      | [{ value := .error, .. }] => pure ()
      | parameters => throw (IO.userError
          s!"missing-type recovery AST changed: {reprStr parameters}")
  | items => throw (IO.userError
      s!"missing-type items changed: {reprStr items}")

/-- Run pinned malformed-upstream diagnostic and recovery-policy regressions. -/
def testSyntaxParserUpstreamDiagnosticPolicy : IO Unit := do
  testAssemblyUnclosedCall
  testTwoErrorsRecovery
  testParameterRecovery
  testSignatureMissingType

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserUpstreamFixtures
/-!
Pinned positive parser fixtures from `solcore-rs` commit
`18fd9f75d290df0070e21ee56e0a5691f232596f`.

The sources are embedded so this regression does not depend on an external
checkout at test time.
-/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private def fixture (name : String) (lines : List String) : String × String :=
  (name, String.intercalate "\n" lines ++ "\n")

private def upstreamOkFixtures : List (String × String) := [
  fixture "body_return_min.sol" [
    "function main() returns (word) {",
    "  return 1;",
    "}"
  ],
  fixture "comptime_match_label.sol" [
    "function classify(x: word) returns (word) {",
    "  match (x) {",
    "case comptime 1 {",
    "return 1;",
    "}",
    "default {",
    "return 0;",
    "}",
    "}",
    "}"
  ],
  fixture "comptime_modifier.sol" [
    "type comptime = word;",
    "",
    "contract ComptimeModifier {",
    "  function f(comptime x: word) returns (comptime<word>) {",
    "    return x;",
    "  }",
    "",
    "  function identifier(x: comptime) returns (comptime) {",
    "    let comptime : word = 1;",
    "    let y : comptime<word> = f(comptime);",
    "    return y;",
    "  }",
    "}"
  ],
  fixture "contract_modifiers_constructor_fallback.sol" [
    "contract Modifiers {",
    "  constructor() {}",
    "",
    "  function ping() public {}",
    "",
    "  function deposit() public payable returns (uint256) {",
    "    return 0;",
    "  }",
    "",
    "  fallback() payable {}",
    "}"
  ],
  fixture "dot_ctor_expr_pattern.sol" [
    "enum Option { None, Some(word) }",
    "",
    "function mkSome(x: word) returns (Option) {",
    "  return .Some(x);",
    "}",
    "",
    "function fromOption(x: Option) returns (word) {",
    "  match (x) {",
    "case .Some(v) {",
    "return v;",
    "}",
    "case .None {",
    "return 0;",
    "}",
    "}",
    "}"
  ],
  fixture "export_operator_list.sol" [
    "export { f, (^^) };"
  ],
  fixture "expression_bodied.sol" [
    "function zero() returns (word) {",
    "  0",
    "}",
    "",
    "function apply<a, b>(f: function(a) returns (b), x: a) returns (b) {",
    "  f(x)",
    "}",
    "",
    "function choose<a>(c: bool, a: a, b: a) returns (a) {",
    "   c  ?  a  :  b",
    "}",
    "",
    "function keepThen(then: word) returns (word) {",
    "  then",
    "}"
  ],
  fixture "for_loop.sol" [
    "function sum10() returns (word) {",
    "  let s : word = 0;",
    "  for (let i = 1; i <= 10; i = i + 1) {",
    "    s = s + i;",
    "  }",
    "  return s;",
    "}"
  ],
  fixture "import_alias_operator_hiding.sol" [
    "import {A as B, (^^)} from mod hiding {C};"
  ],
  fixture "import_external_alias.sol" [
    "import * as X from @lib.a.b;"
  ],
  fixture "import_mixed_wildcard.sol" [
    "import * from glob;",
    "import * from glob2;",
    "import * from glob3;"
  ],
  fixture "import_wildcard_selector.sol" [
    "import * from mod;"
  ],
  fixture "match_arm_block.sol" [
    "function main(foo: (word, word)) returns (word) {",
    "  let res: word;",
    "  match (foo) {",
    "case (v0, v1) {",
    "{",
    "    let x: word = v1;",
    "    res = x;",
    "  }",
    "}",
    "}",
    "  return res;",
    "}"
  ],
  fixture "match_trailing_semicolon.sol" [
    "function f() {",
    "  match (0) {",
    "default {",
    "return ();",
    "}",
    "}",
    "}"
  ],
  fixture "no_diagnostics.sol" [
    "function ok() {}"
  ],
  fixture "operators_compound_assign.sol" [
    "function operators(x: word, y: word, z: word) returns (word) {",
    "  let acc = x % y;",
    "  acc = (acc & y) | (x ^ z);",
    "  acc += x;",
    "  acc -= y;",
    "  acc ^= z;",
    "  acc &= x;",
    "  acc |= y;",
    "  acc %= z;",
    "  return acc;",
    "}"
  ],
  fixture "parser_catchup_h.sol" [
    "enum First { First(word) }",
    "enum Second { Second }",
    "",
    "export mod;",
    "export mod as M;",
    "export mod.{a};",
    "export { T(*) };",
    "",
    "import {T} from m;"
  ],
  fixture "proxy_expression.sol" [
    "function main(x: word) returns (word) {",
    "  let p = @word;",
    "  let pairProxy = @(word, word);",
    "  let annotated = p ;",
    "  return x;",
    "}"
  ],
  fixture "proxy_type_sugar.sol" [
    "function proxy_sig(x: @word) returns (@word) {}"
  ],
  fixture "qualified_constructor_pattern_3_segment.sol" [
    "function main(x: mod.Type.Bool) returns (word) {",
    "  match (x) {",
    "case mod.Type.True {",
    "return 1;",
    "}",
    "default {",
    "return 0;",
    "}",
    "}",
    "}"
  ],
  fixture "qualified_constructor_patterns.sol" [
    "contract QualifiedConstructorPatterns {",
    "  enum Option<a> { None, Some(a) }",
    "",
    "  function join<a>(mmx: Option<Option<a>>) returns (Option<a>) {",
    "    match (mmx) {",
    "case Option.None {",
    "return Option.None;",
    "}",
    "case Option.Some(Option.Some(x)) {",
    "return Option.Some(x);",
    "}",
    "case Option.Some(Option.None) {",
    "return Option.None;",
    "}",
    "}",
    "  }",
    "}"
  ],
  fixture "qualified_type_return.sol" [
    "function qualified_ret() returns (mod.Type) {}"
  ],
  fixture "tuple_unit_sail.sol" [
    "enum Pair<a, b> { Pair(a, b) }",
    "",
    "function fst<a, b>(p: (a, b)) returns (a) {",
    "  match (p) {",
    "case (x, y) {",
    "return x;",
    "}",
    "}",
    "}",
    "",
    "function tupleValue() returns (word, word) {",
    "  return (1, 0);",
    "}",
    "",
    "function unitValue() {",
    "  return ();",
    "}",
    "",
    "function nestedTupleUnitPattern(p: ((), (word, word))) returns (word) {",
    "  match (p) {",
    "case ((), (x, y)) {",
    "return x;",
    "}",
    "}",
    "}",
    "",
    "function groupedSinglePattern(p: word) returns (word) {",
    "  match (p) {",
    "case (y) {",
    "return y;",
    "}",
    "}",
    "}",
    "",
    "function pairData(x: word, y: word) returns (Pair<word, word>) {",
    "  return Pair(x, y);",
    "}"
  ]
]

private def hasRecoveryItem : TopItem → Bool
  | { value := .error, .. } => true
  | { value := .contract declaration, .. } =>
      declaration.value.members.any fun member => member.value == .error
  | _ => false

private def checkFixture (name content : String) : IO Unit := do
  let file : SourceFile := {
    id := { origin := .main, path := s!"upstream-ok/{name}" }
    content
  }
  let output ← match Parser.parse file with
    | .ok output => pure output
    | .error error => throw (IO.userError
        s!"{name}: parser invariant failed: {reprStr error}")
  unless output.lexicalDiagnostics.isEmpty do
    throw (IO.userError
      s!"{name}: lexical diagnostics: {reprStr output.lexicalDiagnostics}")
  unless output.parseDiagnostics.isEmpty do
    throw (IO.userError
      s!"{name}: parse diagnostics: {reprStr output.parseDiagnostics}")
  unless output.parsed.span.isValidFor file &&
      output.parsed.items.all (fun item => item.span.isValidFor file) do
    throw (IO.userError s!"{name}: invalid parsed span")
  if output.parsed.items.any hasRecoveryItem then
    throw (IO.userError s!"{name}: retained a declaration recovery node")

def testSyntaxParserUpstreamFixtures : IO Unit := do
  unless upstreamOkFixtures.length == 23 do
    throw (IO.userError "pinned upstream fixture catalog must contain 23 files")
  for (name, content) in upstreamOkFixtures do
    checkFixture name content

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxPreflightNestingProperties
/-! External consumers for nesting-diagnostic provenance. -/

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @NestingContext
example := @NestingDimension
example := @NestingOverflow
example := @NestingScans
example := @NestingOutcome
example := @NestingClears
example := @NestingExceeds
example := @NestingScans.result_unique
example := @NestingScans.exists_result
example := @NestingExceeds.disjointClears
example := @NestingExceeds.overflow_unique
example := @nestingOutcome_total
example := @nestingOverflowDiagnostic
example := @checkNesting_eq_map_of_outcome
example := @checkNesting_reflects_outcome
example := @checkNesting_none_iff_nestingClears
example := @checkNesting_some_iff_nestingExceeds
example := @checkNesting_ordinaryOutcome_sound
example := @checkNesting_some_span_validFor
example := @checkNesting_lexed_some_span_validFor

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxPreflightProperties
/-! External compile consumers for canonical parser preflight laws. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @IndexedSpan
example := @LexedValidationFailure
example := @OrderedSpanAccepted
example := @OrderedSpanValidationScans
example := @SpanValidationScans
example := @TokenSpanValidationScans
example := @CommentSpanValidationScans
example := @LexicalDiagnosticSpanValidationScans
example := @LexedFileValidationOutcome
example := @LexedFileValidationAccepts
example := @LexedFileValidationRejects
example := @OrderedSpanValidationScans.result_unique
example := @OrderedSpanValidationScans.exists_result
example := @OrderedSpanValidationScans.none_iff_spanSequenceValidFor
example := @SpanValidationScans.result_unique
example := @SpanValidationScans.exists_result
example := @SpanValidationScans.none_iff_forall_validFor
example := @LexedFileValidationOutcome.exists_result
example := @LexedFileValidationOutcome.result_unique
example := @lexedFileValidationOutcome_total
example := @LexedFileValidationRejects.disjointAccepts
example := @LexedFileValidationRejects.failure_unique
example := @lexedFileValidationAccepts_iff_validFor
example := @lexedValidationInvariantError
example := @validateLexed_eq_result_of_outcome
example := @validateLexed_reflects_outcome
example := @validateLexed_ok_iff_validationAccepts
example := @validateLexed_error_iff_validationRejects
example := @productionParseLexed_error_iff_validateLexed_error
example := @productionParseLexed_error_iff_validationRejects
example := @productionParseLexed_certifiedOutcome

example (file : SourceFile) (lexed : LexedFile)
    (result : Lexer.lex file = .ok lexed) :
    validateLexed file lexed = .ok () :=
  lex_ok_validateLexed file lexed result

example (file : SourceFile) (lexed : LexedFile)
    (lexing : Lexer.lex file = .ok lexed)
    (error : ParserInvariantError)
    (validation : validateLexed file lexed = .error error) : False :=
  lex_ok_validateLexed_error_impossible file lexed lexing error validation

example (file : SourceFile) (lexed : LexedFile) :
    validateLexed file lexed = .ok () ↔ lexed.ValidFor file :=
  validateLexed_ok_iff_validFor file lexed

example (file : SourceFile) (lexed : LexedFile)
    (accepted : validateLexed file lexed = .ok ()) :
    lexed.source = file.id :=
  (validateLexed_ok_validFor file lexed accepted).source_eq

example (file : SourceFile) (lexed : LexedFile)
    (accepted : validateLexed file lexed = .ok ())
    (token : Token) (member : token ∈ lexed.tokens) :
    token.span.ValidFor file :=
  (validateLexed_ok_validFor file lexed accepted).token_span member

example (file : SourceFile) (lexed : LexedFile)
    (accepted : validateLexed file lexed = .ok ())
    (comment : Comment) (member : comment ∈ lexed.comments) :
    comment.span.ValidFor file :=
  (validateLexed_ok_validFor file lexed accepted).comment_span member

example (file : SourceFile) (lexed : LexedFile)
    (accepted : validateLexed file lexed = .ok ())
    (diagnostic : LexicalDiagnostic)
    (member : diagnostic ∈ lexed.diagnostics) :
    diagnostic.span.ValidFor file :=
  (validateLexed_ok_validFor file lexed accepted).diagnostic_span member

example (file : SourceFile) (lexed : LexedFile)
    (accepted : validateLexed file lexed = .ok ()) :
    SpanSequence.ValidFor file (fun token : Token => token.span)
      0 lexed.tokens :=
  (validateLexed_ok_validFor file lexed accepted).tokens

example (file : SourceFile) (lexed : LexedFile)
    (accepted : validateLexed file lexed = .ok ())
    (token : Token) (rest : List Token)
    (startsWith : lexed.tokens = token :: rest) :
    token.span.ValidFor file ∧
      0 ≤ token.span.startByte ∧
      token.span.startByte < token.span.endByte ∧
      SpanSequence.ValidFor file (fun item : Token => item.span)
        token.span.endByte rest := by
  have valid := (validateLexed_ok_validFor file lexed accepted).tokens
  rw [startsWith] at valid
  exact valid

example (file : SourceFile) (lexed : LexedFile) (output : ParseOutput)
    (parsed : parseLexed file lexed = .ok output) :
    lexed.ValidFor file :=
  parseLexed_ok_input_validFor file lexed output parsed

example (file : SourceFile) (output : ParseOutput)
    (parsed : parse file = .ok output) :
    ∃ lexed,
      Lexer.lex file = .ok lexed ∧
      parseLexed file lexed = .ok output ∧
      lexed.ValidFor file ∧
      output.tokens = lexed.tokens ∧
      output.lexicalDiagnostics = lexed.diagnostics ∧
      output.parsed.comments = lexed.comments :=
  parse_ok_valid_lexed_provenance file output parsed

example (file : SourceFile) (output : ParseOutput)
    (parsed : parse file = .ok output)
    (token : Token) (member : token ∈ output.tokens) :
    token.span.ValidFor file :=
  parse_ok_tokens_validFor file output parsed token member

example (file : SourceFile) (output : ParseOutput)
    (parsed : parse file = .ok output)
    (comment : Comment) (member : comment ∈ output.parsed.comments) :
    comment.span.ValidFor file :=
  parse_ok_comments_validFor file output parsed comment member

example (file : SourceFile) (output : ParseOutput)
    (parsed : parse file = .ok output)
    (diagnostic : LexicalDiagnostic)
    (member : diagnostic ∈ output.lexicalDiagnostics) :
    diagnostic.span.ValidFor file :=
  parse_ok_lexicalDiagnostics_validFor file output parsed diagnostic member

example (file : SourceFile) (output : ParseOutput)
    (parsed : parse file = .ok output) :
    SpanSequence.ValidFor file (fun token : Token => token.span)
      0 output.tokens :=
  parse_ok_tokens_sequence_validFor file output parsed

example (file : SourceFile) (output : ParseOutput)
    (parsed : parse file = .ok output) :
    SpanSequence.ValidFor file (fun comment : Comment => comment.span)
      0 output.parsed.comments :=
  parse_ok_comments_sequence_validFor file output parsed

example (file : SourceFile) (tokens : List Token)
    (valid : SpanSequence.ValidFor file (fun token : Token => token.span)
      0 tokens) (token : Token) (member : token ∈ tokens) :
    0 ≤ token.span.startByte ∧
      token.span.startByte < token.span.endByte :=
  ⟨valid.previousEnd_le_start member, valid.span_nonempty member⟩

example (file : SourceFile) (output : ParseOutput)
    (parsed : parse file = .ok output) :
    output.tokens.Pairwise fun left right =>
      left.span.endByte ≤ right.span.startByte :=
  parse_ok_tokens_pairwise_nonoverlap file output parsed

example (file : SourceFile) (output : ParseOutput)
    (parsed : parse file = .ok output) :
    output.parsed.comments.Pairwise fun left right =>
      left.span.endByte ≤ right.span.startByte :=
  parse_ok_comments_pairwise_nonoverlap file output parsed

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxTraceCompletenessFromSoundnessProperties
/-! The real Boolean-first checked-name leaf consumes all four generic APIs.
Earlier diagnostics are arbitrary, including malformed spans. Countermodels
separate independent exactness, vacuous completeness, and actual existence. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxTraceCompletenessFromSoundnessProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

private theorem name_sound : ParserTraceSuccessSound expressionName ExpressionNameTraceParses :=
  expressionName_success_trace_sound

private theorem name_reject_sound : ParserTraceRejectSound expressionName ExpressionNameTraceRejects := by
  intro input rejected failure result
  have reflected := expressionName_reject_trace_sound result
  exact ⟨[], reflected.1, by rw [reflected.2]; simp only [List.append_nil]⟩

private theorem name_joint (source : SourceId) (endByte : Nat) :
    TraceExactOutcomeSpec ExpressionNameTraceParses ExpressionNameTraceRejects source endByte where
  successResultUnique := ExpressionNameTraceParses.result_unique
  rejectResultUnique := ExpressionNameTraceRejects.result_unique
  successRejectDisjoint := by
    rintro _ _ _ _ rejected ⟨_, _, _, parsed⟩
    exact rejected.disjoint_success parsed

theorem checked_name_success_from_soundness
    {input : State} (prior : List ParseDiagnostic) {name : Identifier} {after : Remainder}
    {trace : List ParseDiagnostic}
    (parsed : ExpressionNameTraceParses input.file.id input.window.endByte input.declarativeRemainder name after trace) :
    ∃ output, expressionName { input with diagnosticsRev := prior.reverse } = .ok name output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = prior ++ trace := by
  have result := trace_success_exists_ok_of_sound name_sound name_reject_sound
    (input := { input with diagnosticsRev := prior.reverse })
    (name_joint input.file.id input.window.endByte)
    (expressionName_ne_invariant _) parsed
  simpa only [State.diagnostics, List.reverse_reverse] using result

theorem checked_name_rejection_from_soundness
    {input : State} (prior : List ParseDiagnostic) {after : Remainder} {report : ParseDiagnostic}
    {trace : List ParseDiagnostic}
    (rejection : ExpressionNameTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace) :
    ∃ failure output, expressionName { input with diagnosticsRev := prior.reverse } = .reject failure output ∧
      output.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧ output.diagnostics = prior ++ trace := by
  have result := trace_reject_exists_reject_of_sound name_sound name_reject_sound
    (input := { input with diagnosticsRev := prior.reverse })
    (name_joint input.file.id input.window.endByte)
    (expressionName_ne_invariant _) rejection
  simpa only [State.diagnostics, List.reverse_reverse] using result

theorem checked_name_success_contract_from_soundness :
    ParserTraceSuccessComplete expressionName ExpressionNameTraceParses :=
  trace_success_complete_of_sound name_sound name_reject_sound name_joint expressionName_ne_invariant

theorem checked_name_rejection_contract_from_soundness :
    ParserTraceRejectComplete expressionName ExpressionNameTraceRejects :=
  trace_reject_complete_of_sound name_sound name_reject_sound name_joint expressionName_ne_invariant

private theorem identifier_has_no_boolean {input : State} {name : Identifier}
    (present : TokenAt input.tokens input.window.endIndex input.cursor { span := name.span, value := .identifier name.value }) :
    BooleanPatternAbsentAt input.declarativeRemainder := by
  constructor <;> rintro ⟨span, other⟩
  all_goals have impossible := congrArg (·.value) (present.token_unique other)
  all_goals cases impossible

theorem hyphen_event_follows_every_prior
    {input : State} (prior : List ParseDiagnostic) {name : Identifier}
    (present : TokenAt input.tokens input.window.endIndex input.cursor { span := name.span, value := .identifier name.value })
    (hyphen : IdentifierHyphenSpelling name.value) :
    ∃ output, expressionName { input with diagnosticsRev := prior.reverse } = .ok name output ∧
      output = { input with
        cursor := input.cursor + 1
        diagnosticsRev := { span := name.span, kind := .invalidIdentifierHyphen name.value } :: prior.reverse } ∧
      output.diagnostics = prior ++ [{ span := name.span, kind := .invalidIdentifierHyphen name.value }] := by
  have parsed : ExpressionNameTraceParses input.file.id input.window.endByte input.declarativeRemainder name
      { input.declarativeRemainder with cursor := input.cursor + 1 }
      [{ span := name.span, kind := .invalidIdentifierHyphen name.value }] :=
    .identifier (identifier_has_no_boolean present) (.parsed ⟨present, rfl, rfl, rfl⟩ (.hyphen hyphen))
  rcases checked_name_success_from_soundness prior parsed with ⟨output, result, _, events⟩
  exact ⟨output, result, expressionName_success_state_eq_of_trace result parsed, events⟩

private def plusFailure (span : SourceSpan) : Failure := {
  span, found := some (.symbol .plus)
  expected := { head := .identifier, tail := [] }, context := .expression
}

theorem plus_rejection_never_commits_report
    {input : State} (prior : List ParseDiagnostic) {span : SourceSpan}
    (present : TokenAt input.tokens input.window.endIndex input.cursor { span, value := .symbol .plus }) :
    expressionName { input with diagnosticsRev := prior.reverse } =
      .reject (plusFailure span) { input with diagnosticsRev := prior.reverse } ∧
    ({ input with diagnosticsRev := prior.reverse } : State).diagnostics = prior := by
  have absent : BooleanPatternAbsentAt input.declarativeRemainder := by
    constructor <;> rintro ⟨otherSpan, other⟩
    all_goals have impossible := congrArg (·.value) (present.token_unique other)
    all_goals cases impossible
  have noName : IdentifierAbsentAt input.declarativeRemainder := by
    rintro ⟨otherSpan, text, other⟩
    have impossible := congrArg (·.value) (present.token_unique other)
    cases impossible
  have rejection : ExpressionNameTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      input.declarativeRemainder (plusFailure span).toDiagnostic [] :=
    ⟨absent, .absent noName,
      .reported (CurrentInputAt.token (source := input.file.id) (endByte := input.window.endByte)
        (input := input.declarativeRemainder) present), rfl⟩
  rcases checked_name_rejection_from_soundness prior rejection with ⟨failure, output, result, _, reportEq, events⟩
  have stateEq := (expressionName_reject_trace_sound result).2
  cases Failure.toDiagnostic_injective reportEq
  exact ⟨stateEq ▸ result, by simpa only [stateEq, List.append_nil] using events⟩

private def stops (input : State) : Reply Unit :=
  .invariant (.fuelExhausted .typeExpr input.currentSpan)

private def phantom (_source : SourceId) (_endByte : Nat) (input : Remainder)
    (_value : Unit) (output : Remainder) (trace : List ParseDiagnostic) : Prop :=
  output = input ∧ trace = []

private def emptySuccess (_source : SourceId) (_endByte : Nat) (_input : Remainder)
    (_value : Unit) (_output : Remainder) (_trace : List ParseDiagnostic) : Prop := False

private def emptyRejection (_source : SourceId) (_endByte : Nat) (_input _output : Remainder)
    (_report : ParseDiagnostic) (_trace : List ParseDiagnostic) : Prop := False

private theorem phantom_joint (source : SourceId) (endByte : Nat) :
    TraceExactOutcomeSpec phantom emptyRejection source endByte where
  successResultUnique := by
    rintro input ⟨⟩ ⟨⟩ _ _ _ _ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  rejectResultUnique := by intro _ _ _ _ _ _ _ impossible; exact False.elim impossible
  successRejectDisjoint := by intro _ _ _ _ impossible; exact False.elim impossible

/-- Both soundness contracts and a nonempty exact success grammar can coexist
with invariant-only execution. The explicit exclusion premise cannot be dropped. -/
theorem sound_joint_does_not_replace_invariant_exclusion (input : State) :
    TraceExactOutcomeSpec phantom emptyRejection input.file.id input.window.endByte ∧
    ParserTraceSuccessSound stops phantom ∧ ParserTraceRejectSound stops emptyRejection ∧
    phantom input.file.id input.window.endByte input.declarativeRemainder () input.declarativeRemainder [] ∧
    (¬ ∃ output, stops input = .ok () output) ∧
    (¬ ∀ error, stops input ≠ .invariant error) := by
  refine ⟨phantom_joint _ _, ?_, ?_, ⟨rfl, rfl⟩, ?_, ?_⟩
  · intro _ _ _ impossible; cases impossible
  · intro _ _ _ impossible; cases impossible
  · rintro ⟨_, impossible⟩; cases impossible
  · intro excluded
    exact excluded (.fuelExhausted .typeExpr input.currentSpan) rfl

/-- Empty grammars have vacuous completeness even when the parser never gives
an ordinary reply. These contracts do not assert outcome existence. -/
theorem empty_completeness_does_not_assert_existence (input : State) :
    TraceExactOutcomeSpec emptySuccess emptyRejection input.file.id input.window.endByte ∧
    ParserTraceSuccessComplete stops emptySuccess ∧ ParserTraceRejectComplete stops emptyRejection ∧
    (¬ ((∃ value output, stops input = .ok value output) ∨
      ∃ failure output, stops input = .reject failure output)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact {
      successResultUnique := by intro _ _ _ _ _ _ _ impossible; exact False.elim impossible
      rejectResultUnique := by intro _ _ _ _ _ _ _ impossible; exact False.elim impossible
      successRejectDisjoint := by intro _ _ _ _ impossible; exact False.elim impossible
    }
  · intro _ _ _ _ impossible; exact False.elim impossible
  · intro _ _ _ _ impossible; exact False.elim impossible
  · rintro (⟨_, _, impossible⟩ | ⟨_, _, impossible⟩) <;> cases impossible

end Solcore.Test.SyntaxTraceCompletenessFromSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxUnrestrictedFuelElementContractProperties
/-! The unrestricted contract permits a child to replace source, tokens,
endByte, and diagnostics, and even to advance past endIndex. Actual delimiter
execution still reaches an ordinary outcome. These are intentionally synthetic
children, not diagnostic-trace or state-validity contracts. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxUnrestrictedFuelElementContractProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

private def originalFile : SourceFile := {
  id := { origin := .main, path := "unrestricted-original.sol" }, content := "("
}
private def replacementFile : SourceFile := {
  id := { origin := .external "child", path := "unrestricted-replacement.sol" }, content := ""
}
private def childEvent : ParseDiagnostic := {
  span := { source := replacementFile.id, startByte := 0, endByte := 0 }
  kind := .invalidIdentifierHyphen "synthetic-child"
}
private def openingToken : Token := {
  span := { source := originalFile.id, startByte := 0, endByte := 1 }, value := .symbol .leftParen
}
private def fixture (prior : List ParseDiagnostic) : State := {
  file := originalFile, tokens := #[openingToken], cursor := 0
  window := { endIndex := 1, endByte := 1 }, diagnosticsRev := prior.reverse
}
private def rewritten (input : State) : State := {
  file := replacementFile, tokens := #[], cursor := input.cursor + 10
  window := { endIndex := input.window.endIndex, endByte := 19 }, diagnosticsRev := [childEvent]
}
private def rewritingChild : Parser Nat := fun input => .ok 7 (rewritten input)
private def finalState : State := {
  file := replacementFile, tokens := #[], cursor := 11
  window := { endIndex := 1, endByte := 19 }, diagnosticsRev := [childEvent]
}
private def missingDelimiter : Failure := {
  span := { source := replacementFile.id, startByte := 19, endByte := 19 }, found := none
  expected := { head := .symbol .comma, tail := [.symbol .rightParen] }, context := .typeExpr
}

theorem rewriting_child_contract (fuel : Nat) : UnrestrictedFuelElementContract rewritingChild fuel where
  endIndexOnSuccess result := by
    simp only [rewritingChild] at result
    cases result
    rfl
  cursorLtOnSuccess result := by
    simp only [rewritingChild] at result
    cases result
    simp only [rewritten]
    omega
  ordinary input _ := Or.inl ⟨7, rewritten input, rfl⟩

/-- Every delimiter policy accepts this minimal contract on arbitrary states. -/
theorem arbitrary_policy_ordinary (opening closing : Symbol) (allowEmpty allowTrailing : Bool)
    (context : ParseContext) (phase : ParserPhase) (fuel : Nat) (input : State)
    (adequate : input.remainingCount < fuel + 1) :
    (∃ values next, delimitedWithPolicy opening closing allowEmpty allowTrailing rewritingChild
      context phase input = .ok values next) ∨
    (∃ failure next, delimitedWithPolicy opening closing allowEmpty allowTrailing rewritingChild
      context phase input = .reject failure next) :=
  delimitedWithPolicy_ordinary_of_unrestrictedElementFuel opening closing allowEmpty allowTrailing
    rewritingChild context phase fuel (rewriting_child_contract fuel) input adequate

/-- The child changes all non-contract fields and overshoots the retained end index. -/
theorem child_changes_frames_and_overshoots (prior : List ParseDiagnostic) :
    rewritingChild { fixture prior with cursor := 1 } = .ok 7 finalState ∧
    finalState.file.id ≠ (fixture prior).file.id ∧
    finalState.tokens ≠ (fixture prior).tokens ∧
    finalState.window.endByte ≠ (fixture prior).window.endByte ∧
    finalState.diagnosticsRev = [childEvent] ∧
    finalState.window.endIndex = (fixture prior).window.endIndex ∧
    finalState.window.endIndex < finalState.cursor := by
  exact ⟨rfl, by change replacementFile.id ≠ originalFile.id; decide,
    by change (#[] : Array Token) ≠ #[openingToken]; decide,
    by change 19 ≠ 1; decide, rfl, rfl, by decide⟩

private theorem tail_rejected :
    afterDelimitedElement rewritingChild .rightParen true .typeExpr .typeExpr openingToken 1 [7] finalState =
      .reject missingDelimiter finalState := by
  have commaAbsent : isSymbol finalState .comma = false := rfl
  have closingAbsent : isSymbol finalState .rightParen = false := rfl
  simp only [afterDelimitedElement, commaAbsent, closingAbsent, Bool.false_eq_true, if_false]
  rfl

/-- At EOF the synthetic child advances by ten, replaces all prior events,
and leaves an ordinary ordered delimiter report at its new source/endByte. -/
theorem exact_rejection_after_rewriting (prior : List ParseDiagnostic) :
    delimited .leftParen .rightParen false rewritingChild .typeExpr .typeExpr (fixture prior) =
      .reject missingDelimiter finalState ∧
    finalState.remainingCount = 0 ∧
    finalState.diagnostics = [childEvent] := by
  have token : ExactTokenParses (.symbol .leftParen) (fixture prior).declarativeRemainder
      openingToken.span ({ fixture prior with cursor := 1 } : State).declarativeRemainder :=
    ⟨by change TokenAt #[openingToken] 1 0 openingToken; exact ⟨by decide, rfl⟩, rfl⟩
  have opening : symbol .leftParen .typeExpr (fixture prior) =
      .ok openingToken { fixture prior with cursor := 1 } :=
    symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr token
  have child := (child_changes_frames_and_overshoots prior).1
  refine ⟨?_, rfl, rfl⟩
  unfold delimited delimitedWithPolicy
  rw [opening]
  simp only [Bool.false_and, Bool.false_eq_true, if_false]
  rw [child]
  change afterDelimitedElement rewritingChild .rightParen true .typeExpr .typeExpr openingToken 1 [7] finalState = _
  exact tail_rejected

/-- This endpoint violates the usual cursor and token-window bounds. -/
theorem final_state_is_not_valid : ¬ finalState.ValidFor := by
  intro valid
  have bound := valid.cursor_le_endIndex
  simp only [finalState] at bound
  omega

end Solcore.Test.SyntaxUnrestrictedFuelElementContractProperties
end
