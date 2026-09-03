import Solcore.Syntax.Parser.Trivia
import Solcore.Syntax.DeclarativeDiagnosticCascadeGrammar

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Number of LF bytes preceding a validated UTF-8 source offset. -/
private def lineIndex (source : String) (offset : Nat) : Nat :=
  match utf8Slice? source 0 offset with
  | some text => text.toList.count '\n'
  | none => 0

private def spansOverlap (left right : SourceSpan) : Bool :=
  left.source == right.source &&
    left.startByte < right.endByte && right.startByte < left.endByte

private def whitespaceAdjacent (source : String)
    (lexical parsed : SourceSpan) : Bool :=
  if lexical.endByte > parsed.startByte then
    false
  else
    match utf8Slice? source lexical.endByte parsed.startByte with
    | some gap => gap.toList.all fun character =>
        isRustWhitespace character && character != '\n' && character != '\r'
    | none => false

/--
The pinned Rust parser treats a parser error on the affected source line as a
cascade of an invalid lexical token. The overlap and horizontal-whitespace
cases are retained explicitly to keep the byte-span policy evident.
-/
private def lexicalSpanSuppresses (source : String)
    (lexical parsed : SourceSpan) : Bool :=
  lexical.source == parsed.source &&
    (lineIndex source lexical.startByte == lineIndex source parsed.startByte ||
      spansOverlap lexical parsed ||
      (lexical.startByte ≤ parsed.startByte &&
        parsed.startByte ≤ lexical.endByte) ||
      whitespaceAdjacent source lexical parsed)

/--
Only parser failures and explicit recovery markers are known lexical cascades.
Semantic grammar constraints and nesting guards have no origin metadata and
are deliberately preserved.
-/
private def isLexicalCascadeCandidate : ParseDiagnosticKind → Bool
  | .unexpected .. | .recovered .. => true
  | _ => false

private def suppressLexicalCascades (source : String)
    (lexical : List LexicalDiagnostic)
    (parsed : List ParseDiagnostic) : List ParseDiagnostic :=
  parsed.filter fun diagnostic =>
    !isLexicalCascadeCandidate diagnostic.kind ||
      !lexical.any fun lexError =>
        lexicalSpanSuppresses source lexError.span diagnostic.span

private theorem whitespaceAdjacent_eq_true_iff (source : String)
    (lexical parsed : SourceSpan) :
    whitespaceAdjacent source lexical parsed = true ↔
      DeclarativeGrammar.HorizontalWhitespaceGap source lexical parsed := by
  unfold whitespaceAdjacent DeclarativeGrammar.HorizontalWhitespaceGap
  split
  · rename_i reversed
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨ordered, _⟩
    omega
  · rename_i ordered
    have bound : lexical.endByte ≤ parsed.startByte := by omega
    cases gap : utf8Slice? source lexical.endByte parsed.startByte with
    | none => simp [bound, gap]
    | some text => simp [bound, gap]

private theorem sourceId_beq_true_iff (left right : SourceId) :
    (left == right) = true ↔ left = right := by
  cases left with
  | mk leftOrigin leftPath =>
      cases right with
      | mk rightOrigin rightPath =>
          cases leftOrigin <;> cases rightOrigin <;>
            simp [BEq.beq, instBEqSourceId.beq, instBEqSourceOrigin.beq]

private theorem lexicalSpanSuppresses_eq_true_iff (source : String)
    (lexical parsed : SourceSpan) :
    lexicalSpanSuppresses source lexical parsed = true ↔
      DeclarativeGrammar.LexicalSpanSuppresses source lexical parsed := by
  by_cases owners : lexical.source = parsed.source
  all_goals simp [lexicalSpanSuppresses, spansOverlap, lineIndex, utf8Slice?,
    DeclarativeGrammar.LexicalSpanSuppresses, DeclarativeGrammar.cascadeLineIndex,
    whitespaceAdjacent_eq_true_iff, sourceId_beq_true_iff, owners, or_assoc] <;> rfl

/-- Normalize ordinary diagnostics without consulting display prose. -/
def filterParseDiagnostics (file : SourceFile)
    (lexical : List LexicalDiagnostic)
    (parsed : List ParseDiagnostic) : List ParseDiagnostic :=
  suppressLexicalCascades file.content lexical parsed

private theorem lexicalAnySuppresses_eq_true_iff (source : String)
    (lexical : List LexicalDiagnostic) (span : SourceSpan) :
    (lexical.any fun diagnostic => lexicalSpanSuppresses source diagnostic.span span) = true ↔
      DeclarativeGrammar.LexicalCascadeSuppresses source (lexical.map (·.span)) span := by
  constructor
  · intro suppressed
    rcases List.any_eq_true.mp suppressed with ⟨diagnostic, member, spanMatches⟩
    exact ⟨diagnostic.span, List.mem_map.mpr ⟨diagnostic, member, rfl⟩,
      (lexicalSpanSuppresses_eq_true_iff source diagnostic.span span).mp spanMatches⟩
  · rintro ⟨lexicalSpan, member, spanMatches⟩
    rcases List.mem_map.mp member with ⟨diagnostic, diagnosticMember, rfl⟩
    exact List.any_eq_true.mpr ⟨diagnostic, diagnosticMember,
      (lexicalSpanSuppresses_eq_true_iff source diagnostic.span span).mpr spanMatches⟩

/-- An independently suppressed recovery event is removed at its exact list position. -/
theorem filterParseDiagnostics_cons_recovered_of_suppressed
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    (span : SourceSpan) (site : RecoverySite) (parsed : List ParseDiagnostic)
    (suppressed : DeclarativeGrammar.LexicalCascadeSuppresses
      file.content (lexical.map (·.span)) span) :
    filterParseDiagnostics file lexical ({ span, kind := .recovered site } :: parsed) =
      filterParseDiagnostics file lexical parsed := by
  have anyEq := (lexicalAnySuppresses_eq_true_iff file.content lexical span).mpr suppressed
  simp [filterParseDiagnostics, suppressLexicalCascades, isLexicalCascadeCandidate, anyEq]

/-- Without an independent suppression witness, a recovery event is retained in order. -/
theorem filterParseDiagnostics_cons_recovered_of_retained
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    (span : SourceSpan) (site : RecoverySite) (parsed : List ParseDiagnostic)
    (retained : ¬ DeclarativeGrammar.LexicalCascadeSuppresses
      file.content (lexical.map (·.span)) span) :
    filterParseDiagnostics file lexical ({ span, kind := .recovered site } :: parsed) =
      { span, kind := .recovered site } :: filterParseDiagnostics file lexical parsed := by
  cases anyEq : lexical.any (fun diagnostic =>
      lexicalSpanSuppresses file.content diagnostic.span span) with
  | false =>
      simp [filterParseDiagnostics, suppressLexicalCascades, isLexicalCascadeCandidate, anyEq]
  | true =>
      exact False.elim (retained
        ((lexicalAnySuppresses_eq_true_iff file.content lexical span).mp anyEq))

/-- An independently suppressed expectation failure is removed without changing
its surrounding trace. The found token, expectations, and context stay explicit. -/
theorem filterParseDiagnostics_cons_unexpected_of_suppressed
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    (span : SourceSpan) (found : Option TokenKind)
    (expected : NonemptyList ParseExpectation) (context : ParseContext)
    (parsed : List ParseDiagnostic)
    (suppressed : DeclarativeGrammar.LexicalCascadeSuppresses
      file.content (lexical.map (·.span)) span) :
    filterParseDiagnostics file lexical
      ({ span, kind := .unexpected found expected context } :: parsed) =
      filterParseDiagnostics file lexical parsed := by
  have anyEq := (lexicalAnySuppresses_eq_true_iff file.content lexical span).mpr suppressed
  simp [filterParseDiagnostics, suppressLexicalCascades, isLexicalCascadeCandidate, anyEq]

/-- A retained expectation failure preserves its complete metadata and position. -/
theorem filterParseDiagnostics_cons_unexpected_of_retained
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    (span : SourceSpan) (found : Option TokenKind)
    (expected : NonemptyList ParseExpectation) (context : ParseContext)
    (parsed : List ParseDiagnostic)
    (retained : ¬ DeclarativeGrammar.LexicalCascadeSuppresses
      file.content (lexical.map (·.span)) span) :
    filterParseDiagnostics file lexical
      ({ span, kind := .unexpected found expected context } :: parsed) =
      { span, kind := .unexpected found expected context } ::
        filterParseDiagnostics file lexical parsed := by
  cases anyEq : lexical.any (fun diagnostic =>
      lexicalSpanSuppresses file.content diagnostic.span span) with
  | false =>
      simp [filterParseDiagnostics, suppressLexicalCascades, isLexicalCascadeCandidate, anyEq]
  | true =>
      exact False.elim (retained
        ((lexicalAnySuppresses_eq_true_iff file.content lexical span).mp anyEq))

/-- Filtering an empty parser trace cannot introduce a diagnostic. -/
@[simp] theorem filterParseDiagnostics_nil_parsed
    (file : SourceFile) (lexical : List LexicalDiagnostic) :
    filterParseDiagnostics file lexical [] = [] := by
  simp [filterParseDiagnostics, suppressLexicalCascades]

/-- With no lexical errors, diagnostic normalization retains every parser
diagnostic exactly. -/
@[simp] theorem filterParseDiagnostics_nil_lexical
    (file : SourceFile) (parsed : List ParseDiagnostic) :
    filterParseDiagnostics file [] parsed = parsed := by
  simp [filterParseDiagnostics, suppressLexicalCascades]

/-- A nesting overflow has no lexical-cascade origin and is retained even
when ordinary lexical diagnostics occur at the same source location. -/
@[simp] theorem filterParseDiagnostics_single_nestingExceeded
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    (span : SourceSpan) (kind : NestingKind) (limit : Nat) :
    filterParseDiagnostics file lexical [{
      span
      kind := .nestingExceeded kind limit
    }] = [{
      span
      kind := .nestingExceeded kind limit
    }] := by
  simp [filterParseDiagnostics, suppressLexicalCascades,
    isLexicalCascadeCandidate]

/-- Diagnostic normalization can only remove parser diagnostics. -/
theorem mem_of_mem_filterParseDiagnostics
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    (parsed : List ParseDiagnostic) (diagnostic : ParseDiagnostic)
    (member : diagnostic ∈ filterParseDiagnostics file lexical parsed) :
    diagnostic ∈ parsed := by
  unfold filterParseDiagnostics suppressLexicalCascades at member
  exact (List.mem_filter.mp member).1

/-- Filtering lexical cascades preserves validity of every retained span. -/
theorem filterParseDiagnostics_spans_validFor
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    (parsed : List ParseDiagnostic)
    (valid : ∀ diagnostic ∈ parsed, diagnostic.span.ValidFor file) :
    ∀ diagnostic ∈ filterParseDiagnostics file lexical parsed,
      diagnostic.span.ValidFor file := by
  intro diagnostic member
  exact valid diagnostic
    (mem_of_mem_filterParseDiagnostics file lexical parsed diagnostic member)

end Solcore.Syntax.Parser
