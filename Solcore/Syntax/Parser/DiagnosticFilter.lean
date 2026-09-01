import Solcore.Syntax.Parser.Trivia

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

/-- Normalize ordinary diagnostics without consulting display prose. -/
def filterParseDiagnostics (file : SourceFile)
    (lexical : List LexicalDiagnostic)
    (parsed : List ParseDiagnostic) : List ParseDiagnostic :=
  suppressLexicalCascades file.content lexical parsed

/-- With no lexical errors, diagnostic normalization retains every parser
diagnostic exactly. -/
@[simp] theorem filterParseDiagnostics_nil_lexical
    (file : SourceFile) (parsed : List ParseDiagnostic) :
    filterParseDiagnostics file [] parsed = parsed := by
  simp [filterParseDiagnostics, suppressLexicalCascades]

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
