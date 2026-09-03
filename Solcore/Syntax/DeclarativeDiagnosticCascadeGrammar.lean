import Solcore.Syntax.Trivia

/-! Independent lexical-cascade suppression for diagnostic spans known to be
ordinary failure or recovery events. Order and duplicate spans are retained;
protected constraint, identifier, and nesting events are outside this relation. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The cascade policy counts LF only; an invalid UTF-8 prefix has index zero. -/
def cascadeLineIndex (source : String) (offset : Nat) : Nat :=
  match Trivia.utf8Slice? source 0 offset with
  | some leading => leading.toList.count '\n'
  | none => 0

/-- An ordered, valid gap consists of Rust whitespace other than CR or LF. -/
def HorizontalWhitespaceGap (source : String)
    (lexical parsed : SourceSpan) : Prop :=
  lexical.endByte ≤ parsed.startByte ∧
    ∃ gap, Trivia.utf8Slice? source lexical.endByte parsed.startByte = some gap ∧
      (gap.toList.all fun character =>
        Trivia.isRustWhitespace character && character != '\n' && character != '\r') = true

/-- Exact source and range conditions making an ordinary parse event a cascade.
The inclusive lexical endpoint and the LF-only line rule are intentional. -/
def LexicalSpanSuppresses (source : String) (lexical parsed : SourceSpan) : Prop :=
  lexical.source = parsed.source ∧
    (cascadeLineIndex source lexical.startByte =
        cascadeLineIndex source parsed.startByte ∨
      (lexical.startByte < parsed.endByte ∧ parsed.startByte < lexical.endByte) ∨
      (lexical.startByte ≤ parsed.startByte ∧ parsed.startByte ≤ lexical.endByte) ∨
      HorizontalWhitespaceGap source lexical parsed)

/-- At least one retained lexical range suppresses this candidate event. -/
def LexicalCascadeSuppresses (source : String) (lexical : List SourceSpan)
    (parsed : SourceSpan) : Prop :=
  ∃ span ∈ lexical, LexicalSpanSuppresses source span parsed

/-- Source-ordered filtering of candidate event spans, preserving duplicates. -/
inductive LexicalCascadeFilters (source : String) (lexical : List SourceSpan) :
    List SourceSpan → List SourceSpan → Prop where
  | nil : LexicalCascadeFilters source lexical [] []
  | keep {span : SourceSpan} {raw kept : List SourceSpan}
      (retained : ¬ LexicalCascadeSuppresses source lexical span)
      (tail : LexicalCascadeFilters source lexical raw kept) :
      LexicalCascadeFilters source lexical (span :: raw) (span :: kept)
  | drop {span : SourceSpan} {raw kept : List SourceSpan}
      (suppressed : LexicalCascadeSuppresses source lexical span)
      (tail : LexicalCascadeFilters source lexical raw kept) :
      LexicalCascadeFilters source lexical (span :: raw) kept

end Solcore.Syntax.DeclarativeGrammar
