import Solcore.Syntax.Lexer.Contract

/-!
Parser-independent exact outcomes for validating an already-tokenized source.
The relations stop at the first invalid span and preserve the public preflight
priority: source identity, tokens, comments, then lexical diagnostics.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- An exact source-order location reported by a validation scan. -/
structure IndexedSpan where
  index : Nat
  span : SourceSpan
  deriving Repr, BEq, DecidableEq

/-- Parser-neutral failures of already-tokenized source validation. -/
inductive LexedValidationFailure where
  | sourceMismatch (expected actual : SourceId)
  | invalidTokenSpan (index : Nat) (span : SourceSpan)
  | invalidCommentSpan (index : Nat) (span : SourceSpan)
  | invalidLexicalDiagnosticSpan (index : Nat) (span : SourceSpan)
  deriving Repr, BEq, DecidableEq

/-- Exact acceptance condition for one ordered, nonempty source span. -/
def OrderedSpanAccepted (file : SourceFile) (previousEnd : Nat)
    (span : SourceSpan) : Prop :=
  span.ValidFor file ∧
    previousEnd ≤ span.startByte ∧
    span.startByte < span.endByte

/-- Scan source-ordered spans, returning the first invalid indexed span. -/
inductive OrderedSpanValidationScans {α : Type} (file : SourceFile)
    (spanOf : α → SourceSpan) :
    Nat → Nat → List α → Option IndexedSpan → Prop where
  | done {index previousEnd : Nat} :
      OrderedSpanValidationScans file spanOf index previousEnd [] none
  | rejected {index previousEnd : Nat} {item : α} {rest : List α}
      (invalid : ¬ OrderedSpanAccepted file previousEnd (spanOf item)) :
      OrderedSpanValidationScans file spanOf index previousEnd (item :: rest)
        (some { index := index, span := spanOf item })
  | continues {index previousEnd : Nat} {item : α} {rest : List α}
      {result : Option IndexedSpan}
      (accepted : OrderedSpanAccepted file previousEnd (spanOf item))
      (tail : OrderedSpanValidationScans file spanOf (index + 1)
        (spanOf item).endByte rest result) :
      OrderedSpanValidationScans file spanOf index previousEnd (item :: rest)
        result

/-- Scan pointwise source-owned spans, returning the first invalid one. -/
inductive SpanValidationScans {α : Type} (file : SourceFile)
    (spanOf : α → SourceSpan) :
    Nat → List α → Option IndexedSpan → Prop where
  | done {index : Nat} :
      SpanValidationScans file spanOf index [] none
  | rejected {index : Nat} {item : α} {rest : List α}
      (invalid : ¬ (spanOf item).ValidFor file) :
      SpanValidationScans file spanOf index (item :: rest)
        (some { index := index, span := spanOf item })
  | continues {index : Nat} {item : α} {rest : List α}
      {result : Option IndexedSpan}
      (accepted : (spanOf item).ValidFor file)
      (tail : SpanValidationScans file spanOf (index + 1) rest result) :
      SpanValidationScans file spanOf index (item :: rest) result

/-- Exact token-span scan used by whole-file validation. -/
abbrev TokenSpanValidationScans (file : SourceFile) :=
  OrderedSpanValidationScans file (fun token : Token => token.span)

/-- Exact comment-span scan used by whole-file validation. -/
abbrev CommentSpanValidationScans (file : SourceFile) :=
  OrderedSpanValidationScans file (fun comment : Comment => comment.span)

/-- Exact lexical-diagnostic span scan used by whole-file validation. -/
abbrev LexicalDiagnosticSpanValidationScans (file : SourceFile) :=
  SpanValidationScans file
    (fun diagnostic : LexicalDiagnostic => diagnostic.span)

/-- Exact priority-ordered outcome of validating one tokenized source file. -/
inductive LexedFileValidationOutcome (file : SourceFile)
    (lexed : LexedFile) : Option LexedValidationFailure → Prop where
  | sourceRejected (mismatch : lexed.source ≠ file.id) :
      LexedFileValidationOutcome file lexed
        (some (.sourceMismatch file.id lexed.source))
  | tokenRejected {invalid : IndexedSpan}
      (sourceAccepted : lexed.source = file.id)
      (tokens : TokenSpanValidationScans file 0 0 lexed.tokens
        (some invalid)) :
      LexedFileValidationOutcome file lexed
        (some (.invalidTokenSpan invalid.index invalid.span))
  | commentRejected {invalid : IndexedSpan}
      (sourceAccepted : lexed.source = file.id)
      (tokens : TokenSpanValidationScans file 0 0 lexed.tokens none)
      (comments : CommentSpanValidationScans file 0 0 lexed.comments
        (some invalid)) :
      LexedFileValidationOutcome file lexed
        (some (.invalidCommentSpan invalid.index invalid.span))
  | diagnosticRejected {invalid : IndexedSpan}
      (sourceAccepted : lexed.source = file.id)
      (tokens : TokenSpanValidationScans file 0 0 lexed.tokens none)
      (comments : CommentSpanValidationScans file 0 0 lexed.comments none)
      (diagnostics : LexicalDiagnosticSpanValidationScans file 0
        lexed.diagnostics (some invalid)) :
      LexedFileValidationOutcome file lexed
        (some (.invalidLexicalDiagnosticSpan invalid.index invalid.span))
  | accepted
      (sourceAccepted : lexed.source = file.id)
      (tokens : TokenSpanValidationScans file 0 0 lexed.tokens none)
      (comments : CommentSpanValidationScans file 0 0 lexed.comments none)
      (diagnostics : LexicalDiagnosticSpanValidationScans file 0
        lexed.diagnostics none) :
      LexedFileValidationOutcome file lexed none

/-- Whole-file validation accepts every retained lexical artifact. -/
def LexedFileValidationAccepts (file : SourceFile)
    (lexed : LexedFile) : Prop :=
  LexedFileValidationOutcome file lexed none

/-- Whole-file validation rejects with one exact first failure. -/
def LexedFileValidationRejects (file : SourceFile) (lexed : LexedFile)
    (failure : LexedValidationFailure) : Prop :=
  LexedFileValidationOutcome file lexed (some failure)

end Solcore.Syntax.DeclarativeGrammar
