import Solcore.Syntax.Lexer.Contract
import Solcore.Syntax.Parser.Diagnostic
import Solcore.Syntax.DeclarativeLexedValidationOutcomeProperties

/-! Executable provenance validation for already-tokenized syntax input. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace LexedValidation

/-- Validate token spans in source order, returning the first bad index. -/
def tokens (file : SourceFile) :
    Nat → Nat → List Token → Except ParserInvariantError Unit
  | _, _, [] => .ok ()
  | index, previousEnd, token :: rest =>
      if token.span.isValidFor file &&
          previousEnd ≤ token.span.startByte &&
          token.span.startByte < token.span.endByte then
        tokens file (index + 1) token.span.endByte rest
      else
        .error (.invalidTokenSpan index token.span)

/-- Validate comment spans in source order, returning the first bad index. -/
def comments (file : SourceFile) :
    Nat → Nat → List Comment → Except ParserInvariantError Unit
  | _, _, [] => .ok ()
  | index, previousEnd, comment :: rest =>
      if comment.span.isValidFor file &&
          previousEnd ≤ comment.span.startByte &&
          comment.span.startByte < comment.span.endByte then
        comments file (index + 1) comment.span.endByte rest
      else
        .error (.invalidCommentSpan index comment.span)

/-- Validate lexical-diagnostic ownership and UTF-8 boundaries in order. -/
def lexicalDiagnostics (file : SourceFile) :
    Nat → List LexicalDiagnostic → Except ParserInvariantError Unit
  | _, [] => .ok ()
  | index, diagnostic :: rest =>
      if diagnostic.span.isValidFor file then
        lexicalDiagnostics file (index + 1) rest
      else
        .error (.invalidLexicalDiagnosticSpan index diagnostic.span)

end LexedValidation

/-- Validate all provenance consumed or retained by `parseLexed`. -/
def validateLexed (file : SourceFile)
    (lexed : LexedFile) : Except ParserInvariantError Unit := do
  if lexed.source ≠ file.id then
    throw (.invalidLexedSource file.id lexed.source)
  LexedValidation.tokens file 0 0 lexed.tokens
  LexedValidation.comments file 0 0 lexed.comments
  LexedValidation.lexicalDiagnostics file 0 lexed.diagnostics

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.LexedValidationOutcomeSoundnessProperties`
-/

/-! Exact correspondence between executable and declarative lexed validation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

/-- Translate a parser-neutral validation failure to its public invariant error. -/
def lexedValidationInvariantError :
    LexedValidationFailure → ParserInvariantError
  | .sourceMismatch expected actual =>
      .invalidLexedSource expected actual
  | .invalidTokenSpan index span => .invalidTokenSpan index span
  | .invalidCommentSpan index span => .invalidCommentSpan index span
  | .invalidLexicalDiagnosticSpan index span =>
      .invalidLexicalDiagnosticSpan index span

/-- Executable result represented by one declarative whole-file outcome. -/
def lexedValidationResult :
    Option LexedValidationFailure → Except ParserInvariantError Unit
  | none => .ok ()
  | some failure => .error (lexedValidationInvariantError failure)

/-- Executable result represented by one declarative indexed-span scan. -/
def indexedSpanValidationResult
    (failure : Nat → SourceSpan → ParserInvariantError) :
    Option IndexedSpan → Except ParserInvariantError Unit
  | none => .ok ()
  | some invalid => .error (failure invalid.index invalid.span)

private theorem orderedSpanCondition_true_iff
    (file : SourceFile) (previousEnd : Nat) (span : SourceSpan) :
    (span.isValidFor file &&
      decide (previousEnd ≤ span.startByte) &&
      decide (span.startByte < span.endByte)) = true ↔
      OrderedSpanAccepted file previousEnd span := by
  simp only [OrderedSpanAccepted, Bool.and_eq_true,
    SourceSpan.isValidFor_eq_true_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨valid, ordered⟩, nonempty⟩
    exact ⟨valid, ordered, nonempty⟩
  · rintro ⟨valid, ordered, nonempty⟩
    exact ⟨⟨valid, ordered⟩, nonempty⟩

/-- A declarative token scan computes the identical executable result. -/
theorem tokens_eq_result_of_validationScans
    {file : SourceFile} {index previousEnd : Nat} {tokens : List Token}
    {result : Option IndexedSpan}
    (scan : TokenSpanValidationScans file index previousEnd tokens result) :
    LexedValidation.tokens file index previousEnd tokens =
      indexedSpanValidationResult ParserInvariantError.invalidTokenSpan
        result := by
  induction scan with
  | done => rfl
  | rejected invalid =>
      simp only [LexedValidation.tokens]
      rw [if_neg (fun accepted =>
        invalid ((orderedSpanCondition_true_iff _ _ _).mp accepted))]
      rfl
  | continues accepted tail inductionHypothesis =>
      simp only [LexedValidation.tokens]
      rw [if_pos ((orderedSpanCondition_true_iff _ _ _).mpr accepted)]
      exact inductionHypothesis

/-- A declarative comment scan computes the identical executable result. -/
theorem comments_eq_result_of_validationScans
    {file : SourceFile} {index previousEnd : Nat}
    {comments : List Comment} {result : Option IndexedSpan}
    (scan : CommentSpanValidationScans file index previousEnd comments result) :
    LexedValidation.comments file index previousEnd comments =
      indexedSpanValidationResult ParserInvariantError.invalidCommentSpan
        result := by
  induction scan with
  | done => rfl
  | rejected invalid =>
      simp only [LexedValidation.comments]
      rw [if_neg (fun accepted =>
        invalid ((orderedSpanCondition_true_iff _ _ _).mp accepted))]
      rfl
  | continues accepted tail inductionHypothesis =>
      simp only [LexedValidation.comments]
      rw [if_pos ((orderedSpanCondition_true_iff _ _ _).mpr accepted)]
      exact inductionHypothesis

/-- A declarative lexical-diagnostic scan computes the identical result. -/
theorem lexicalDiagnostics_eq_result_of_validationScans
    {file : SourceFile} {index : Nat}
    {diagnostics : List LexicalDiagnostic} {result : Option IndexedSpan}
    (scan : LexicalDiagnosticSpanValidationScans file index diagnostics
      result) :
    LexedValidation.lexicalDiagnostics file index diagnostics =
      indexedSpanValidationResult
        ParserInvariantError.invalidLexicalDiagnosticSpan result := by
  induction scan with
  | done => rfl
  | rejected invalid =>
      simp only [LexedValidation.lexicalDiagnostics]
      rw [if_neg (fun accepted =>
        invalid ((SourceSpan.isValidFor_eq_true_iff _ _).mp accepted))]
      rfl
  | continues accepted tail inductionHypothesis =>
      simp only [LexedValidation.lexicalDiagnostics]
      rw [if_pos ((SourceSpan.isValidFor_eq_true_iff _ _).mpr accepted)]
      exact inductionHypothesis

/-- The token validator always reflects one exact declarative scan. -/
theorem tokens_reflects_validationScans
    (file : SourceFile) (index previousEnd : Nat) (tokens : List Token) :
    ∃ result,
      TokenSpanValidationScans file index previousEnd tokens result ∧
        LexedValidation.tokens file index previousEnd tokens =
          indexedSpanValidationResult ParserInvariantError.invalidTokenSpan
            result := by
  rcases OrderedSpanValidationScans.exists_result file
      (fun token : Token => token.span) index previousEnd tokens with
    ⟨result, scan⟩
  exact ⟨result, scan, tokens_eq_result_of_validationScans scan⟩

/-- The comment validator always reflects one exact declarative scan. -/
theorem comments_reflects_validationScans
    (file : SourceFile) (index previousEnd : Nat)
    (comments : List Comment) :
    ∃ result,
      CommentSpanValidationScans file index previousEnd comments result ∧
        LexedValidation.comments file index previousEnd comments =
          indexedSpanValidationResult ParserInvariantError.invalidCommentSpan
            result := by
  rcases OrderedSpanValidationScans.exists_result file
      (fun comment : Comment => comment.span) index previousEnd comments with
    ⟨result, scan⟩
  exact ⟨result, scan, comments_eq_result_of_validationScans scan⟩

/-- The lexical-diagnostic validator reflects one exact declarative scan. -/
theorem lexicalDiagnostics_reflects_validationScans
    (file : SourceFile) (index : Nat)
    (diagnostics : List LexicalDiagnostic) :
    ∃ result,
      LexicalDiagnosticSpanValidationScans file index diagnostics result ∧
        LexedValidation.lexicalDiagnostics file index diagnostics =
          indexedSpanValidationResult
            ParserInvariantError.invalidLexicalDiagnosticSpan result := by
  rcases SpanValidationScans.exists_result file
      (fun diagnostic : LexicalDiagnostic => diagnostic.span)
      index diagnostics with ⟨result, scan⟩
  exact ⟨result, scan,
    lexicalDiagnostics_eq_result_of_validationScans scan⟩

/-- A whole-file declarative outcome computes the same preflight result. -/
theorem validateLexed_eq_result_of_outcome
    {file : SourceFile} {lexed : LexedFile}
    {result : Option LexedValidationFailure}
    (outcome : LexedFileValidationOutcome file lexed result) :
    validateLexed file lexed = lexedValidationResult result := by
  cases outcome with
  | sourceRejected mismatch =>
      unfold validateLexed
      rw [if_pos mismatch]
      rfl
  | tokenRejected sourceAccepted tokens =>
      unfold validateLexed
      rw [if_neg (fun mismatch => mismatch sourceAccepted)]
      rw [tokens_eq_result_of_validationScans tokens]
      rfl
  | commentRejected sourceAccepted tokens comments =>
      unfold validateLexed
      rw [if_neg (fun mismatch => mismatch sourceAccepted)]
      rw [tokens_eq_result_of_validationScans tokens]
      rw [comments_eq_result_of_validationScans comments]
      rfl
  | diagnosticRejected sourceAccepted tokens comments diagnostics =>
      unfold validateLexed
      rw [if_neg (fun mismatch => mismatch sourceAccepted)]
      rw [tokens_eq_result_of_validationScans tokens]
      rw [comments_eq_result_of_validationScans comments]
      rw [lexicalDiagnostics_eq_result_of_validationScans diagnostics]
      rfl
  | accepted sourceAccepted tokens comments diagnostics =>
      unfold validateLexed
      rw [if_neg (fun mismatch => mismatch sourceAccepted)]
      rw [tokens_eq_result_of_validationScans tokens]
      rw [comments_eq_result_of_validationScans comments]
      rw [lexicalDiagnostics_eq_result_of_validationScans diagnostics]
      rfl

/-- Executable preflight always reflects one exact declarative outcome. -/
theorem validateLexed_reflects_outcome
    (file : SourceFile) (lexed : LexedFile) :
    ∃ result,
      LexedFileValidationOutcome file lexed result ∧
        validateLexed file lexed = lexedValidationResult result := by
  rcases LexedFileValidationOutcome.exists_result file lexed with
    ⟨result, outcome⟩
  exact ⟨result, outcome, validateLexed_eq_result_of_outcome outcome⟩

/-- Executable preflight succeeds exactly on declarative acceptance. -/
theorem validateLexed_ok_iff_validationAccepts
    (file : SourceFile) (lexed : LexedFile) :
    validateLexed file lexed = .ok () ↔
      LexedFileValidationAccepts file lexed := by
  constructor
  · intro validated
    rcases validateLexed_reflects_outcome file lexed with
      ⟨result, outcome, equation⟩
    rw [validated] at equation
    cases result with
    | none => exact outcome
    | some failure => simp [lexedValidationResult] at equation
  · intro accepts
    simpa [lexedValidationResult] using
      validateLexed_eq_result_of_outcome accepts

/-- Executable preflight errors exactly with the mapped first rejection. -/
theorem validateLexed_error_iff_validationRejects
    (file : SourceFile) (lexed : LexedFile)
    (error : ParserInvariantError) :
    validateLexed file lexed = .error error ↔
      ∃ failure,
        LexedFileValidationRejects file lexed failure ∧
          error = lexedValidationInvariantError failure := by
  constructor
  · intro validated
    rcases validateLexed_reflects_outcome file lexed with
      ⟨result, outcome, equation⟩
    rw [validated] at equation
    cases result with
    | none => simp [lexedValidationResult] at equation
    | some failure =>
        exact ⟨failure, outcome,
          Except.error.inj equation⟩
  · rintro ⟨failure, rejects, rfl⟩
    simpa [lexedValidationResult] using
      validateLexed_eq_result_of_outcome rejects

end Solcore.Syntax.Parser
