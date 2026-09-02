import Solcore.Syntax.Lexer.Contract
import Solcore.Syntax.Parser.LexedValidation
import Solcore.Syntax.Parser.Nesting
import Solcore.Syntax.Parser.State

set_option autoImplicit false

namespace Solcore.Syntax.Parser.State

/-- Canonical root-state construction preserves validated lexer provenance. -/
theorem initial_validFor {file : SourceFile} {lexed : LexedFile}
    (valid : lexed.ValidFor file) :
    (initial file lexed).ValidFor := by
  exact {
    tokens := by simpa [initial] using valid.tokens
    cursor_le_endIndex := Nat.zero_le _
    endIndex_le_size := by simp [initial]
    endByte_le_source := Nat.le_refl _
    endByte_boundary := isUtf8Boundary_end file.content
    diagnosticsRev := by simp [initial]
  }

end Solcore.Syntax.Parser.State

namespace Solcore.Syntax.Parser

private theorem validateTokens_sound (file : SourceFile)
    (index previousEnd : Nat) (tokens : List Token)
    (result : LexedValidation.tokens file index previousEnd tokens = .ok ()) :
    SpanSequence.ValidFor file (fun token : Token => token.span)
      previousEnd tokens := by
  induction tokens generalizing index previousEnd with
  | nil => trivial
  | cons token rest ih =>
      simp only [LexedValidation.tokens] at result
      split at result
      · rename_i accepted
        simp only [Bool.and_eq_true,
          SourceSpan.isValidFor_eq_true_iff] at accepted
        rcases accepted with ⟨⟨spanValid, afterPrevious⟩, nonempty⟩
        exact ⟨spanValid, of_decide_eq_true afterPrevious,
          of_decide_eq_true nonempty,
          ih (index := index + 1) (previousEnd := token.span.endByte)
            result⟩
      · contradiction

private theorem validateComments_sound (file : SourceFile)
    (index previousEnd : Nat) (comments : List Comment)
    (result : LexedValidation.comments file index previousEnd comments = .ok ()) :
    SpanSequence.ValidFor file (fun comment : Comment => comment.span)
      previousEnd comments := by
  induction comments generalizing index previousEnd with
  | nil => trivial
  | cons comment rest ih =>
      simp only [LexedValidation.comments] at result
      split at result
      · rename_i accepted
        simp only [Bool.and_eq_true,
          SourceSpan.isValidFor_eq_true_iff] at accepted
        rcases accepted with ⟨⟨spanValid, afterPrevious⟩, nonempty⟩
        exact ⟨spanValid, of_decide_eq_true afterPrevious,
          of_decide_eq_true nonempty,
          ih (index := index + 1) (previousEnd := comment.span.endByte)
            result⟩
      · contradiction

private theorem validateLexicalDiagnostics_sound (file : SourceFile)
    (index : Nat) (diagnostics : List LexicalDiagnostic)
    (result : LexedValidation.lexicalDiagnostics file index diagnostics = .ok ()) :
    ∀ diagnostic ∈ diagnostics, diagnostic.span.ValidFor file := by
  induction diagnostics generalizing index with
  | nil => simp
  | cons head tail ih =>
      simp only [LexedValidation.lexicalDiagnostics] at result
      split at result
      · rename_i accepted
        intro diagnostic member
        rcases List.mem_cons.mp member with rfl | member
        · exact (SourceSpan.isValidFor_eq_true_iff diagnostic.span file).mp
            accepted
        · exact ih (index := index + 1) result diagnostic member
      · contradiction

private theorem validateTokens_complete (file : SourceFile)
    (index previousEnd : Nat) (tokens : List Token)
    (valid : SpanSequence.ValidFor file
      (fun token : Token => token.span) previousEnd tokens) :
    LexedValidation.tokens file index previousEnd tokens = .ok () := by
  induction tokens generalizing index previousEnd with
  | nil => rfl
  | cons token rest ih =>
      simp only [SpanSequence.ValidFor] at valid
      rcases valid with
        ⟨spanValid, afterPrevious, nonempty, restValid⟩
      simp only [LexedValidation.tokens]
      have accepted :
          (token.span.isValidFor file &&
            decide (previousEnd ≤ token.span.startByte) &&
            decide (token.span.startByte < token.span.endByte)) = true := by
        simp only [Bool.and_eq_true,
          SourceSpan.isValidFor_eq_true_iff]
        exact ⟨⟨spanValid, decide_eq_true afterPrevious⟩,
          decide_eq_true nonempty⟩
      rw [if_pos accepted]
      exact ih (index := index + 1)
        (previousEnd := token.span.endByte) restValid

private theorem validateComments_complete (file : SourceFile)
    (index previousEnd : Nat) (comments : List Comment)
    (valid : SpanSequence.ValidFor file
      (fun comment : Comment => comment.span) previousEnd comments) :
    LexedValidation.comments file index previousEnd comments = .ok () := by
  induction comments generalizing index previousEnd with
  | nil => rfl
  | cons comment rest ih =>
      simp only [SpanSequence.ValidFor] at valid
      rcases valid with
        ⟨spanValid, afterPrevious, nonempty, restValid⟩
      simp only [LexedValidation.comments]
      have accepted :
          (comment.span.isValidFor file &&
            decide (previousEnd ≤ comment.span.startByte) &&
            decide (comment.span.startByte < comment.span.endByte)) = true := by
        simp only [Bool.and_eq_true,
          SourceSpan.isValidFor_eq_true_iff]
        exact ⟨⟨spanValid, decide_eq_true afterPrevious⟩,
          decide_eq_true nonempty⟩
      rw [if_pos accepted]
      exact ih (index := index + 1)
        (previousEnd := comment.span.endByte) restValid

private theorem validateLexicalDiagnostics_complete (file : SourceFile)
    (index : Nat) (diagnostics : List LexicalDiagnostic)
    (valid : ∀ diagnostic ∈ diagnostics,
      diagnostic.span.ValidFor file) :
    LexedValidation.lexicalDiagnostics file index diagnostics = .ok () := by
  induction diagnostics generalizing index with
  | nil => rfl
  | cons head tail ih =>
      simp only [LexedValidation.lexicalDiagnostics]
      have headValid : head.span.isValidFor file = true :=
        (SourceSpan.isValidFor_eq_true_iff head.span file).mpr
          (valid head (by simp))
      rw [if_pos headValid]
      apply ih (index := index + 1)
      intro diagnostic member
      exact valid diagnostic (by simp [member])

/-- Successful parser preflight exposes its complete declarative contract. -/
theorem validateLexed_ok_validFor (file : SourceFile) (lexed : LexedFile)
    (result : validateLexed file lexed = .ok ()) :
    lexed.ValidFor file := by
  unfold validateLexed at result
  split at result
  · contradiction
  · rename_i sourceAccepted
    cases tokensResult : LexedValidation.tokens file 0 0 lexed.tokens with
    | error error =>
        rw [tokensResult] at result
        contradiction
    | ok witness =>
        cases witness
        cases commentsResult : LexedValidation.comments file 0 0 lexed.comments with
        | error error =>
            rw [tokensResult, commentsResult] at result
            contradiction
        | ok witness =>
            cases witness
            cases diagnosticsResult :
                LexedValidation.lexicalDiagnostics file 0 lexed.diagnostics with
            | error error =>
                rw [tokensResult, commentsResult, diagnosticsResult] at result
                contradiction
            | ok witness =>
                cases witness
                refine {
                  source_eq := ?_
                  tokens := validateTokens_sound file 0 0 lexed.tokens ?_
                  comments := validateComments_sound file 0 0 lexed.comments ?_
                  diagnostics := validateLexicalDiagnostics_sound file 0
                    lexed.diagnostics ?_
                }
                · exact Decidable.of_not_not sourceAccepted
                · exact tokensResult
                · exact commentsResult
                · exact diagnosticsResult

/-- Every declaratively valid lexer result passes parser preflight. -/
theorem validateLexed_validFor_ok (file : SourceFile) (lexed : LexedFile)
    (valid : lexed.ValidFor file) :
    validateLexed file lexed = .ok () := by
  unfold validateLexed
  have sourceAccepted : ¬ lexed.source ≠ file.id := by
    intro rejected
    exact rejected valid.source_eq
  rw [if_neg sourceAccepted]
  rw [validateTokens_complete file 0 0 lexed.tokens valid.tokens]
  rw [validateComments_complete file 0 0 lexed.comments valid.comments]
  exact validateLexicalDiagnostics_complete file 0
    lexed.diagnostics valid.diagnostics

/-- Parser preflight decides the complete declarative lexer contract. -/
theorem validateLexed_ok_iff_validFor (file : SourceFile)
    (lexed : LexedFile) :
    validateLexed file lexed = .ok () ↔ lexed.ValidFor file :=
  ⟨validateLexed_ok_validFor file lexed,
    validateLexed_validFor_ok file lexed⟩

end Solcore.Syntax.Parser
