import Solcore.Syntax.Lexer.Core
import Solcore.Syntax.Lexer.ScanProperties

/-! Source-provenance laws for the total canonical lexer. -/

set_option autoImplicit false

namespace Solcore.Syntax.Lexer

/-- Every successful executor result remains owned by the input source. -/
theorem lexLoop_ok_source
    (file : SourceFile) (fuel : Nat) (state : State) (lexed : LexedFile)
    (result : lexLoop file fuel state = .ok lexed) :
    lexed.source = file.id := by
  induction fuel generalizing state with
  | zero =>
      simp [lexLoop] at result
  | succ fuel inductionHypothesis =>
      cases state with
      | mk cursor remaining tokens comments diagnostics =>
          cases remaining with
          | nil =>
              simp [lexLoop, State.finish] at result
              cases result
              rfl
          | cons character rest =>
              simp only [lexLoop] at result
              exact inductionHypothesis _ result

/-- Every exceptional executor diagnostic remains owned by the input source. -/
theorem lexLoop_error_source
    (file : SourceFile) (fuel : Nat) (state : State)
    (diagnostic : LexicalDiagnostic)
    (result : lexLoop file fuel state = .error diagnostic) :
    diagnostic.span.source = file.id := by
  induction fuel generalizing state with
  | zero =>
      simp only [lexLoop] at result
      cases result
      rfl
  | succ fuel inductionHypothesis =>
      cases state with
      | mk cursor remaining tokens comments diagnostics =>
          cases remaining with
          | nil => simp [lexLoop] at result
          | cons character rest =>
              simp only [lexLoop] at result
              exact inductionHypothesis _ result

/--
Every successful executor result retains source ownership and valid UTF-8
spans for all exposed lexical carriers.
-/
theorem lexLoop_ok_carrier_spans
    (file : SourceFile) (fuel : Nat) (state : State) (lexed : LexedFile)
    (stateValid : state.ValidFor file)
    (result : lexLoop file fuel state = .ok lexed) :
    lexed.source = file.id ∧
      (∀ token ∈ lexed.tokens, token.span.ValidFor file) ∧
      (∀ comment ∈ lexed.comments, comment.span.ValidFor file) ∧
      (∀ diagnostic ∈ lexed.diagnostics,
        diagnostic.span.ValidFor file) := by
  induction fuel generalizing state with
  | zero => simp [lexLoop] at result
  | succ fuel inductionHypothesis =>
      cases state with
      | mk cursor remaining tokens comments diagnostics =>
          cases remaining with
          | nil =>
              simp only [lexLoop] at result
              cases result
              exact stateValid.finish
          | cons character rest =>
              simp only [lexLoop] at result
              exact inductionHypothesis
                (step file ⟨cursor, character :: rest, tokens, comments,
                  diagnostics⟩)
                (step_validFor file _ stateValid) result

/-- A successful public lex retains the exact input source identity. -/
theorem lex_ok_source
    (file : SourceFile) (lexed : LexedFile)
    (result : lex file = .ok lexed) :
    lexed.source = file.id :=
  lexLoop_ok_source file (fuelBound file) (State.initial file) lexed result

/-- A public lexer invariant diagnostic cannot name a different source. -/
theorem lex_error_source
    (file : SourceFile) (diagnostic : LexicalDiagnostic)
    (result : lex file = .error diagnostic) :
    diagnostic.span.source = file.id :=
  lexLoop_error_source file (fuelBound file) (State.initial file)
    diagnostic result

/-- A successful public lex exposes only source-owned, valid carrier spans. -/
theorem lex_ok_carrier_spans
    (file : SourceFile) (lexed : LexedFile)
    (result : lex file = .ok lexed) :
    lexed.source = file.id ∧
      (∀ token ∈ lexed.tokens, token.span.ValidFor file) ∧
      (∀ comment ∈ lexed.comments, comment.span.ValidFor file) ∧
      (∀ diagnostic ∈ lexed.diagnostics,
        diagnostic.span.ValidFor file) :=
  lexLoop_ok_carrier_spans file (fuelBound file) (State.initial file) lexed
    (State.initial_validFor file) result

end Solcore.Syntax.Lexer
