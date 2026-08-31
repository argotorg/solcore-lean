import Solcore.Syntax.Lexer.Core

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

end Solcore.Syntax.Lexer
