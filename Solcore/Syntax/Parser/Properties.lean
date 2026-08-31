import Solcore.Syntax.Lexer.Properties
import Solcore.Syntax.Parser

/-! Source-provenance laws for the total canonical parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A successful complete-file grammar result has canonical file provenance. -/
theorem sourceFile_ok_provenance
    (comments : List Comment) (state next : State) (parsed : ParsedFile)
    (result : sourceFile comments state = .ok parsed next) :
    parsed.source = state.file.id ∧
      parsed.span = SourceSpan.fullFile state.file := by
  simp only [sourceFile] at result
  split at result
  · rcases result with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  · contradiction
  · contradiction

/-- A successful complete-file grammar result retains every lexical comment. -/
theorem sourceFile_ok_comments
    (comments : List Comment) (state next : State) (parsed : ParsedFile)
    (result : sourceFile comments state = .ok parsed next) :
    parsed.comments = comments := by
  simp only [sourceFile] at result
  split at result
  · rcases result with ⟨rfl, rfl⟩
    rfl
  · contradiction
  · contradiction

/-- `parseLexed` cannot change the source owner or complete-file span. -/
theorem parseLexed_ok_provenance
    (file : SourceFile) (lexed : LexedFile) (output : ParseOutput)
    (result : parseLexed file lexed = .ok output) :
    output.parsed.source = file.id ∧
      output.parsed.span = SourceSpan.fullFile file := by
  unfold parseLexed at result
  cases validation : validateLexed file lexed with
  | error error =>
      rw [validation] at result
      change Except.error error = Except.ok output at result
      contradiction
  | ok validationWitness =>
      rw [validation] at result
      change (match checkNesting lexed.tokens with
        | some diagnostic => Except.ok ({
            parsed := {
              source := file.id
              span := SourceSpan.fullFile file
              items := []
              comments := lexed.comments
            }
            tokens := lexed.tokens
            lexicalDiagnostics := lexed.diagnostics
            parseDiagnostics :=
              filterParseDiagnostics file lexed.diagnostics [diagnostic]
          } : ParseOutput)
        | none =>
            match sourceFile lexed.comments (State.initial file lexed) with
            | .ok parsed finalState => Except.ok ({
                parsed
                tokens := lexed.tokens
                lexicalDiagnostics := lexed.diagnostics
                parseDiagnostics := filterParseDiagnostics file
                  lexed.diagnostics finalState.diagnostics
              } : ParseOutput)
            | .reject failure _ =>
                Except.error (ParserInvariantError.noProgress
                  .topLevel failure.span)
            | .invariant error => Except.error error) =
              Except.ok output at result
      cases nesting : checkNesting lexed.tokens with
      | some diagnostic =>
          simp only [nesting] at result
          cases result
          exact ⟨rfl, rfl⟩
      | none =>
          simp only [nesting] at result
          cases grammar : sourceFile lexed.comments
              (State.initial file lexed) with
          | ok parsed finalState =>
              simp only [grammar] at result
              cases result
              exact sourceFile_ok_provenance lexed.comments
                (State.initial file lexed) finalState parsed grammar
          | reject failure failedState =>
              simp only [grammar] at result
              contradiction
          | invariant error =>
              simp only [grammar] at result
              contradiction

/--
`parseLexed` retains the validated lexer output used by downstream provenance
checks. The parser neither retokenizes nor rewrites lexical diagnostics or the
complete source-order comment stream.
-/
theorem parseLexed_ok_retention
    (file : SourceFile) (lexed : LexedFile) (output : ParseOutput)
    (result : parseLexed file lexed = .ok output) :
    output.tokens = lexed.tokens ∧
      output.lexicalDiagnostics = lexed.diagnostics ∧
      output.parsed.comments = lexed.comments := by
  unfold parseLexed at result
  cases validation : validateLexed file lexed with
  | error error =>
      rw [validation] at result
      change Except.error error = Except.ok output at result
      contradiction
  | ok validationWitness =>
      rw [validation] at result
      change (match checkNesting lexed.tokens with
        | some diagnostic => Except.ok ({
            parsed := {
              source := file.id
              span := SourceSpan.fullFile file
              items := []
              comments := lexed.comments
            }
            tokens := lexed.tokens
            lexicalDiagnostics := lexed.diagnostics
            parseDiagnostics :=
              filterParseDiagnostics file lexed.diagnostics [diagnostic]
          } : ParseOutput)
        | none =>
            match sourceFile lexed.comments (State.initial file lexed) with
            | .ok parsed finalState => Except.ok ({
                parsed
                tokens := lexed.tokens
                lexicalDiagnostics := lexed.diagnostics
                parseDiagnostics := filterParseDiagnostics file
                  lexed.diagnostics finalState.diagnostics
              } : ParseOutput)
            | .reject failure _ =>
                Except.error (ParserInvariantError.noProgress
                  .topLevel failure.span)
            | .invariant error => Except.error error) =
              Except.ok output at result
      cases nesting : checkNesting lexed.tokens with
      | some diagnostic =>
          simp only [nesting] at result
          cases result
          exact ⟨rfl, rfl, rfl⟩
      | none =>
          simp only [nesting] at result
          cases grammar : sourceFile lexed.comments
              (State.initial file lexed) with
          | ok parsed finalState =>
              simp only [grammar] at result
              cases result
              exact ⟨rfl, rfl, sourceFile_ok_comments lexed.comments
                (State.initial file lexed) finalState parsed grammar⟩
          | reject failure failedState =>
              simp only [grammar] at result
              contradiction
          | invariant error =>
              simp only [grammar] at result
              contradiction

/-- Successful public parsing retains exact input source and full-file span. -/
theorem parse_ok_provenance
    (file : SourceFile) (output : ParseOutput)
    (result : parse file = .ok output) :
    output.parsed.source = file.id ∧
      output.parsed.span = SourceSpan.fullFile file := by
  unfold parse at result
  cases lexing : Lexer.lex file with
  | error diagnostic => simp [lexing] at result
  | ok lexed =>
      cases parsing : parseLexed file lexed with
      | error error => simp [lexing, parsing] at result
      | ok parsedOutput =>
          have definition : parsedOutput = output := by
            simpa [lexing, parsing] using result
          subst output
          exact parseLexed_ok_provenance file lexed parsedOutput parsing

/--
Every successful public parse exposes a successful lexer/parser composition and
the exact retained lexical carriers that produced its output.
-/
theorem parse_ok_lexed_provenance
    (file : SourceFile) (output : ParseOutput)
    (result : parse file = .ok output) :
    ∃ lexed,
      Lexer.lex file = .ok lexed ∧
      parseLexed file lexed = .ok output ∧
      output.tokens = lexed.tokens ∧
      output.lexicalDiagnostics = lexed.diagnostics ∧
      output.parsed.comments = lexed.comments := by
  unfold parse at result
  cases lexing : Lexer.lex file with
  | error diagnostic => simp [lexing] at result
  | ok lexed =>
      cases parsing : parseLexed file lexed with
      | error error => simp [lexing, parsing] at result
      | ok parsedOutput =>
          have definition : parsedOutput = output := by
            simpa [lexing, parsing] using result
          subst output
          exact ⟨lexed, rfl, parsing,
            parseLexed_ok_retention file lexed parsedOutput parsing⟩

theorem parse_ok_source
    (file : SourceFile) (output : ParseOutput)
    (result : parse file = .ok output) :
    output.parsed.source = file.id :=
  (parse_ok_provenance file output result).1

theorem parse_ok_span
    (file : SourceFile) (output : ParseOutput)
    (result : parse file = .ok output) :
    output.parsed.span = SourceSpan.fullFile file :=
  (parse_ok_provenance file output result).2

end Solcore.Syntax.Parser
