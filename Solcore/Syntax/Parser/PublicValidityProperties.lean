import Solcore.Syntax.Parser.FileItemsProperties
import Solcore.Syntax.Parser.Properties

/-! Canonical parsed-file validity at the public parser boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Canonical recursive validity for one complete parsed file. -/
abbrev CanonicalParsedFileValid : SourceFile → ParsedFile → Prop :=
  ParsedFile.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor

/-- A successful preflighted parse returns a canonically valid parsed file.

The item-parser laws remain explicit until the outer contract declaration and
derive-aware top-level dispatcher are closed.
-/
theorem parseLexed_ok_parsed_validFor
    (itemValid : FileInternals.parseItemsItem.ValidFor
      FileInternals.RecoveredTopItemValid)
    (itemWindow : Parser.PreservesTokenWindow
      FileInternals.parseItemsItem)
    (file : SourceFile) (lexed : LexedFile) (output : ParseOutput)
    (lexedValid : lexed.ValidFor file)
    (result : parseLexed file lexed = .ok output) :
    CanonicalParsedFileValid file output.parsed := by
  unfold parseLexed at result
  rw [validateLexed_validFor_ok file lexed lexedValid] at result
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
        | .invariant error => Except.error error) = .ok output at result
  cases nesting : checkNesting lexed.tokens with
  | some diagnostic =>
      simp only [nesting] at result
      cases result
      exact ⟨rfl, SourceSpan.fullFile_validFor file, by simp,
        fun _ member => lexedValid.comment_span member⟩
  | none =>
      simp only [nesting] at result
      have initialValid := State.initial_validFor lexedValid
      have parsedReply := FileInternals.sourceFile_reply_validFor itemValid
        itemWindow initialValid
          (fun _ member => lexedValid.comment_span member)
      cases grammar : sourceFile lexed.comments (State.initial file lexed) with
      | ok parsed finalState =>
          rw [grammar] at parsedReply
          simp only [grammar] at result
          cases result
          exact parsedReply.1
      | reject failure rejected =>
          simp only [grammar] at result
          contradiction
      | invariant error =>
          simp only [grammar] at result
          contradiction

/-- Every successful public source parse returns a canonically valid file. -/
theorem parse_ok_parsed_validFor
    (itemValid : FileInternals.parseItemsItem.ValidFor
      FileInternals.RecoveredTopItemValid)
    (itemWindow : Parser.PreservesTokenWindow
      FileInternals.parseItemsItem)
    (file : SourceFile) (output : ParseOutput)
    (result : parse file = .ok output) :
    CanonicalParsedFileValid file output.parsed := by
  unfold parse at result
  cases lexing : Lexer.lex file with
  | error diagnostic => simp [lexing] at result
  | ok lexed =>
      have lexedValid := Lexer.lex_ok_validFor file lexed lexing
      cases parsing : parseLexed file lexed with
      | error error => simp [lexing, parsing] at result
      | ok parsedOutput =>
          have outputEq : parsedOutput = output := by
            simpa [lexing, parsing] using result
          subst output
          exact parseLexed_ok_parsed_validFor itemValid itemWindow file lexed
            parsedOutput lexedValid parsing

end Solcore.Syntax.Parser
