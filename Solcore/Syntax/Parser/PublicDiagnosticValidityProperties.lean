import Solcore.Syntax.Parser.FileCanonicalProperties

/-! Parse-diagnostic provenance at the public parser boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every parse diagnostic returned after preflight points into the input file. -/
theorem parseLexed_ok_parseDiagnostics_validFor
    (contract : FileInternals.ContractDeclInputs)
    (file : SourceFile) (lexed : LexedFile) (output : ParseOutput)
    (result : parseLexed file lexed = .ok output) :
    ∀ diagnostic ∈ output.parseDiagnostics,
      diagnostic.span.ValidFor file := by
  have lexedValid := parseLexed_ok_input_validFor file lexed output result
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
  | some nestingDiagnostic =>
      have nestingValid := checkNesting_lexed_some_span_validFor file lexed
        lexedValid nesting
      simp only [nesting] at result
      cases result
      exact filterParseDiagnostics_spans_validFor file lexed.diagnostics
        [nestingDiagnostic] (by
          intro diagnostic member
          simp only [List.mem_singleton] at member
          cases member
          exact nestingValid)
  | none =>
      simp only [nesting] at result
      have initialValid := State.initial_validFor lexedValid
      have grammarReply := FileInternals.sourceFile_canonical_reply_validFor
        contract initialValid (fun _ member => lexedValid.comment_span member)
      cases grammar : sourceFile lexed.comments (State.initial file lexed) with
      | ok parsed finalState =>
          rw [grammar] at grammarReply
          simp only [grammar] at result
          cases result
          apply filterParseDiagnostics_spans_validFor
          intro diagnostic member
          have validInFinal :=
            grammarReply.2.1.diagnostics_span_validFor member
          simpa [State.initial, grammarReply.2.2] using validInFinal
      | reject failure rejected =>
          simp only [grammar] at result
          contradiction
      | invariant error =>
          simp only [grammar] at result
          contradiction

/-- Every parse diagnostic returned by public source parsing is source-valid. -/
theorem parse_ok_parseDiagnostics_validFor
    (contract : FileInternals.ContractDeclInputs)
    (file : SourceFile) (output : ParseOutput)
    (result : parse file = .ok output) :
    ∀ diagnostic ∈ output.parseDiagnostics,
      diagnostic.span.ValidFor file := by
  unfold parse at result
  cases lexing : Lexer.lex file with
  | error diagnostic => simp [lexing] at result
  | ok lexed =>
      cases parsing : parseLexed file lexed with
      | error error => simp [lexing, parsing] at result
      | ok parsedOutput =>
          have outputEq : parsedOutput = output := by
            simpa [lexing, parsing] using result
          subst output
          exact parseLexed_ok_parseDiagnostics_validFor contract file lexed
            parsedOutput parsing

end Solcore.Syntax.Parser
