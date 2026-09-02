import Solcore.Syntax.Parser.CoreSourceFileOrdinarySoundnessProperties
import Solcore.Syntax.Parser.FileCompleteProperties

/-! Concrete ordinary grammar soundness at both public parser boundaries. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A diagnostic-free successful token-to-syntax parse follows the concrete
ordinary Core grammar from the root token window. -/
theorem parseLexed_ok_coreOrdinary_sound
    {file : SourceFile} {lexed : LexedFile} {output : ParseOutput}
    (diagnosticFree : output.DiagnosticFree)
    (result : parseLexed file lexed = .ok output) :
    DeclarativeGrammar.CoreSourceFileOrdinaryParsesFromStart file
      lexed.tokens lexed.comments output.parsed := by
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
      simp only [nesting] at result
      cases result
      rcases diagnosticFree with ⟨lexicalFree, parseFree⟩
      change lexed.diagnostics = [] at lexicalFree
      change filterParseDiagnostics file lexed.diagnostics
        [nestingDiagnostic] = [] at parseFree
      rw [lexicalFree, filterParseDiagnostics_nil_lexical] at parseFree
      contradiction
  | none =>
      simp only [nesting] at result
      cases grammar : sourceFile lexed.comments
          (State.initial file lexed) with
      | ok parsed finalState =>
          simp only [grammar] at result
          cases result
          rcases diagnosticFree with ⟨lexicalFree, parseFree⟩
          change lexed.diagnostics = [] at lexicalFree
          change filterParseDiagnostics file lexed.diagnostics
            finalState.diagnostics = [] at parseFree
          rw [lexicalFree, filterParseDiagnostics_nil_lexical] at parseFree
          have finalDiagnosticFree : finalState.diagnosticsRev = [] := by
            simpa [State.diagnostics] using parseFree
          have parsedByCore :=
            FileInternals.sourceFile_success_coreOrdinary_sound_toEnd
              (comments := lexed.comments) (input := State.initial file lexed)
              (next := finalState) (parsedFile := parsed)
              (State.initial_validFor lexedValid)
              (fun comment member => lexedValid.comment_span member)
              finalDiagnosticFree grammar
          simpa [DeclarativeGrammar.CoreSourceFileOrdinaryParsesFromStart,
            State.initial, State.declarativeRemainder] using parsedByCore
      | reject failure rejected =>
          simp only [grammar] at result
          contradiction
      | invariant error =>
          simp only [grammar] at result
          contradiction

/-- Token-to-syntax ordinary soundness paired with canonical parsed-file
validity. -/
theorem parseLexed_ok_coreOrdinary_sound_and_validFor
    {file : SourceFile} {lexed : LexedFile} {output : ParseOutput}
    (diagnosticFree : output.DiagnosticFree)
    (result : parseLexed file lexed = .ok output) :
    DeclarativeGrammar.CoreSourceFileOrdinaryParsesFromStart file
        lexed.tokens lexed.comments output.parsed ∧
      CanonicalParsedFileValid file output.parsed := by
  exact ⟨parseLexed_ok_coreOrdinary_sound diagnosticFree result,
    parseLexed_ok_complete_validFor file lexed output
      (parseLexed_ok_input_validFor file lexed output result) result⟩

/-- A diagnostic-free successful source parse follows the concrete ordinary
Core grammar over the exact carriers retained in its public output. -/
theorem parse_ok_coreOrdinary_sound
    {file : SourceFile} {output : ParseOutput}
    (diagnosticFree : output.DiagnosticFree)
    (result : parse file = .ok output) :
    DeclarativeGrammar.CoreSourceFileOrdinaryParsesFromStart file
      output.tokens output.parsed.comments output.parsed := by
  rcases parse_ok_lexed_provenance file output result with
    ⟨lexed, _lexing, parsing, tokens, _diagnostics, comments⟩
  simpa only [tokens, comments] using
    parseLexed_ok_coreOrdinary_sound diagnosticFree parsing

/-- Public source ordinary soundness paired with canonical parsed-file
validity. -/
theorem parse_ok_coreOrdinary_sound_and_validFor
    {file : SourceFile} {output : ParseOutput}
    (diagnosticFree : output.DiagnosticFree)
    (result : parse file = .ok output) :
    DeclarativeGrammar.CoreSourceFileOrdinaryParsesFromStart file
        output.tokens output.parsed.comments output.parsed ∧
      CanonicalParsedFileValid file output.parsed := by
  rcases parse_ok_lexed_provenance file output result with
    ⟨lexed, _lexing, parsing, tokens, _diagnostics, comments⟩
  have paired := parseLexed_ok_coreOrdinary_sound_and_validFor
    diagnosticFree parsing
  exact ⟨by simpa only [tokens, comments] using paired.1, paired.2⟩

end Solcore.Syntax.Parser
