import Solcore.Syntax.DeclarativePublicSourceFileOutcomeProperties
import Solcore.Syntax.Parser.CompleteOutputProperties
import Solcore.Syntax.Parser.Nesting
import Solcore.Syntax.Parser.SourceFileOrdinaryOutcomeSoundnessProperties

/-! Broad syntax outcomes at both public canonical parser boundaries. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful token-to-file parse has the exact public syntax shape:
either the canonical empty file after nesting overflow, or the recovery-aware
source-file grammar from the root token window. -/
theorem parseLexed_ok_publicSourceFileOrdinary_sound
    {file : SourceFile} {lexed : LexedFile} {output : ParseOutput}
    (result : parseLexed file lexed = .ok output) :
    DeclarativeGrammar.PublicSourceFileOrdinaryParses file
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
        match sourceFile lexed.comments
            (State.initial file lexed) with
        | .ok parsed finalState => Except.ok ({
            parsed
            tokens := lexed.tokens
            lexicalDiagnostics := lexed.diagnostics
            parseDiagnostics := filterParseDiagnostics file
              lexed.diagnostics finalState.diagnostics
          } : ParseOutput)
        | .reject failure _ => Except.error
            (ParserInvariantError.noProgress .topLevel failure.span)
        | .invariant error => Except.error error) = .ok output at result
  cases nesting : checkNesting lexed.tokens with
  | some diagnostic =>
      have exceeds :=
        (checkNesting_some_iff_nestingExceeds
          lexed.tokens diagnostic).mp nesting
      rcases exceeds with ⟨overflow, overflowScan, _diagnosticEq⟩
      simp only [nesting] at result
      cases result
      exact .nestingExceeded overflowScan
  | none =>
      have clears :=
        (checkNesting_none_iff_nestingClears lexed.tokens).mp nesting
      simp only [nesting] at result
      cases grammar : sourceFile lexed.comments
          (State.initial file lexed) with
      | ok parsed finalState =>
          simp only [grammar] at result
          cases result
          have sourceParsed :=
            FileInternals.sourceFile_success_ordinaryOutcome_sound grammar
          apply DeclarativeGrammar.PublicSourceFileOrdinaryParses.sourceFile
            clears
          simpa [DeclarativeGrammar.sourceFileRootRemainder,
            State.initial, State.declarativeRemainder] using sourceParsed
      | reject failure rejected =>
          simp only [grammar] at result
          contradiction
      | invariant error =>
          simp only [grammar] at result
          contradiction

/-- Broad token-to-file syntax soundness paired with the complete canonical
validity contract for every retained public carrier. -/
theorem parseLexed_ok_publicSourceFileOrdinary_sound_and_validFor
    {file : SourceFile} {lexed : LexedFile} {output : ParseOutput}
    (result : parseLexed file lexed = .ok output) :
    DeclarativeGrammar.PublicSourceFileOrdinaryParses file
        lexed.tokens lexed.comments output.parsed ∧
      output.CanonicalValidFor file :=
  ⟨parseLexed_ok_publicSourceFileOrdinary_sound result,
    parseLexed_ok_completeOutput_validFor file lexed output result⟩

/-- Every successful source parse has the broad syntax outcome over the exact
tokens and comments retained by its public output. -/
theorem parse_ok_publicSourceFileOrdinary_sound
    {file : SourceFile} {output : ParseOutput}
    (result : parse file = .ok output) :
    DeclarativeGrammar.PublicSourceFileOrdinaryParses file
      output.tokens output.parsed.comments output.parsed := by
  rcases parse_ok_lexed_provenance file output result with
    ⟨lexed, _lexing, parsing, tokens, _diagnostics, comments⟩
  simpa only [tokens, comments] using
    parseLexed_ok_publicSourceFileOrdinary_sound parsing

/-- Broad source parsing soundness paired with the complete canonical output
validity contract. -/
theorem parse_ok_publicSourceFileOrdinary_sound_and_validFor
    {file : SourceFile} {output : ParseOutput}
    (result : parse file = .ok output) :
    DeclarativeGrammar.PublicSourceFileOrdinaryParses file
        output.tokens output.parsed.comments output.parsed ∧
      output.CanonicalValidFor file :=
  ⟨parse_ok_publicSourceFileOrdinary_sound result,
    parse_ok_completeOutput_validFor file output result⟩

end Solcore.Syntax.Parser
