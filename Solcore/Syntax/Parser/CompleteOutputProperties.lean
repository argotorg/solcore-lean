import Solcore.Syntax.Parser.FileCompleteProperties
import Solcore.Syntax.Parser.PublicDiagnosticValidityProperties

/-! Complete provenance contract for successful public parser output. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace ParseOutput

/-- Canonical syntax and every retained diagnostic carrier belong to one file. -/
structure CanonicalValidFor (output : ParseOutput) (file : SourceFile) : Prop where
  parsed : Parser.CanonicalParsedFileValid file output.parsed
  tokens : ∀ token ∈ output.tokens, token.span.ValidFor file
  lexicalDiagnostics : ∀ diagnostic ∈ output.lexicalDiagnostics,
    diagnostic.span.ValidFor file
  parseDiagnostics : ∀ diagnostic ∈ output.parseDiagnostics,
    diagnostic.span.ValidFor file

end ParseOutput

namespace Parser

/-- Successful token-to-syntax parsing satisfies the complete output contract. -/
theorem parseLexed_ok_completeOutput_validFor
    (file : SourceFile) (lexed : LexedFile) (output : ParseOutput)
    (result : parseLexed file lexed = .ok output) :
    output.CanonicalValidFor file := by
  have lexedValid := parseLexed_ok_input_validFor file lexed output result
  have retained := parseLexed_ok_retention file lexed output result
  exact {
    parsed := parseLexed_ok_complete_validFor file lexed output lexedValid result
    tokens := by
      intro token member
      exact lexedValid.token_span (by
        simpa only [retained.1] using member)
    lexicalDiagnostics := by
      intro diagnostic member
      exact lexedValid.diagnostic_span (by
        simpa only [retained.2.1] using member)
    parseDiagnostics :=
      parseLexed_ok_parseDiagnostics_validFor
        FileInternals.contractDecl_canonical_inputs file lexed output result
  }

/-- Successful public source parsing satisfies the complete output contract. -/
theorem parse_ok_completeOutput_validFor
    (file : SourceFile) (output : ParseOutput)
    (result : parse file = .ok output) :
    output.CanonicalValidFor file := by
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
          exact parseLexed_ok_completeOutput_validFor file lexed parsedOutput
            parsing

end Parser

end Solcore.Syntax
