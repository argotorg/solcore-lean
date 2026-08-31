import Solcore.Syntax.Parser.File
import Solcore.Syntax.Parser.DiagnosticFilter
import Solcore.Syntax.Parser.Preflight
import Solcore.Syntax.Parser.Validity
import Solcore.Syntax.Parser.LiteralProperties
import Solcore.Syntax.Parser.StateCursorProperties

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private def emptyParsedFile (file : SourceFile)
    (comments : List Comment) : ParsedFile := {
  source := file.id
  span := SourceSpan.fullFile file
  items := []
  comments
}

/-- Parse already-tokenized canonical syntax after validating its provenance. -/
def parseLexed (file : SourceFile)
    (lexed : LexedFile) : Except ParserInvariantError ParseOutput := do
  validateLexed file lexed
  match checkNesting lexed.tokens with
  | some diagnostic => pure {
      parsed := emptyParsedFile file lexed.comments
      tokens := lexed.tokens
      lexicalDiagnostics := lexed.diagnostics
      parseDiagnostics :=
        filterParseDiagnostics file lexed.diagnostics [diagnostic]
    }
  | none =>
      match sourceFile lexed.comments (State.initial file lexed) with
      | .ok parsed finalState => pure {
          parsed
          tokens := lexed.tokens
          lexicalDiagnostics := lexed.diagnostics
          parseDiagnostics :=
            filterParseDiagnostics file lexed.diagnostics
              finalState.diagnostics
        }
      | .reject failure _ =>
          throw (.noProgress .topLevel failure.span)
      | .invariant error => throw error

/-- Total source-to-syntax entry point; only executor invariants are errors. -/
def parse (file : SourceFile) : ParseResult :=
  match Lexer.lex file with
  | .error diagnostic => .error (.lexerInvariant diagnostic)
  | .ok lexed =>
      match parseLexed file lexed with
      | .ok output => .ok output
      | .error error => .error (.parserInvariant error)

end Solcore.Syntax.Parser
