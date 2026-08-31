import Solcore

/-! External compile consumers for canonical syntax provenance laws. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example (file : SourceFile) (lexed : LexedFile)
    (result : Lexer.lex file = .ok lexed) :
    lexed.source = file.id :=
  Lexer.lex_ok_source file lexed result

example (file : SourceFile) (diagnostic : LexicalDiagnostic)
    (result : Lexer.lex file = .error diagnostic) :
    diagnostic.span.source = file.id :=
  Lexer.lex_error_source file diagnostic result

example (file : SourceFile) (output : ParseOutput)
    (result : Parser.parse file = .ok output) :
    output.parsed.source = file.id :=
  Parser.parse_ok_source file output result

example (file : SourceFile) (output : ParseOutput)
    (result : Parser.parse file = .ok output) :
    output.parsed.span = SourceSpan.fullFile file :=
  Parser.parse_ok_span file output result

end Tests
