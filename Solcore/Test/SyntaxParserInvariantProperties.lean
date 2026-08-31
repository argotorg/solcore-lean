import Solcore.Syntax.Parser.Properties

/-! External consumers for public frontend invariant classification. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example (file : SourceFile) (diagnostic : LexicalDiagnostic)
    (result : parse file = .error (.lexerInvariant diagnostic)) : False :=
  parse_lexerInvariant_impossible file diagnostic result

example (file : SourceFile) (error : SyntaxInvariantError)
    (result : parse file = .error error) :
    ∃ lexed parserError,
      Lexer.lex file = .ok lexed ∧
      parseLexed file lexed = .error parserError ∧
      error = .parserInvariant parserError :=
  parse_error_parserInvariant file error result

end Tests
