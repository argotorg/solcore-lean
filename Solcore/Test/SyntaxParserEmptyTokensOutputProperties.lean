import Solcore.Syntax.Parser.PublicEmptyTokensOutputProperties

/-! Complete empty-token outputs retain comments and lexical diagnostics. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserEmptyTokensOutputProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

example (comments : List Comment) (input : State)
    (atEnd : input.window.endIndex ≤ input.cursor) :
    sourceFile comments input = .ok {
      source := input.file.id
      span := SourceSpan.fullFile input.file
      items := []
      comments
    } input :=
  sourceFile_atWindowEnd_exact comments atEnd

example {file : SourceFile} {lexed : LexedFile}
    (empty : lexed.tokens = [])
    (accepted : LexedFileValidationAccepts file lexed) :
    parseLexed file lexed = .ok {
      parsed := {
        source := file.id
        span := SourceSpan.fullFile file
        items := []
        comments := lexed.comments
      }
      tokens := lexed.tokens
      lexicalDiagnostics := lexed.diagnostics
      parseDiagnostics := []
    } :=
  parseLexed_eq_ok_of_emptyTokens accepted empty

example {file : SourceFile} {lexed : LexedFile}
    (empty : lexed.tokens = [])
    (result : parseLexed file lexed = .ok (emptyTokensParseOutput file lexed)) :
    LexedFileValidationAccepts file lexed :=
  (parseLexed_eq_ok_emptyTokens_iff empty).mp result

example {file : SourceFile} {lexed : LexedFile}
    (lexing : Lexer.lex file = .ok lexed) (empty : lexed.tokens = []) :
    parse file = .ok (emptyTokensParseOutput file lexed) :=
  parse_eq_ok_of_emptyTokens lexing empty

end Solcore.Test.SyntaxParserEmptyTokensOutputProperties
