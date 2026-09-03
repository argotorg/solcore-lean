import Solcore.Syntax.Parser.PublicEmptyTokensOutputProperties

/-! Empty, whitespace-only, comment-only, and diagnosed tokenless source outputs.
The kernel evaluates only lexical fixtures; public parsing uses the exact law. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicEmptyTokensExamples

open Solcore.Syntax
open Solcore.Syntax.Parser

private def sourceId : SourceId := { origin := .main, path := "empty-tokens.sol" }

private def exampleFile (content : String) : SourceFile := { id := sourceId, content }

private def byteSpan (startByte endByte : Nat) : SourceSpan := {
  source := sourceId, startByte, endByte
}

private def carrier (comments : List Comment) (diagnostics : List LexicalDiagnostic) : LexedFile := {
  source := sourceId, tokens := [], comments, diagnostics
}

private def expectedOutput (content : String) (comments : List Comment)
    (lexical : List LexicalDiagnostic) : ParseOutput := {
  parsed := {
    source := sourceId
    span := SourceSpan.fullFile (exampleFile content)
    items := []
    comments
  }
  tokens := []
  lexicalDiagnostics := lexical
  parseDiagnostics := []
}

private theorem complete (content : String) (comments : List Comment)
    (lexical : List LexicalDiagnostic)
    (checked : (Lexer.lex (exampleFile content)).toOption = some (carrier comments lexical)) :
    parse (exampleFile content) = .ok (expectedOutput content comments lexical) := by
  have lexing : Lexer.lex (exampleFile content) = .ok (carrier comments lexical) := by
    cases result : Lexer.lex (exampleFile content) with
    | error error => simp only [result, Except.toOption] at checked; contradiction
    | ok actual => simp only [result, Except.toOption] at checked; cases checked; rfl
  exact parse_eq_ok_of_emptyTokens lexing rfl

set_option maxRecDepth 4096 in
/-- Empty text produces the exact empty normal output. -/
theorem empty_parse_eq_output :
    parse (exampleFile "") = .ok (expectedOutput "" [] []) := by
  apply complete
  decide +kernel

set_option maxRecDepth 4096 in
/-- Whitespace changes the full-file byte span but produces no token or report. -/
theorem whitespace_parse_eq_output :
    parse (exampleFile " \r\n") = .ok (expectedOutput " \r\n" [] []) := by
  apply complete
  decide +kernel

set_option maxRecDepth 4096 in
/-- The comment's original text and delimiter-inclusive span remain in the file. -/
theorem commentOnly_parse_eq_output :
    parse (exampleFile "/*note*/") = .ok (expectedOutput "/*note*/"
      [{ kind := .block, text := "note", span := byteSpan 0 8 }] []) := by
  apply complete
  decide +kernel

set_option maxRecDepth 4096 in
/-- A lexical error can survive in a tokenless normal output without inventing
a parser recovery or unexpected-token diagnostic. -/
theorem invalidTokenOnly_parse_eq_output :
    parse (exampleFile "§") = .ok (expectedOutput "§" []
      [{ span := byteSpan 0 2, kind := .invalidToken }]) := by
  apply complete
  decide +kernel

end Solcore.Test.SyntaxParserPublicEmptyTokensExamples
