import Solcore.Test.SyntaxParserPublicPragmaSuccessExamples

/-! Lexical cascades cannot suppress successful pragma's protected identifier
events. A comment fixture also fixes both retained and attached comment lists. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicPragmaProtectedTraceExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples
open Solcore.Test.SyntaxParserPublicPragmaSuccessExamples

private def invalidToken : LexicalDiagnostic := {
  span := byteSpan 0 2, kind := .invalidToken
}

private def protectedTokens : List Token := [pragmaToken 3, identifierToken 10 11 "p",
  identifierToken 12 19 "foo-bar", semicolonToken 19]

private def protectedDeclaration : PragmaDecl := {
  span := byteSpan 3 20
  value := {
    name := { span := byteSpan 10 11, value := "p" }
    items := [{ span := byteSpan 12 19, value := "foo-bar" }]
  }
}

private def protectedTrace : List ParseDiagnostic := [
  { span := byteSpan 12 19, kind := .invalidIdentifierHyphen "foo-bar" }]

private theorem protectedParsed :
    PragmaDeclTraceParses (sourceFileRootRemainder protectedTokens) protectedDeclaration
      (atCursor protectedTokens 4) protectedTrace := by
  refine ⟨?_, .cons (.hyphen (by change '-' ∈ "foo-bar".toList; decide)) .nil⟩
  apply PragmaDeclOrdinaryParses.parsed
    (afterKeyword := atCursor protectedTokens 1)
    (afterName := atCursor protectedTokens 2)
    (afterItems := atCursor protectedTokens 3) (byteSpan 3 9) (byteSpan 19 20)
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, protectedTokens, pragmaToken]
  · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, protectedTokens, identifierToken]
  · apply PragmaItemsOrdinaryParses.nonempty (afterFirst := atCursor protectedTokens 3)
    · simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, protectedTokens, identifierToken]
    · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, protectedTokens, identifierToken]
    · apply PragmaItemsTailOrdinaryParses.done
      simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, protectedTokens, semicolonToken]
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, protectedTokens, semicolonToken]

set_option maxRecDepth 8192 in
private theorem protectedLexes : Lexer.lex (exampleFile "§ pragma p foo-bar;") =
    .ok (lexicalCarrier protectedTokens [invalidToken]) := by
  apply lex_ok_of_toOption
  decide +kernel

/-- These two spans satisfy the same-LF-line cascade relation that would
suppress an unexpected/recovery report, making protection non-vacuous. -/
theorem sameLineCascadeApplies :
    LexicalCascadeSuppresses "§ pragma p foo-bar;" [invalidToken.span] (byteSpan 12 19) := by
  exact ⟨invalidToken.span, by simp, rfl, Or.inl (by decide)⟩

/-- The lexical invalid character and checked-name diagnostic both remain,
with exact independent spans and a complete singleton-pragma AST. -/
theorem protectedHyphen_parse_eq_output :
    parse (exampleFile "§ pragma p foo-bar;") =
      .ok (pragmaOutput "§ pragma p foo-bar;" (lexicalCarrier protectedTokens [invalidToken])
        protectedDeclaration [] protectedTrace) :=
  parse_eq_ok_of_singlePragmaTrace protectedLexes
    (.preserve rfl (.preserve rfl (.preserve rfl (.reset rfl .done)))) protectedParsed rfl

/-- Already-tokenized public parsing preserves the identical protected trace. -/
theorem protectedHyphen_parseLexed_eq_output :
    parseLexed (exampleFile "§ pragma p foo-bar;") (lexicalCarrier protectedTokens [invalidToken]) =
      .ok (pragmaOutput "§ pragma p foo-bar;" (lexicalCarrier protectedTokens [invalidToken])
        protectedDeclaration [] protectedTrace) :=
  parseLexed_eq_ok_of_singlePragmaTrace
    ((lexedFileValidationAccepts_iff_validFor _ _).mpr (Lexer.lex_ok_validFor _ _ protectedLexes))
    (.preserve rfl (.preserve rfl (.preserve rfl (.reset rfl .done)))) protectedParsed rfl

private def docComment : Comment := {
  kind := .line, text := " doc", span := byteSpan 0 6
}

private def commentedLexed : LexedFile := {
  source := exampleSource, tokens := rawTokens 7, comments := [docComment], diagnostics := []
}

set_option maxRecDepth 8192 in
private theorem commentLexes : Lexer.lex (exampleFile "// doc\npragma foo-bar;") =
    .ok commentedLexed := by
  apply lex_ok_of_toOption
  decide +kernel

/-- The original line comment is retained file-wide and attached once to the
pragma item. The raw hyphenated name still contributes no diagnostic event. -/
theorem commentAttachment_parse_eq_output :
    parse (exampleFile "// doc\npragma foo-bar;") =
      .ok (pragmaOutput "// doc\npragma foo-bar;" commentedLexed
        (rawDeclaration 7) [docComment] []) :=
  parse_eq_ok_of_singlePragmaTrace commentLexes (rawClears 7) (rawParsed 7) rfl

end Solcore.Test.SyntaxParserPublicPragmaProtectedTraceExamples
