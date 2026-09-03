import Solcore.Syntax.Parser.PublicPragmaSequenceOutputProperties
import Solcore.Test.SyntaxParserPublicPragmaSuccessExamples

/-! Ground complete outputs of two independently traced pragma declarations.
Only lexical fixtures use kernel-backed evaluation; public parsing is derived
from the independent sequence grammar, including ordered protected events. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicPragmaSequenceExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples
open Solcore.Test.SyntaxParserPublicPragmaSuccessExamples

private def sequenceTokens (secondOffset : Nat) : List Token := [
  pragmaToken 0, identifierToken 7 8 "p", identifierToken 9 12 "a-b", semicolonToken 12,
  pragmaToken secondOffset, identifierToken (secondOffset + 7) (secondOffset + 8) "q",
  identifierToken (secondOffset + 9) (secondOffset + 12) "c-d",
  semicolonToken (secondOffset + 12)]

private def firstDeclaration : PragmaDecl := {
  span := byteSpan 0 13
  value := {
    name := { span := byteSpan 7 8, value := "p" }
    items := [{ span := byteSpan 9 12, value := "a-b" }]
  }
}

private def secondDeclaration (offset : Nat) : PragmaDecl := {
  span := SourceSpan.cover (pragmaToken offset).span (semicolonToken (offset + 12)).span
  value := {
    name := { span := byteSpan (offset + 7) (offset + 8), value := "q" }
    items := [{ span := byteSpan (offset + 9) (offset + 12), value := "c-d" }]
  }
}

private def firstEvent : ParseDiagnostic := {
  span := byteSpan 9 12, kind := .invalidIdentifierHyphen "a-b"
}

private def secondEvent (offset : Nat) : ParseDiagnostic := {
  span := byteSpan (offset + 9) (offset + 12), kind := .invalidIdentifierHyphen "c-d"
}

private theorem firstParsed (offset : Nat) :
    PragmaDeclTraceParses (sourceFileRootRemainder (sequenceTokens offset)) firstDeclaration
      (atCursor (sequenceTokens offset) 4) [firstEvent] := by
  refine ⟨?_, .cons (.hyphen (by change '-' ∈ "a-b".toList; decide)) .nil⟩
  apply PragmaDeclOrdinaryParses.parsed
    (afterKeyword := atCursor (sequenceTokens offset) 1)
    (afterName := atCursor (sequenceTokens offset) 2)
    (afterItems := atCursor (sequenceTokens offset) 3) (byteSpan 0 6) (byteSpan 12 13)
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, sequenceTokens, pragmaToken]
  · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, sequenceTokens, identifierToken]
  · apply PragmaItemsOrdinaryParses.nonempty (afterFirst := atCursor (sequenceTokens offset) 3)
    · simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, sequenceTokens, identifierToken]
    · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, sequenceTokens, identifierToken]
    · apply PragmaItemsTailOrdinaryParses.done
      simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, sequenceTokens, semicolonToken]
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, sequenceTokens, semicolonToken]

private theorem secondParsed (offset : Nat) :
    PragmaDeclTraceParses (atCursor (sequenceTokens offset) 4) (secondDeclaration offset)
      (atCursor (sequenceTokens offset) 8) [secondEvent offset] := by
  refine ⟨?_, .cons (.hyphen (by change '-' ∈ "c-d".toList; decide)) .nil⟩
  apply PragmaDeclOrdinaryParses.parsed
    (afterKeyword := atCursor (sequenceTokens offset) 5)
    (afterName := atCursor (sequenceTokens offset) 6)
    (afterItems := atCursor (sequenceTokens offset) 7)
    (pragmaToken offset).span (semicolonToken (offset + 12)).span
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, sequenceTokens, pragmaToken]
  · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, sequenceTokens, identifierToken]
  · apply PragmaItemsOrdinaryParses.nonempty (afterFirst := atCursor (sequenceTokens offset) 7)
    · simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, sequenceTokens, identifierToken]
    · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, sequenceTokens, identifierToken]
    · apply PragmaItemsTailOrdinaryParses.done
      simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, sequenceTokens, semicolonToken]
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, sequenceTokens, semicolonToken]

private theorem sequenceParsed (offset : Nat) :
    PragmaSequenceTraceParses (sourceFileRootRemainder (sequenceTokens offset))
      [firstDeclaration, secondDeclaration offset] (atCursor (sequenceTokens offset) 8)
      [firstEvent, secondEvent offset] :=
  .cons (firstParsed offset) (.cons (secondParsed offset)
    (.done (by simp [atCursor, sourceFileRootRemainder, sequenceTokens])))

private theorem sequenceClears (offset : Nat) : NestingClears (sequenceTokens offset) :=
  .preserve rfl (.preserve rfl (.preserve rfl (.reset rfl
    (.preserve rfl (.preserve rfl (.preserve rfl (.reset rfl .done)))))))

/-- Both AST nodes and both diagnostics are explicit, in written order. -/
private def sequenceOutput (content : String) (offset : Nat)
    (lexical : List LexicalDiagnostic) : ParseOutput := {
  parsed := {
    source := exampleSource
    span := SourceSpan.fullFile (exampleFile content)
    items := [
      { span := firstDeclaration.span, leadingComments := [], value := .pragmaDecl firstDeclaration },
      { span := (secondDeclaration offset).span, leadingComments := [],
        value := .pragmaDecl (secondDeclaration offset) }]
    comments := []
  }
  tokens := sequenceTokens offset
  lexicalDiagnostics := lexical
  parseDiagnostics := [firstEvent, secondEvent offset]
}

set_option maxRecDepth 8192 in
private theorem cleanLexes : Lexer.lex (exampleFile "pragma p a-b; pragma q c-d;") =
    .ok (lexicalCarrier (sequenceTokens 14) []) := by
  apply lex_ok_of_toOption
  decide +kernel

/-- Two declarations emit one event per checked item. The first declaration's
event precedes exactly one event from the second, without duplication. -/
theorem twoPragmas_parse_eq_output :
    parse (exampleFile "pragma p a-b; pragma q c-d;") =
      .ok (sequenceOutput "pragma p a-b; pragma q c-d;" 14 []) :=
  parse_eq_ok_of_pragmaSequence cleanLexes (sequenceClears 14) (sequenceParsed 14)

private def betweenInvalid : LexicalDiagnostic := {
  span := byteSpan 14 16, kind := .invalidToken
}

set_option maxRecDepth 8192 in
private theorem diagnosedLexes : Lexer.lex (exampleFile "pragma p a-b; § pragma q c-d;") =
    .ok (lexicalCarrier (sequenceTokens 17) [betweenInvalid]) := by
  apply lex_ok_of_toOption
  decide +kernel

/-- The lexical error between pragmas is on both events' LF line, so ordinary
expectation or recovery events at either exact span would be suppressed. -/
theorem sameLineCascadeAppliesToBoth :
    LexicalCascadeSuppresses "pragma p a-b; § pragma q c-d;"
        [betweenInvalid.span] firstEvent.span ∧
      LexicalCascadeSuppresses "pragma p a-b; § pragma q c-d;"
        [betweenInvalid.span] (secondEvent 17).span := by
  constructor
  · exact ⟨betweenInvalid.span, by simp, rfl, Or.inl (by decide)⟩
  · exact ⟨betweenInvalid.span, by simp, rfl, Or.inl (by decide)⟩

/-- A real lexical diagnostic between the declarations does not suppress or
reorder either protected checked-name event; the complete carrier is retained. -/
theorem protectedTwoPragmas_parse_eq_output :
    parse (exampleFile "pragma p a-b; § pragma q c-d;") =
      .ok (sequenceOutput "pragma p a-b; § pragma q c-d;" 17 [betweenInvalid]) :=
  parse_eq_ok_of_pragmaSequence diagnosedLexes (sequenceClears 17) (sequenceParsed 17)

/-- The validated token-to-file entry point exposes the identical complete
two-pragma AST, lexical error, and ordered protected diagnostic sequence. -/
theorem protectedTwoPragmas_parseLexed_eq_output :
    parseLexed (exampleFile "pragma p a-b; § pragma q c-d;")
        (lexicalCarrier (sequenceTokens 17) [betweenInvalid]) =
      .ok (sequenceOutput "pragma p a-b; § pragma q c-d;" 17 [betweenInvalid]) :=
  parseLexed_eq_ok_of_pragmaSequence
    ((lexedFileValidationAccepts_iff_validFor _ _).mpr (Lexer.lex_ok_validFor _ _ diagnosedLexes))
    (sequenceClears 17) (sequenceParsed 17)

end Solcore.Test.SyntaxParserPublicPragmaSequenceExamples
