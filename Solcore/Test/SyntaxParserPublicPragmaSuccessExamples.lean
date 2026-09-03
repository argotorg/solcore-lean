import Solcore.Syntax.Parser.PublicPragmaSuccessOutputProperties
import Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples

/-! Ground complete pragma outputs derived from independent grammar and traces.
Only canonical lexical fixtures are evaluated by kernel-backed decision. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicPragmaSuccessExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples

def atCursor (tokens : List Token) (cursor : Nat) : Remainder := {
  sourceFileRootRemainder tokens with cursor
}

def identifierToken (startByte endByte : Nat) (text : String) : Token := {
  span := byteSpan startByte endByte, value := .identifier text
}

def commaToken (offset : Nat) : Token := {
  span := byteSpan offset (offset + 1), value := .symbol .comma
}

/-- Every output field is explicit, including attached comments and diagnostics. -/
def pragmaOutput (content : String) (lexed : LexedFile) (declaration : PragmaDecl)
    (leading : List Comment) (trace : List ParseDiagnostic) : ParseOutput := {
  parsed := {
    source := exampleSource
    span := SourceSpan.fullFile (exampleFile content)
    items := [{
      span := declaration.span
      leadingComments := leading
      value := .pragmaDecl declaration }]
    comments := lexed.comments
  }
  tokens := lexed.tokens
  lexicalDiagnostics := lexed.diagnostics
  parseDiagnostics := trace
}

def rawTokens (offset : Nat) : List Token := [pragmaToken offset,
  identifierToken (offset + 7) (offset + 14) "foo-bar", semicolonToken (offset + 14)]

def rawDeclaration (offset : Nat) : PragmaDecl := {
  span := SourceSpan.cover (pragmaToken offset).span (semicolonToken (offset + 14)).span
  value := {
    name := { span := byteSpan (offset + 7) (offset + 14), value := "foo-bar" }
    items := [] }
}

/-- The raw name is parsed exactly but contributes no checked-name event. -/
theorem rawParsed (offset : Nat) :
    PragmaDeclTraceParses (sourceFileRootRemainder (rawTokens offset))
      (rawDeclaration offset) (atCursor (rawTokens offset) 3) [] := by
  refine ⟨?_, .nil⟩
  apply PragmaDeclOrdinaryParses.parsed
    (afterKeyword := atCursor (rawTokens offset) 1)
    (afterName := atCursor (rawTokens offset) 2)
    (afterItems := atCursor (rawTokens offset) 2)
    (pragmaToken offset).span (semicolonToken (offset + 14)).span
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, rawTokens, pragmaToken]
  · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, rawTokens, identifierToken]
  · apply PragmaItemsOrdinaryParses.empty
    exact ⟨(semicolonToken (offset + 14)).span, by
      simp [TokenAt, sourceFileRootRemainder, atCursor, rawTokens, semicolonToken]⟩
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, rawTokens, semicolonToken]

theorem rawClears (offset : Nat) : NestingClears (rawTokens offset) :=
  .preserve rfl (.preserve rfl (.reset rfl .done))

set_option maxRecDepth 4096 in
private theorem rawLexes : Lexer.lex (exampleFile "pragma foo-bar;") =
    .ok (lexicalCarrier (rawTokens 0) []) := by
  apply lex_ok_of_toOption
  decide +kernel

/-- A hyphenated raw pragma name has a complete successful, diagnostic-free
public result; it is not checked like a pragma item. -/
theorem rawNameHyphen_parse_eq_output :
    parse (exampleFile "pragma foo-bar;") =
      .ok (pragmaOutput "pragma foo-bar;" (lexicalCarrier (rawTokens 0) [])
        (rawDeclaration 0) [] []) :=
  parse_eq_ok_of_singlePragmaTrace rawLexes (rawClears 0) (rawParsed 0) rfl

def multipleTokens : List Token := [pragmaToken 0, identifierToken 7 8 "p",
  identifierToken 9 20 "foo-bar-baz", commaToken 20,
  identifierToken 21 29 "qux-quux", commaToken 29, semicolonToken 30]

def multipleDeclaration : PragmaDecl := {
  span := byteSpan 0 31
  value := {
    name := { span := byteSpan 7 8, value := "p" }
    items := [{ span := byteSpan 9 20, value := "foo-bar-baz" },
      { span := byteSpan 21 29, value := "qux-quux" }]
  }
}

def multipleTrace : List ParseDiagnostic := [
  { span := byteSpan 9 20, kind := .invalidIdentifierHyphen "foo-bar-baz" },
  { span := byteSpan 21 29, kind := .invalidIdentifierHyphen "qux-quux" }]

private theorem multipleParsed :
    PragmaDeclTraceParses (sourceFileRootRemainder multipleTokens) multipleDeclaration
      (atCursor multipleTokens 7) multipleTrace := by
  refine ⟨?_, .cons (.hyphen (by change '-' ∈ "foo-bar-baz".toList; decide))
    (.cons (.hyphen (by change '-' ∈ "qux-quux".toList; decide)) .nil)⟩
  apply PragmaDeclOrdinaryParses.parsed
    (afterKeyword := atCursor multipleTokens 1)
    (afterName := atCursor multipleTokens 2)
    (afterItems := atCursor multipleTokens 6) (byteSpan 0 6) (byteSpan 30 31)
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, multipleTokens, pragmaToken]
  · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, multipleTokens, identifierToken]
  · apply PragmaItemsOrdinaryParses.nonempty (afterFirst := atCursor multipleTokens 3)
    · simp [TokenKindAbsentAt, TokenAt, atCursor, sourceFileRootRemainder, multipleTokens, identifierToken]
    · simp [IdentifierParses, TokenAt, atCursor, sourceFileRootRemainder, multipleTokens, identifierToken]
    · apply PragmaItemsTailOrdinaryParses.next
        (afterComma := atCursor multipleTokens 4) (afterItem := atCursor multipleTokens 5)
        (byteSpan 20 21)
      · exact ⟨byteSpan 20 21, by
          simp [TokenAt, atCursor, sourceFileRootRemainder, multipleTokens, commaToken]⟩
      · simp [ExactTokenParses, TokenAt, atCursor, sourceFileRootRemainder, multipleTokens, commaToken]
      · simp [TokenKindAbsentAt, TokenAt, atCursor, sourceFileRootRemainder, multipleTokens, identifierToken]
      · simp [IdentifierParses, TokenAt, atCursor, sourceFileRootRemainder, multipleTokens, identifierToken]
      · apply PragmaItemsTailOrdinaryParses.trailing (byteSpan 29 30)
        · exact ⟨byteSpan 29 30, by
            simp [TokenAt, atCursor, sourceFileRootRemainder, multipleTokens, commaToken]⟩
        · simp [ExactTokenParses, TokenAt, atCursor, sourceFileRootRemainder, multipleTokens, commaToken]
        · exact ⟨byteSpan 30 31, by
            simp [TokenAt, atCursor, sourceFileRootRemainder, multipleTokens, semicolonToken]⟩
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, multipleTokens, semicolonToken]

set_option maxRecDepth 8192 in
private theorem multipleLexes : Lexer.lex (exampleFile "pragma p foo-bar-baz,qux-quux,;") =
    .ok (lexicalCarrier multipleTokens []) := by
  apply lex_ok_of_toOption
  decide +kernel

/-- Multiple checked items emit once per item, not once per hyphen. The
trailing comma is accepted and emits no additional event. -/
theorem multipleItemsTrailingComma_parse_eq_output :
    parse (exampleFile "pragma p foo-bar-baz,qux-quux,;") =
      .ok (pragmaOutput "pragma p foo-bar-baz,qux-quux,;" (lexicalCarrier multipleTokens [])
        multipleDeclaration [] multipleTrace) :=
  parse_eq_ok_of_singlePragmaTrace multipleLexes
    (.preserve rfl (.preserve rfl (.preserve rfl (.reset rfl
      (.preserve rfl (.reset rfl (.reset rfl .done))))))) multipleParsed rfl

end Solcore.Test.SyntaxParserPublicPragmaSuccessExamples
