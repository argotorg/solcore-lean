import Solcore.Syntax.DeclarativePragmaRejectionTraceGrammar
import Solcore.Test.SyntaxParserPublicPragmaSuccessExamples

/-! Canonical carriers and independent exact later-stage pragma rejection.
Only lexical fixtures are evaluated; parser replies are never assumed here. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaLaterRejectionFixtures

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples
open Solcore.Test.SyntaxParserPublicPragmaSuccessExamples

def prefixTokens (offset : Nat) : List Token := [pragmaToken offset,
  identifierToken (offset + 7) (offset + 8) "p",
  identifierToken (offset + 9) (offset + 12) "a-b"]

def missingItemTokens (offset : Nat) : List Token :=
  prefixTokens offset ++ [commaToken (offset + 12)]

def rawName (offset : Nat) : Identifier := {
  span := byteSpan (offset + 7) (offset + 8), value := "p"
}

def checkedItem (offset : Nat) : Identifier := {
  span := byteSpan (offset + 9) (offset + 12), value := "a-b"
}

def hyphenEvent (offset : Nat) : ParseDiagnostic := {
  span := (checkedItem offset).span, kind := .invalidIdentifierHyphen "a-b"
}

def eofUnexpected (endByte : Nat) (expected : ParseExpectation) : ParseDiagnostic := {
  span := byteSpan endByte endByte
  kind := .unexpected none { head := expected, tail := [] } .pragmaDecl
}

def lexicalInvalid : LexicalDiagnostic := { span := byteSpan 0 2, kind := .invalidToken }

theorem prefixKeyword (offset : Nat) (rest : List Token) :
    ExactTokenParses (.keyword .pragmaKw) (sourceFileRootRemainder (prefixTokens offset ++ rest))
      (pragmaToken offset).span (atCursor (prefixTokens offset ++ rest) 1) := by
  simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, prefixTokens, pragmaToken]

theorem prefixClears (offset : Nat) (rest : List Token) (clears : NestingClears rest) :
    NestingClears (prefixTokens offset ++ rest) :=
  .preserve rfl (.preserve rfl (.preserve rfl clears))

/-- The first item succeeds and emits once; the comma then requires a new
identifier, so EOF reports an identifier expectation at the exact byte end. -/
theorem missingItemDeclRejects (offset : Nat) :
    PragmaDeclTraceRejects exampleSource (offset + 13)
      (sourceFileRootRemainder (missingItemTokens offset))
      (atCursor (missingItemTokens offset) 4)
      (eofUnexpected (offset + 13) .identifier) [hyphenEvent offset] := by
  apply PragmaDeclTraceRejects.itemsRejected
    (afterKeyword := atCursor (missingItemTokens offset) 1)
    (afterName := atCursor (missingItemTokens offset) 2)
    (name := rawName offset) (pragmaToken offset).span
  · exact prefixKeyword offset [commaToken (offset + 12)]
  · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor,
      missingItemTokens, prefixTokens, rawName, identifierToken]
  · refine ⟨[checkedItem offset], ?_,
      .cons (.hyphen (by change '-' ∈ "a-b".toList; decide)) .nil, ?_⟩
    · apply PragmaItemsRejectedPrefix.tailRejected
        (afterFirst := atCursor (missingItemTokens offset) 3)
      · simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor,
          missingItemTokens, prefixTokens, identifierToken]
      · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor,
          missingItemTokens, prefixTokens, checkedItem, identifierToken]
      · apply PragmaItemsTailRejectedPrefix.identifierRejected
          (afterComma := atCursor (missingItemTokens offset) 4)
          (byteSpan (offset + 12) (offset + 13))
        · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor,
            missingItemTokens, prefixTokens, commaToken, Nat.add_assoc]
        · simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor,
            missingItemTokens, prefixTokens]
        · apply IdentifierRejects.absent
          simp [IdentifierAbsentAt, TokenAt, sourceFileRootRemainder, atCursor,
            missingItemTokens, prefixTokens]
    · apply RejectAtReports.reported
      exact .windowEnd (by simp [sourceFileRootRemainder, atCursor, missingItemTokens, prefixTokens])

/-- Without a comma the item scan succeeds; only the final semicolon is
missing, and the already emitted hyphen event still precedes its report. -/
theorem missingSemicolonDeclRejects (offset : Nat) :
    PragmaDeclTraceRejects exampleSource (offset + 12)
      (sourceFileRootRemainder (prefixTokens offset)) (atCursor (prefixTokens offset) 3)
      (eofUnexpected (offset + 12) (.symbol .semicolon)) [hyphenEvent offset] := by
  apply PragmaDeclTraceRejects.semicolonMissing
    (afterKeyword := atCursor (prefixTokens offset) 1)
    (afterName := atCursor (prefixTokens offset) 2)
    (name := rawName offset) (items := [checkedItem offset]) (pragmaToken offset).span
  · exact prefixKeyword offset []
  · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor,
      prefixTokens, rawName, identifierToken]
  · refine ⟨?_, .cons (.hyphen (by change '-' ∈ "a-b".toList; decide)) .nil⟩
    apply PragmaItemsOrdinaryParses.nonempty (afterFirst := atCursor (prefixTokens offset) 3)
    · simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, prefixTokens, identifierToken]
    · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, prefixTokens,
        checkedItem, identifierToken]
    · apply PragmaItemsTailOrdinaryParses.done
      simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, prefixTokens]
  · simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, prefixTokens]
  · apply RejectAtReports.reported
    exact .windowEnd (by simp [sourceFileRootRemainder, atCursor, prefixTokens])

set_option maxRecDepth 8192 in
theorem missingItemLexes : Lexer.lex (exampleFile "pragma p a-b,") =
    .ok (lexicalCarrier (missingItemTokens 0) []) := by
  apply lex_ok_of_toOption
  decide +kernel

set_option maxRecDepth 8192 in
theorem missingSemicolonLexes : Lexer.lex (exampleFile "pragma p a-b") =
    .ok (lexicalCarrier (prefixTokens 0) []) := by
  apply lex_ok_of_toOption
  decide +kernel

set_option maxRecDepth 8192 in
theorem sameLineLexes : Lexer.lex (exampleFile "§ pragma p a-b,") =
    .ok (lexicalCarrier (missingItemTokens 3) [lexicalInvalid]) := by
  apply lex_ok_of_toOption
  decide +kernel

end Solcore.Test.SyntaxParserPragmaLaterRejectionFixtures
