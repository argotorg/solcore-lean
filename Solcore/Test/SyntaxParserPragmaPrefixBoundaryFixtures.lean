import Solcore.Syntax.DeclarativePragmaPrefixBoundaryTraceProperties
import Solcore.Test.SyntaxParserPragmaLaterRejectionFixtures

/-! Canonical successful-then-rejected pragma carriers. Independent grammar
fixes the successful AST, rewound second marker, and two prior identifier events. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaPrefixBoundaryFixtures

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples
open Solcore.Test.SyntaxParserPublicPragmaSuccessExamples
open Solcore.Test.SyntaxParserPragmaLaterRejectionFixtures (eofUnexpected)

def boundaryTokens (secondOffset : Nat) : List Token := [
  pragmaToken 0, identifierToken 7 8 "p", identifierToken 9 12 "a-b", semicolonToken 12,
  pragmaToken secondOffset, identifierToken (secondOffset + 7) (secondOffset + 8) "q",
  identifierToken (secondOffset + 9) (secondOffset + 12) "c-d",
  commaToken (secondOffset + 12)]

def keptDeclaration : PragmaDecl := {
  span := byteSpan 0 13
  value := {
    name := { span := byteSpan 7 8, value := "p" }
    items := [{ span := byteSpan 9 12, value := "a-b" }]
  }
}

def firstEvent : ParseDiagnostic := {
  span := byteSpan 9 12, kind := .invalidIdentifierHyphen "a-b"
}

def failedItem (offset : Nat) : Identifier := {
  span := byteSpan (offset + 9) (offset + 12), value := "c-d"
}

def secondEvent (offset : Nat) : ParseDiagnostic := {
  span := (failedItem offset).span, kind := .invalidIdentifierHyphen "c-d"
}

private theorem firstParsed (offset : Nat) :
    PragmaDeclTraceParses (sourceFileRootRemainder (boundaryTokens offset)) keptDeclaration
      (atCursor (boundaryTokens offset) 4) [firstEvent] := by
  refine ⟨?_, .cons (.hyphen (by change '-' ∈ "a-b".toList; decide)) .nil⟩
  apply PragmaDeclOrdinaryParses.parsed
    (afterKeyword := atCursor (boundaryTokens offset) 1)
    (afterName := atCursor (boundaryTokens offset) 2)
    (afterItems := atCursor (boundaryTokens offset) 3) (byteSpan 0 6) (byteSpan 12 13)
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, boundaryTokens, pragmaToken]
  · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, boundaryTokens, identifierToken]
  · apply PragmaItemsOrdinaryParses.nonempty (afterFirst := atCursor (boundaryTokens offset) 3)
    · simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, boundaryTokens, identifierToken]
    · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, boundaryTokens, identifierToken]
    · apply PragmaItemsTailOrdinaryParses.done
      simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, boundaryTokens, semicolonToken]
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, boundaryTokens, semicolonToken]

private theorem secondKeyword (offset : Nat) :
    ExactTokenParses (.keyword .pragmaKw) (atCursor (boundaryTokens offset) 4)
      (pragmaToken offset).span (atCursor (boundaryTokens offset) 5) := by
  simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, boundaryTokens, pragmaToken]

private theorem secondRejected (offset : Nat) :
    PragmaDeclTraceRejects exampleSource (offset + 13) (atCursor (boundaryTokens offset) 4)
      (atCursor (boundaryTokens offset) 8) (eofUnexpected (offset + 13) .identifier)
      [secondEvent offset] := by
  apply PragmaDeclTraceRejects.itemsRejected
    (afterKeyword := atCursor (boundaryTokens offset) 5)
    (afterName := atCursor (boundaryTokens offset) 6)
    (name := { span := byteSpan (offset + 7) (offset + 8), value := "q" })
    (pragmaToken offset).span
  · exact secondKeyword offset
  · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, boundaryTokens, identifierToken]
  · refine ⟨[failedItem offset], ?_,
      .cons (.hyphen (by change '-' ∈ "c-d".toList; decide)) .nil, ?_⟩
    · apply PragmaItemsRejectedPrefix.tailRejected
        (afterFirst := atCursor (boundaryTokens offset) 7)
      · simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, boundaryTokens, identifierToken]
      · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor,
          boundaryTokens, failedItem, identifierToken]
      · apply PragmaItemsTailRejectedPrefix.identifierRejected
          (afterComma := atCursor (boundaryTokens offset) 8)
          (byteSpan (offset + 12) (offset + 13))
        · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor,
            boundaryTokens, commaToken, Nat.add_assoc]
        · simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, boundaryTokens]
        · apply IdentifierRejects.absent
          simp [IdentifierAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, boundaryTokens]
    · apply RejectAtReports.reported
      exact .windowEnd (by simp [sourceFileRootRemainder, atCursor, boundaryTokens])

/-- The failed declaration emits its checked-name event, but yields no AST;
its cursor is rewound to token four while the exact EOF report stays separate. -/
theorem boundaryParsed (offset : Nat) :
    PragmaPrefixBoundaryTraceParses exampleSource (offset + 13)
      (sourceFileRootRemainder (boundaryTokens offset)) [keptDeclaration]
      (atCursor (boundaryTokens offset) 4) (eofUnexpected (offset + 13) .identifier)
      [firstEvent, secondEvent offset] :=
  .cons (firstParsed offset)
    (.stopped (pragmaToken offset).span (secondKeyword offset) (secondRejected offset))

theorem boundaryClears (offset : Nat) : NestingClears (boundaryTokens offset) :=
  .preserve rfl (.preserve rfl (.preserve rfl (.reset rfl
    (.preserve rfl (.preserve rfl (.preserve rfl (.reset rfl .done)))))))

def lexicalBetween : LexicalDiagnostic := {
  span := byteSpan 14 16, kind := .invalidToken
}

set_option maxRecDepth 8192 in
theorem cleanBoundaryLexes : Lexer.lex (exampleFile "pragma p a-b; pragma q c-d,") =
    .ok (lexicalCarrier (boundaryTokens 14) []) := by
  apply lex_ok_of_toOption
  decide +kernel

set_option maxRecDepth 8192 in
theorem sameLineBoundaryLexes : Lexer.lex (exampleFile "pragma p a-b; § pragma q c-d,") =
    .ok (lexicalCarrier (boundaryTokens 17) [lexicalBetween]) := by
  apply lex_ok_of_toOption
  decide +kernel

end Solcore.Test.SyntaxParserPragmaPrefixBoundaryFixtures
