import Solcore.Syntax.DeclarativeNamespaceImportOutcomeGrammar
import Solcore.Syntax.DeclarativePlainImportOutcomeGrammar
import Solcore.Syntax.DeclarativeSelectiveImportOutcomeGrammar
import Solcore.Syntax.DeclarativeWildcardImportOutcomeGrammar

/-!
Parser-independent broad ordinary outcomes for the complete prioritized import
declaration dispatcher.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact token-kind evidence used by an import-payload dispatch lookahead. -/
def ImportDispatchTokenPresentAt (input : Remainder) (offset : Nat)
    (kind : TokenKind) : Prop :=
  ∃ span, TokenAt input.tokens input.endIndex (input.cursor + offset) {
    span
    value := kind
  }

/-- Exact broad success of the complete prioritized import declaration. -/
inductive ImportDeclOrdinaryParses :
    Remainder → Syntax.ImportDecl → Remainder → Prop where
  | namespaceImport {input afterKeyword output : Remainder}
      {declaration : Syntax.ImportDecl} (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .importKw) input keywordSpan
        afterKeyword)
      (starPresent : ImportDispatchTokenPresentAt afterKeyword 0
        (.symbol .star))
      (asPresent : ImportDispatchTokenPresentAt afterKeyword 1
        (.keyword .asKw))
      (payloadParsed : NamespaceImportOrdinaryParses keywordSpan afterKeyword
        declaration output) :
      ImportDeclOrdinaryParses input declaration output
  | wildcardImport {input afterKeyword output : Remainder}
      {declaration : Syntax.ImportDecl} (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .importKw) input keywordSpan
        afterKeyword)
      (starPresent : ImportDispatchTokenPresentAt afterKeyword 0
        (.symbol .star))
      (asAbsent : TokenKindAbsentAt afterKeyword.tokens afterKeyword.endIndex
        (afterKeyword.cursor + 1) (.keyword .asKw))
      (payloadParsed : WildcardImportOrdinaryParses keywordSpan afterKeyword
        declaration output) :
      ImportDeclOrdinaryParses input declaration output
  | selectiveImport {input afterKeyword output : Remainder}
      {declaration : Syntax.ImportDecl} (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .importKw) input keywordSpan
        afterKeyword)
      (starAbsent : TokenKindAbsentAt afterKeyword.tokens afterKeyword.endIndex
        (afterKeyword.cursor + 0) (.symbol .star))
      (leftBracePresent : ImportDispatchTokenPresentAt afterKeyword 0
        (.symbol .leftBrace))
      (payloadParsed : SelectiveImportOrdinaryParses keywordSpan afterKeyword
        declaration output) :
      ImportDeclOrdinaryParses input declaration output
  | plainImport {input afterKeyword output : Remainder}
      {declaration : Syntax.ImportDecl} (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .importKw) input keywordSpan
        afterKeyword)
      (starAbsent : TokenKindAbsentAt afterKeyword.tokens afterKeyword.endIndex
        (afterKeyword.cursor + 0) (.symbol .star))
      (leftBraceAbsent : TokenKindAbsentAt afterKeyword.tokens
        afterKeyword.endIndex (afterKeyword.cursor + 0) (.symbol .leftBrace))
      (payloadParsed : PlainImportOrdinaryParses keywordSpan afterKeyword
        declaration output) :
      ImportDeclOrdinaryParses input declaration output

/-- Exact first rejecting stage of the complete prioritized import declaration. -/
inductive ImportDeclRejects : Remainder → Remainder → Prop where
  | keywordMissing {input : Remainder}
      (keywordAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .importKw)) :
      ImportDeclRejects input input
  | namespaceImportRejected {input afterKeyword rejected : Remainder}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .importKw) input keywordSpan
        afterKeyword)
      (starPresent : ImportDispatchTokenPresentAt afterKeyword 0
        (.symbol .star))
      (asPresent : ImportDispatchTokenPresentAt afterKeyword 1
        (.keyword .asKw))
      (payloadRejected : NamespaceImportRejects afterKeyword rejected) :
      ImportDeclRejects input rejected
  | wildcardImportRejected {input afterKeyword rejected : Remainder}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .importKw) input keywordSpan
        afterKeyword)
      (starPresent : ImportDispatchTokenPresentAt afterKeyword 0
        (.symbol .star))
      (asAbsent : TokenKindAbsentAt afterKeyword.tokens afterKeyword.endIndex
        (afterKeyword.cursor + 1) (.keyword .asKw))
      (payloadRejected : WildcardImportRejects afterKeyword rejected) :
      ImportDeclRejects input rejected
  | selectiveImportRejected {input afterKeyword rejected : Remainder}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .importKw) input keywordSpan
        afterKeyword)
      (starAbsent : TokenKindAbsentAt afterKeyword.tokens afterKeyword.endIndex
        (afterKeyword.cursor + 0) (.symbol .star))
      (leftBracePresent : ImportDispatchTokenPresentAt afterKeyword 0
        (.symbol .leftBrace))
      (payloadRejected : SelectiveImportRejects afterKeyword rejected) :
      ImportDeclRejects input rejected
  | plainImportRejected {input afterKeyword rejected : Remainder}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .importKw) input keywordSpan
        afterKeyword)
      (starAbsent : TokenKindAbsentAt afterKeyword.tokens afterKeyword.endIndex
        (afterKeyword.cursor + 0) (.symbol .star))
      (leftBraceAbsent : TokenKindAbsentAt afterKeyword.tokens
        afterKeyword.endIndex (afterKeyword.cursor + 0) (.symbol .leftBrace))
      (payloadRejected : PlainImportRejects afterKeyword rejected) :
      ImportDeclRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
