import Solcore.Syntax.DeclarativeLocalExportOutcomeGrammar
import Solcore.Syntax.DeclarativePathExportOutcomeGrammar

/-! Parser-independent broad ordinary outcomes for complete exports. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact positive left-brace guard for the outer export dispatcher. -/
def ExportDeclLeftBracePresentAt (input : Remainder) : Prop :=
  ∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .symbol .leftBrace
  }

/-- Ordinary complete-export success is the existing exact four-form grammar. -/
abbrev ExportDeclOrdinaryParses := ExportDeclParses

/-- Exact first rejecting stage of a complete prioritized export declaration. -/
inductive ExportDeclRejects : Remainder → Remainder → Prop where
  | keywordMissing {input : Remainder}
      (keywordAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .exportKw)) :
      ExportDeclRejects input input
  | localRejected {input afterKeyword rejected : Remainder}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .exportKw) input keywordSpan
        afterKeyword)
      (leftBracePresent : ExportDeclLeftBracePresentAt afterKeyword)
      (payloadRejected : LocalExportRejects afterKeyword rejected) :
      ExportDeclRejects input rejected
  | pathRejected {input afterKeyword rejected : Remainder}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .exportKw) input keywordSpan
        afterKeyword)
      (leftBraceAbsent : TokenKindAbsentAt afterKeyword.tokens
        afterKeyword.endIndex afterKeyword.cursor (.symbol .leftBrace))
      (payloadRejected : PathExportRejects afterKeyword rejected) :
      ExportDeclRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
