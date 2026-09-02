import Solcore.Syntax.DeclarativeCoreIdentifierOutcomeGrammar
import Solcore.Syntax.DeclarativeExportPathOutcomeGrammar
import Solcore.Syntax.DeclarativeExportSelectionOutcomeGrammar
import Solcore.Syntax.DeclarativeFinishExportOutcomeGrammar

/-! Parser-independent broad ordinary outcomes for path export payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact positive current-token guard for path-export suffix dispatch. -/
def PathExportTokenPresentAt (input : Remainder) (kind : TokenKind) : Prop :=
  ∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := kind
  }

/-- Ordinary path-export success is the existing exact prioritized grammar. -/
abbrev PathExportOrdinaryParses (start : SourceSpan) :=
  PathExportTailParses start

/-- Exact first rejecting stage of a prioritized path export payload. -/
inductive PathExportRejects : Remainder → Remainder → Prop where
  | pathRejected {input rejected : Remainder}
      (pathRejected : ExportPathRejects input rejected) :
      PathExportRejects input rejected
  | selectionRejected
      {input afterPath afterDot rejected : Remainder}
      {path : Syntax.QualifiedName} (dotSpan : SourceSpan)
      (pathParsed : ExportPathOrdinaryParses input path afterPath)
      (dotPresent : PathExportTokenPresentAt afterPath (.symbol .dot))
      (dotParsed : ExactTokenParses (.symbol .dot) afterPath dotSpan afterDot)
      (selectionRejected : ExportSelectionRejects afterDot rejected) :
      PathExportRejects input rejected
  | selectionFinishRejected
      {input afterPath afterDot afterSelection rejected : Remainder}
      {path : Syntax.QualifiedName} {selection : Syntax.ExportSelection}
      (dotSpan : SourceSpan)
      (pathParsed : ExportPathOrdinaryParses input path afterPath)
      (dotPresent : PathExportTokenPresentAt afterPath (.symbol .dot))
      (dotParsed : ExactTokenParses (.symbol .dot) afterPath dotSpan afterDot)
      (selectionParsed : ExportSelectionOrdinaryParses afterDot selection
        afterSelection)
      (finishRejected : FinishExportRejects afterSelection rejected) :
      PathExportRejects input rejected
  | aliasRejected {input afterPath afterAs rejected : Remainder}
      {path : Syntax.QualifiedName} (asSpan : SourceSpan)
      (pathParsed : ExportPathOrdinaryParses input path afterPath)
      (dotAbsent : TokenKindAbsentAt afterPath.tokens afterPath.endIndex
        afterPath.cursor (.symbol .dot))
      (asPresent : PathExportTokenPresentAt afterPath (.keyword .asKw))
      (asParsed : ExactTokenParses (.keyword .asKw) afterPath asSpan afterAs)
      (aliasRejected : IdentifierRejects afterAs rejected) :
      PathExportRejects input rejected
  | aliasFinishRejected
      {input afterPath afterAs afterAlias rejected : Remainder}
      {path : Syntax.QualifiedName} {alias : Syntax.Identifier}
      (asSpan : SourceSpan)
      (pathParsed : ExportPathOrdinaryParses input path afterPath)
      (dotAbsent : TokenKindAbsentAt afterPath.tokens afterPath.endIndex
        afterPath.cursor (.symbol .dot))
      (asPresent : PathExportTokenPresentAt afterPath (.keyword .asKw))
      (asParsed : ExactTokenParses (.keyword .asKw) afterPath asSpan afterAs)
      (aliasParsed : IdentifierParses afterAs alias afterAlias)
      (finishRejected : FinishExportRejects afterAlias rejected) :
      PathExportRejects input rejected
  | moduleFinishRejected {input afterPath rejected : Remainder}
      {path : Syntax.QualifiedName}
      (pathParsed : ExportPathOrdinaryParses input path afterPath)
      (dotAbsent : TokenKindAbsentAt afterPath.tokens afterPath.endIndex
        afterPath.cursor (.symbol .dot))
      (asAbsent : TokenKindAbsentAt afterPath.tokens afterPath.endIndex
        afterPath.cursor (.keyword .asKw))
      (finishRejected : FinishExportRejects afterPath rejected) :
      PathExportRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
