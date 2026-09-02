import Solcore.Syntax.DeclarativeExportNameOutcomeGrammar
import Solcore.Syntax.DeclarativeExportPathOutcomeGrammar

/-! Parser-independent broad ordinary outcomes for local export items. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact positive guard for the prioritized qualified-wildcard branch. -/
def LocalExportItemQualifiedStartAt (input : Remainder) : Prop :=
  ∃ identifierSpan dotSpan text,
    TokenAt input.tokens input.endIndex input.cursor {
      span := identifierSpan
      value := .identifier text
    } ∧
    TokenAt input.tokens input.endIndex (input.cursor + 1) {
      span := dotSpan
      value := .symbol .dot
    }

/-- Ordinary local-export-item success is the existing prioritized grammar. -/
abbrev LocalExportItemOrdinaryParses := LocalExportItemParses

/-- Exact reachable rejection stages of one local export item. -/
inductive LocalExportItemRejects : Remainder → Remainder → Prop where
  | moduleDotMissing {input afterPath : Remainder}
      {path : Syntax.QualifiedName}
      (qualifiedStart : LocalExportItemQualifiedStartAt input)
      (pathParsed : ExportPathOrdinaryParses input path afterPath)
      (dotAbsent : TokenKindAbsentAt afterPath.tokens afterPath.endIndex
        afterPath.cursor (.symbol .dot)) :
      LocalExportItemRejects input afterPath
  | moduleStarMissing {input afterPath afterDot : Remainder}
      {path : Syntax.QualifiedName}
      (qualifiedStart : LocalExportItemQualifiedStartAt input)
      (pathParsed : ExportPathOrdinaryParses input path afterPath)
      (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) afterPath dotSpan afterDot)
      (starAbsent : TokenKindAbsentAt afterDot.tokens afterDot.endIndex
        afterDot.cursor (.symbol .star)) :
      LocalExportItemRejects input afterDot
  | nameRejected {input rejected : Remainder}
      (qualifiedAbsent : IdentifierDotAbsentAt input.tokens input.endIndex
        input.cursor)
      (nameRejected : ExportNameRejects input rejected) :
      LocalExportItemRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
