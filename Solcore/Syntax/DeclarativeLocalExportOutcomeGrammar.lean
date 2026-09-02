import Solcore.Syntax.DeclarativeFinishExportOutcomeGrammar
import Solcore.Syntax.DeclarativeLocalExportItemOutcomeGrammar

/-! Parser-independent broad ordinary outcomes for local export payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary local-export success is the existing exact list-and-finish
grammar for a fixed outer start span. -/
abbrev LocalExportOrdinaryParses (start : SourceSpan) :=
  LocalExportTailParses start

/-- Exact first rejecting stage of a local export payload. -/
inductive LocalExportRejects : Remainder → Remainder → Prop where
  | itemsRejected {input rejected : Remainder}
      (itemsRejected : DelimitedListRejects .leftBrace .rightBrace true true
        LocalExportItemOrdinaryParses LocalExportItemRejects input rejected) :
      LocalExportRejects input rejected
  | finishRejected {input afterItems rejected : Remainder}
      {items : DelimitedList Syntax.LocalExportItem}
      (itemsParsed : TrailingDelimitedListParses .leftBrace .rightBrace
        LocalExportItemOrdinaryParses input items afterItems)
      (finishRejected : FinishExportRejects afterItems rejected) :
      LocalExportRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
