import Solcore.Syntax.DeclarativeCoreBlockTraceGrammar
import Solcore.Syntax.DeclarativeRejectionDiagnosticGrammar

/-! Independent ordinary rejection traces of raw Core blocks. A missing
closing brace or rejected statement returns before tail validation. Only
statement events already emitted precede the separate uncommitted report. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact first rejecting item stage, with the closing-brace branch preferred.
The source and byte endpoint stay fixed throughout the abstract statement chain. -/
inductive CoreBlockItemsTraceRejects
    (statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
      Remainder → List ParseDiagnostic → Prop)
    (statementRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | missingClose {input : Remainder} {diagnostic : ParseDiagnostic}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (atEnd : input.endIndex ≤ input.cursor)
      (reported : RejectAtReports source endByte
        { head := .symbol .rightBrace, tail := [] } .statement input diagnostic) :
      CoreBlockItemsTraceRejects statementTrace statementRejects source endByte
        input input diagnostic []
  | statementRejected {input rejected : Remainder}
      {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
      (notAtEnd : input.cursor < input.endIndex)
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (statementRejected : statementRejects source endByte input rejected diagnostic trace) :
      CoreBlockItemsTraceRejects statementTrace statementRejects source endByte
        input rejected diagnostic trace
  | laterRejected {input afterStatement rejected : Remainder}
      {statement : Syntax.Statement} {diagnostic : ParseDiagnostic}
      {statementEvents tailEvents : List ParseDiagnostic}
      (notAtEnd : input.cursor < input.endIndex)
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (statementParsed : statementTrace source endByte input statement afterStatement statementEvents)
      (progress : input.cursor < afterStatement.cursor)
      (tailRejected : CoreBlockItemsTraceRejects statementTrace statementRejects source endByte
        afterStatement rejected diagnostic tailEvents) :
      CoreBlockItemsTraceRejects statementTrace statementRejects source endByte
        input rejected diagnostic (statementEvents ++ tailEvents)

/-- A missing opening brace emits no prior event. After an exact opening,
only the item-rejection trace survives; no block-tail check has run. -/
inductive CoreBlockTraceRejects
    (statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
      Remainder → List ParseDiagnostic → Prop)
    (statementRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (policy : CoreBlockTailPolicy) (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | openingMissing {input : Remainder} {diagnostic : ParseDiagnostic}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftBrace))
      (reported : RejectAtReports source endByte
        { head := .symbol .leftBrace, tail := [] } .statement input diagnostic) :
      CoreBlockTraceRejects statementTrace statementRejects policy source endByte
        input input diagnostic []
  | itemsRejected {input afterOpening rejected : Remainder}
      {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
      (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftBrace) input openingSpan afterOpening)
      (itemsRejected : CoreBlockItemsTraceRejects statementTrace statementRejects source endByte
        afterOpening rejected diagnostic trace) :
      CoreBlockTraceRejects statementTrace statementRejects policy source endByte
        input rejected diagnostic trace

end Solcore.Syntax.DeclarativeGrammar
