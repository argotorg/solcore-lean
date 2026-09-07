import Solcore.Syntax.DeclarativeParenthesizedTraceGrammar
import Solcore.Syntax.DeclarativeCoreParenthesizedOutcomeGrammar
import Solcore.Syntax.DeclarativeRejectionDiagnosticGrammar

/-! Raw tuple-tail and parenthesized rejection traces. Marker failures are
included even outside dispatcher-selected entry points. The final report is
not an event. Recursive tails require a selected comma explicitly. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ParenthesizedTupleTailTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | commaMissing {input : Remainder} {report : ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .comma))
      (reported : RejectAtReports source endByte { head := .symbol .comma, tail := [] } .expression input report) :
      ParenthesizedTupleTailTraceRejects elementTrace elementRejects source endByte input input report []
  | elementRejected {input afterComma rejected : Remainder} {report : ParseDiagnostic}
      {events : List ParseDiagnostic} (commaSpan : SourceSpan)
      (comma : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (child : elementRejects source endByte afterComma rejected report events) :
      ParenthesizedTupleTailTraceRejects elementTrace elementRejects source endByte input rejected report events
  | closingMissing {input afterComma afterElement : Remainder} {element : Syntax.Expr}
      {events : List ParseDiagnostic} {report : ParseDiagnostic} (commaSpan : SourceSpan)
      (comma : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (child : elementTrace source endByte afterComma element afterElement events)
      (progress : afterComma.cursor < afterElement.cursor)
      (commaAbsent : TokenKindAbsentAt afterElement.tokens afterElement.endIndex afterElement.cursor (.symbol .comma))
      (lastClosingAbsent : TokenKindAbsentAt afterElement.tokens afterElement.endIndex afterElement.cursor (.symbol .rightParen))
      (reported : RejectAtReports source endByte { head := .symbol .rightParen, tail := [] } .expression afterElement report) :
      ParenthesizedTupleTailTraceRejects elementTrace elementRejects source endByte input afterElement report events
  | laterRejected {input afterComma afterElement rejected : Remainder} {element : Syntax.Expr}
      {headEvents tailEvents : List ParseDiagnostic} {report : ParseDiagnostic} (commaSpan nextCommaSpan : SourceSpan)
      (comma : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (child : elementTrace source endByte afterComma element afterElement headEvents)
      (progress : afterComma.cursor < afterElement.cursor)
      (nextComma : TokenAt afterElement.tokens afterElement.endIndex afterElement.cursor
        { span := nextCommaSpan, value := .symbol .comma })
      (tail : ParenthesizedTupleTailTraceRejects elementTrace elementRejects source endByte
        afterElement rejected report tailEvents) :
      ParenthesizedTupleTailTraceRejects elementTrace elementRejects source endByte input rejected report
        (headEvents ++ tailEvents)

inductive ParenthesizedExpressionTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | openingMissing {input : Remainder} {report : ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftParen))
      (reported : RejectAtReports source endByte { head := .symbol .leftParen, tail := [] } .expression input report) :
      ParenthesizedExpressionTraceRejects elementTrace elementRejects source endByte input input report []
  | firstRejected {input afterOpening rejected : Remainder} {report : ParseDiagnostic}
      {events : List ParseDiagnostic} (openingSpan : SourceSpan)
      (opening : ExactTokenParses (.symbol .leftParen) input openingSpan afterOpening)
      (closingAbsent : TokenKindAbsentAt afterOpening.tokens afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (child : elementRejects source endByte afterOpening rejected report events) :
      ParenthesizedExpressionTraceRejects elementTrace elementRejects source endByte input rejected report events
  | closingMissing {input afterOpening afterElement : Remainder} {element : Syntax.Expr}
      {events : List ParseDiagnostic} {report : ParseDiagnostic} (openingSpan : SourceSpan)
      (opening : ExactTokenParses (.symbol .leftParen) input openingSpan afterOpening)
      (closingAbsent : TokenKindAbsentAt afterOpening.tokens afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (child : elementTrace source endByte afterOpening element afterElement events)
      (progress : afterOpening.cursor < afterElement.cursor)
      (commaAbsent : TokenKindAbsentAt afterElement.tokens afterElement.endIndex afterElement.cursor (.symbol .comma))
      (lastClosingAbsent : TokenKindAbsentAt afterElement.tokens afterElement.endIndex afterElement.cursor (.symbol .rightParen))
      (reported : RejectAtReports source endByte { head := .symbol .rightParen, tail := [] } .expression afterElement report) :
      ParenthesizedExpressionTraceRejects elementTrace elementRejects source endByte input afterElement report events
  | tailRejected {input afterOpening afterFirst rejected : Remainder} {first : Syntax.Expr}
      {headEvents tailEvents : List ParseDiagnostic} {report : ParseDiagnostic} (openingSpan commaSpan : SourceSpan)
      (opening : ExactTokenParses (.symbol .leftParen) input openingSpan afterOpening)
      (closingAbsent : TokenKindAbsentAt afterOpening.tokens afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (child : elementTrace source endByte afterOpening first afterFirst headEvents)
      (progress : afterOpening.cursor < afterFirst.cursor)
      (comma : TokenAt afterFirst.tokens afterFirst.endIndex afterFirst.cursor
        { span := commaSpan, value := .symbol .comma })
      (tail : ParenthesizedTupleTailTraceRejects elementTrace elementRejects source endByte
        afterFirst rejected report tailEvents) :
      ParenthesizedExpressionTraceRejects elementTrace elementRejects source endByte input rejected report
        (headEvents ++ tailEvents)

end Solcore.Syntax.DeclarativeGrammar
