import Solcore.Syntax.DeclarativePostfixTailTraceGrammar
import Solcore.Syntax.DeclarativeDelimitedNoTrailingRejectionTraceGrammar
import Solcore.Syntax.DeclarativeCoreTypeOutcomeGrammar

/-! Independent exact postfix rejections. Selected opening markers cannot
fail; failures occur in the nested index, its closing bracket, call arguments,
the checked field identifier, or a later suffix. Earlier emitted events remain
ordered, and the terminal report is never appended as an emitted event. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive PostfixTailTraceRejects
    (nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | indexNestedRejected {input afterOpening rejected : Remainder}
      {base : Syntax.Expr} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (openingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBracket) input openingSpan afterOpening)
      (nestedRejected : nestedRejects source endByte afterOpening rejected report trace) :
      PostfixTailTraceRejects nestedTrace nestedRejects source endByte input base rejected report trace
  | indexClosingMissing {input afterOpening afterIndex : Remainder}
      {base index : Syntax.Expr} {report : ParseDiagnostic} {indexEvents : List ParseDiagnostic}
      (openingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBracket) input openingSpan afterOpening)
      (indexParsed : nestedTrace source endByte afterOpening index afterIndex indexEvents)
      (closingAbsent : TokenKindAbsentAt afterIndex.tokens afterIndex.endIndex afterIndex.cursor (.symbol .rightBracket))
      (reported : RejectAtReports source endByte { head := .symbol .rightBracket, tail := [] }
        .expression afterIndex report) :
      PostfixTailTraceRejects nestedTrace nestedRejects source endByte input base afterIndex report indexEvents
  | indexLaterRejected {input afterOpening afterIndex afterClosing rejected : Remainder}
      {base index : Syntax.Expr} {report : ParseDiagnostic}
      {indexEvents tailEvents : List ParseDiagnostic} (openingSpan closingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBracket) input openingSpan afterOpening)
      (indexParsed : nestedTrace source endByte afterOpening index afterIndex indexEvents)
      (closingToken : ExactTokenParses (.symbol .rightBracket) afterIndex closingSpan afterClosing)
      (tailRejected : PostfixTailTraceRejects nestedTrace nestedRejects source endByte afterClosing
        (postfixIndexTraceValue base index openingSpan closingSpan) rejected report tailEvents) :
      PostfixTailTraceRejects nestedTrace nestedRejects source endByte input base rejected report (indexEvents ++ tailEvents)
  | callArgumentsRejected {input rejected : Remainder}
      {base : Syntax.Expr} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (openingSpan : SourceSpan)
      (indexAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftBracket))
      (openingToken : TokenAt input.tokens input.endIndex input.cursor { span := openingSpan, value := .symbol .leftParen })
      (argumentsRejected : NoTrailingDelimitedListTraceRejects .leftParen .rightParen true .expression
        nestedTrace nestedRejects source endByte input rejected report trace) :
      PostfixTailTraceRejects nestedTrace nestedRejects source endByte input base rejected report trace
  | callLaterRejected {input afterArguments rejected : Remainder}
      {base : Syntax.Expr} {arguments : DelimitedList Syntax.Expr} {report : ParseDiagnostic}
      {argumentEvents tailEvents : List ParseDiagnostic}
      (indexAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftBracket))
      (argumentsParsed : NoTrailingDelimitedListTraceParses .leftParen .rightParen true
        nestedTrace source endByte input arguments afterArguments argumentEvents)
      (tailRejected : PostfixTailTraceRejects nestedTrace nestedRejects source endByte afterArguments
        (postfixCallTraceValue base arguments) rejected report tailEvents) :
      PostfixTailTraceRejects nestedTrace nestedRejects source endByte input base rejected report (argumentEvents ++ tailEvents)
  | fieldNameRejected {input afterDot : Remainder}
      {base : Syntax.Expr} {report : ParseDiagnostic} (dotSpan : SourceSpan)
      (indexAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftBracket))
      (callAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftParen))
      (dotToken : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameAbsent : IdentifierAbsentAt afterDot)
      (reported : RejectAtReports source endByte { head := .identifier, tail := [] }
        .expression afterDot report) :
      PostfixTailTraceRejects nestedTrace nestedRejects source endByte input base afterDot report []
  | fieldLaterRejected {input afterDot afterName rejected : Remainder}
      {base : Syntax.Expr} {name : Syntax.Identifier} {report : ParseDiagnostic}
      {nameEvents tailEvents : List ParseDiagnostic} (dotSpan : SourceSpan)
      (indexAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftBracket))
      (callAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftParen))
      (dotToken : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameParsed : IdentifierTraceParses afterDot name afterName nameEvents)
      (tailRejected : PostfixTailTraceRejects nestedTrace nestedRejects source endByte afterName
        (postfixFieldTraceValue base dotSpan name) rejected report tailEvents) :
      PostfixTailTraceRejects nestedTrace nestedRejects source endByte input base rejected report (nameEvents ++ tailEvents)

end Solcore.Syntax.DeclarativeGrammar
