import Solcore.Syntax.DeclarativeDelimitedTrailingTraceGrammar
import Solcore.Syntax.DeclarativeRejectionDiagnosticGrammar

/-! Independent trailing-enabled list rejection traces. Commas have priority over
closing delimiters, even when those symbols coincide. After a comma an immediate
closing delimiter bypasses the child; rejection requires its absence. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive TrailingDelimitedTailTraceRejects {α : Type}
    (closing : Symbol) (context : ParseContext)
    (elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | delimiterMissing {input : Remainder} {diagnostic : ParseDiagnostic}
      (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .comma))
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol closing))
      (reported : RejectAtReports source endByte
        { head := .symbol .comma, tail := [.symbol closing] } context input diagnostic) :
      TrailingDelimitedTailTraceRejects closing context elementTrace elementRejects source endByte
        input input diagnostic []
  | elementRejected {input afterComma rejected : Remainder}
      {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex
        afterComma.cursor (.symbol closing))
      (childRejected : elementRejects source endByte afterComma rejected diagnostic trace) :
      TrailingDelimitedTailTraceRejects closing context elementTrace elementRejects source endByte
        input rejected diagnostic trace
  | laterRejected {input afterComma afterElement rejected : Remainder} {value : α}
      {diagnostic : ParseDiagnostic} {childEvents tailEvents : List ParseDiagnostic} (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex
        afterComma.cursor (.symbol closing))
      (childParsed : elementTrace source endByte afterComma value afterElement childEvents)
      (progress : afterComma.cursor < afterElement.cursor)
      (tailRejected : TrailingDelimitedTailTraceRejects closing context elementTrace elementRejects
        source endByte afterElement rejected diagnostic tailEvents) :
      TrailingDelimitedTailTraceRejects closing context elementTrace elementRejects source endByte
        input rejected diagnostic (childEvents ++ tailEvents)

inductive TrailingDelimitedListTraceRejects {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext)
    (elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | openingMissing {input : Remainder} {diagnostic : ParseDiagnostic}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol opening))
      (reported : RejectAtReports source endByte { head := .symbol opening, tail := [] }
        context input diagnostic) :
      TrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace elementRejects
        source endByte input input diagnostic []
  | firstRejected {input afterOpening rejected : Remainder}
      {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol opening) input openingSpan afterOpening)
      (continues : PreferredCloseNotTaken closing allowEmpty afterOpening)
      (childRejected : elementRejects source endByte afterOpening rejected diagnostic trace) :
      TrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace elementRejects
        source endByte input rejected diagnostic trace
  | tailRejected {input afterOpening afterFirst rejected : Remainder} {value : α}
      {diagnostic : ParseDiagnostic} {childEvents tailEvents : List ParseDiagnostic} (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol opening) input openingSpan afterOpening)
      (continues : PreferredCloseNotTaken closing allowEmpty afterOpening)
      (childParsed : elementTrace source endByte afterOpening value afterFirst childEvents)
      (progress : afterOpening.cursor < afterFirst.cursor)
      (tailRejected : TrailingDelimitedTailTraceRejects closing context elementTrace elementRejects
        source endByte afterFirst rejected diagnostic tailEvents) :
      TrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace elementRejects
        source endByte input rejected diagnostic (childEvents ++ tailEvents)

end Solcore.Syntax.DeclarativeGrammar
