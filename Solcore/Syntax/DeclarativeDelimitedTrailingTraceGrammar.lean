import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar
import Solcore.Syntax.Parser.Diagnostic

/-! Independent trailing-enabled delimited traces. Commas precede closing guards;
after a comma the closing symbol is preferred over another child.
Child carrier/window preservation is not built into the grammar. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive TrailingDelimitedTailTraceParses {α : Type} (closing : Symbol)
    (elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → List α → SourceSpan → Remainder → List ParseDiagnostic → Prop where
  | close {input output : Remainder} {closingSpan : SourceSpan}
      (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .comma))
      (closingToken : ExactTokenParses (.symbol closing) input closingSpan output) :
      TrailingDelimitedTailTraceParses closing elementTrace source endByte
        input [] closingSpan output []
  | trailing {input afterComma output : Remainder} {closingSpan : SourceSpan}
      (commaSpan : SourceSpan)
      (commaToken : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (closingToken : ExactTokenParses (.symbol closing) afterComma closingSpan output) :
      TrailingDelimitedTailTraceParses closing elementTrace source endByte
        input [] closingSpan output []
  | next {input afterComma afterElement output : Remainder}
      {value : α} {elements : List α} {closingSpan : SourceSpan}
      {elementEvents tailEvents : List ParseDiagnostic} (commaSpan : SourceSpan)
      (commaToken : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex afterComma.cursor (.symbol closing))
      (elementParsed : elementTrace source endByte afterComma value afterElement elementEvents)
      (progress : afterComma.cursor < afterElement.cursor)
      (tail : TrailingDelimitedTailTraceParses closing elementTrace source endByte
        afterElement elements closingSpan output tailEvents) :
      TrailingDelimitedTailTraceParses closing elementTrace source endByte
        input (value :: elements) closingSpan output (elementEvents ++ tailEvents)

inductive TrailingDelimitedListTraceParses {α : Type} (opening closing : Symbol)
    (allowEmpty : Bool)
    (elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → DelimitedList α → Remainder → List ParseDiagnostic → Prop where
  | empty {input afterOpening output : Remainder} (openingSpan closingSpan : SourceSpan)
      (allowed : allowEmpty = true)
      (openingToken : ExactTokenParses (.symbol opening) input openingSpan afterOpening)
      (closingToken : ExactTokenParses (.symbol closing) afterOpening closingSpan output) :
      TrailingDelimitedListTraceParses opening closing allowEmpty elementTrace source endByte input
        { span := SourceSpan.cover openingSpan closingSpan, elements := [] } output []
  | nonempty {input afterOpening afterFirst output : Remainder}
      {first : α} {rest : List α} {firstEvents tailEvents : List ParseDiagnostic}
      (openingSpan closingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol opening) input openingSpan afterOpening)
      (continues : PreferredCloseNotTaken closing allowEmpty afterOpening)
      (firstParsed : elementTrace source endByte afterOpening first afterFirst firstEvents)
      (progress : afterOpening.cursor < afterFirst.cursor)
      (tail : TrailingDelimitedTailTraceParses closing elementTrace source endByte
        afterFirst rest closingSpan output tailEvents) :
      TrailingDelimitedListTraceParses opening closing allowEmpty elementTrace source endByte input
        { span := SourceSpan.cover openingSpan closingSpan, elements := first :: rest }
        output (firstEvents ++ tailEvents)

end Solcore.Syntax.DeclarativeGrammar
