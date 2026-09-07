import Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceGrammar

/-! Child-relation implication lifts through trailing-enabled lists without
changing a value, source coordinate, remainder, report, or diagnostic event.
Every existing delimiter guard and progress witness is retained unchanged. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {α : Type} {opening closing : Symbol} {allowEmpty : Bool} {context : ParseContext}
  {source : SourceId} {endByte : Nat}
  {elementTrace otherTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
  {elementRejects otherRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic →
    List ParseDiagnostic → Prop}

theorem TrailingDelimitedTailTraceParses.mono
    (childMap : ∀ {input value output trace},
      elementTrace source endByte input value output trace → otherTrace source endByte input value output trace)
    {input output : Remainder} {values : List α} {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : TrailingDelimitedTailTraceParses closing elementTrace source endByte
      input values closingSpan output trace) :
    TrailingDelimitedTailTraceParses closing otherTrace source endByte input values closingSpan output trace := by
  induction parsed with
  | close absent closing => exact .close absent closing
  | trailing span comma closing => exact .trailing span comma closing
  | next span comma absent child progress tail ih =>
      exact .next span comma absent (childMap child) progress ih

theorem TrailingDelimitedListTraceParses.mono
    (childMap : ∀ {input value output trace},
      elementTrace source endByte input value output trace → otherTrace source endByte input value output trace)
    {input output : Remainder} {values : DelimitedList α} {trace : List ParseDiagnostic}
    (parsed : TrailingDelimitedListTraceParses opening closing allowEmpty elementTrace source endByte
      input values output trace) :
    TrailingDelimitedListTraceParses opening closing allowEmpty otherTrace source endByte input values output trace := by
  cases parsed with
  | empty openingSpan closingSpan allowed opening closing =>
      exact .empty openingSpan closingSpan allowed opening closing
  | nonempty openingSpan closingSpan opening continues first progress tail =>
      exact .nonempty openingSpan closingSpan opening continues (childMap first) progress (tail.mono childMap)

theorem TrailingDelimitedTailTraceRejects.mono
    (successMap : ∀ {input value output trace},
      elementTrace source endByte input value output trace → otherTrace source endByte input value output trace)
    (rejectMap : ∀ {input rejected report trace},
      elementRejects source endByte input rejected report trace → otherRejects source endByte input rejected report trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TrailingDelimitedTailTraceRejects closing context elementTrace elementRejects source endByte
      input rejected report trace) :
    TrailingDelimitedTailTraceRejects closing context otherTrace otherRejects source endByte
      input rejected report trace := by
  induction rejection with
  | delimiterMissing commaAbsent closingAbsent reported => exact .delimiterMissing commaAbsent closingAbsent reported
  | elementRejected span comma absent child => exact .elementRejected span comma absent (rejectMap child)
  | laterRejected span comma absent child progress tail ih =>
      exact .laterRejected span comma absent (successMap child) progress ih

theorem TrailingDelimitedListTraceRejects.mono
    (successMap : ∀ {input value output trace},
      elementTrace source endByte input value output trace → otherTrace source endByte input value output trace)
    (rejectMap : ∀ {input rejected report trace},
      elementRejects source endByte input rejected report trace → otherRejects source endByte input rejected report trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace elementRejects
      source endByte input rejected report trace) :
    TrailingDelimitedListTraceRejects opening closing allowEmpty context otherTrace otherRejects
      source endByte input rejected report trace := by
  cases rejection with
  | openingMissing absent reported => exact .openingMissing absent reported
  | firstRejected span opening continues child => exact .firstRejected span opening continues (rejectMap child)
  | tailRejected span opening continues child progress tail =>
      exact .tailRejected span opening continues (successMap child) progress (tail.mono successMap rejectMap)

end Solcore.Syntax.DeclarativeGrammar
