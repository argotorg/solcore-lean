import Solcore.Syntax.DeclarativeDelimitedNoTrailingRejectionTraceGrammar
import Solcore.Syntax.DeclarativeParseDiagnosticCascadeProperties

/-! No-trailing lists add no delimiter events. Protected child events retain
their complete order and multiplicity, including on rejection. The separate
uncommitted rejection report is not asserted to be protected. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {α : Type} {opening closing : Symbol} {allowEmpty : Bool} {context : ParseContext}
  {elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}

theorem NoTrailingDelimitedTailTraceParses.cascadeFilters
    (elementProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {values : List α} {closingSpan : SourceSpan}
    {trace : List ParseDiagnostic}
    (parsed : NoTrailingDelimitedTailTraceParses closing elementTrace source endByte
      input values closingSpan output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  induction parsed with
  | close => exact .nil
  | next _ _ element _ _ ih => exact (elementProtected element).append ih

theorem NoTrailingDelimitedListTraceParses.cascadeFilters
    (elementProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {values : DelimitedList α} {trace : List ParseDiagnostic}
    (parsed : NoTrailingDelimitedListTraceParses opening closing allowEmpty elementTrace source endByte
      input values output trace) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | empty => exact .nil
  | nonempty _ _ _ _ first _ tail =>
      exact (elementProtected first).append (tail.cascadeFilters elementProtected)

theorem NoTrailingDelimitedTailTraceRejects.cascadeFilters
    (successProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected diagnostic trace},
      elementRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NoTrailingDelimitedTailTraceRejects closing context elementTrace elementRejects
      source endByte input rejected diagnostic trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  induction rejection with
  | delimiterMissing => exact .nil
  | elementRejected _ _ child => exact rejectProtected child
  | laterRejected _ _ child _ _ ih => exact (successProtected child).append ih

theorem NoTrailingDelimitedListTraceRejects.cascadeFilters
    (successProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected diagnostic trace},
      elementRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NoTrailingDelimitedListTraceRejects opening closing allowEmpty context
      elementTrace elementRejects source endByte input rejected diagnostic trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | openingMissing => exact .nil
  | firstRejected _ _ _ child => exact rejectProtected child
  | tailRejected _ _ _ child _ tail =>
      exact (successProtected child).append (tail.cascadeFilters successProtected rejectProtected)

end Solcore.Syntax.DeclarativeGrammar
