import Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceGrammar
import Solcore.Syntax.DeclarativeParseDiagnosticCascadeProperties

/-! Trailing-enabled lists add no delimiter events. Protected child events retain
their complete order and multiplicity, including on rejection. The separate
uncommitted rejection report is not asserted to be protected. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {α : Type} {opening closing : Symbol} {allowEmpty : Bool} {context : ParseContext}
  {elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}

theorem TrailingDelimitedTailTraceRejects.cascadeFilters
    (successProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected diagnostic trace},
      elementRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TrailingDelimitedTailTraceRejects closing context elementTrace elementRejects
      source endByte input rejected diagnostic trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  induction rejection with
  | delimiterMissing => exact .nil
  | elementRejected _ _ _ child => exact rejectProtected child
  | laterRejected _ _ _ child _ _ ih => exact (successProtected child).append ih

theorem TrailingDelimitedListTraceRejects.cascadeFilters
    (successProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected diagnostic trace},
      elementRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TrailingDelimitedListTraceRejects opening closing allowEmpty context
      elementTrace elementRejects source endByte input rejected diagnostic trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | openingMissing => exact .nil
  | firstRejected _ _ _ child => exact rejectProtected child
  | tailRejected _ _ _ child _ tail =>
      exact (successProtected child).append (tail.cascadeFilters successProtected rejectProtected)

end Solcore.Syntax.DeclarativeGrammar
