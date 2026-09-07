import Solcore.Syntax.DeclarativeDelimitedTrailingTraceGrammar
import Solcore.Syntax.DeclarativeParseDiagnosticCascadeProperties

/-! Trailing-enabled lists add no delimiter events. Protected child events retain
their complete order and multiplicity through either silent closing branch. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {α : Type} {opening closing : Symbol} {allowEmpty : Bool}
  {elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}

theorem TrailingDelimitedTailTraceParses.cascadeFilters
    (elementProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {values : List α} {closingSpan : SourceSpan}
    {trace : List ParseDiagnostic}
    (parsed : TrailingDelimitedTailTraceParses closing elementTrace source endByte
      input values closingSpan output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  induction parsed with
  | close | trailing => exact .nil
  | next _ _ _ element _ _ ih => exact (elementProtected element).append ih

theorem TrailingDelimitedListTraceParses.cascadeFilters
    (elementProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {values : DelimitedList α} {trace : List ParseDiagnostic}
    (parsed : TrailingDelimitedListTraceParses opening closing allowEmpty elementTrace source endByte
      input values output trace) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | empty => exact .nil
  | nonempty _ _ _ _ first _ tail =>
      exact (elementProtected first).append (tail.cascadeFilters elementProtected)

end Solcore.Syntax.DeclarativeGrammar
