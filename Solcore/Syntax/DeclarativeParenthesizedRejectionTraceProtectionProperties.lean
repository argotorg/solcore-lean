import Solcore.Syntax.DeclarativeParenthesizedRejectionTraceGrammar
import Solcore.Syntax.DeclarativeParseDiagnosticCascadeProperties

/-! Protected child events survive later tuple-tail or parenthesized
rejection. Marker/closing failures emit nothing, and their uncommitted report
is separate from the complete protected diagnostic suffix. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.Expr →
    Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}

theorem ParenthesizedTupleTailTraceRejects.cascadeFilters
    (successProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected report trace},
      elementRejects source endByte input rejected report trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ParenthesizedTupleTailTraceRejects elementTrace elementRejects
      source endByte input rejected report trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  induction rejection with
  | commaMissing => exact .nil
  | elementRejected _ _ _ child => exact rejectProtected child
  | closingMissing _ _ _ child _ _ _ _ => exact successProtected child
  | laterRejected _ _ _ _ child _ _ _ ih => exact (successProtected child).append ih

theorem ParenthesizedExpressionTraceRejects.cascadeFilters
    (successProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected report trace},
      elementRejects source endByte input rejected report trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ParenthesizedExpressionTraceRejects elementTrace elementRejects
      source endByte input rejected report trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | openingMissing => exact .nil
  | firstRejected _ _ _ child => exact rejectProtected child
  | closingMissing _ _ _ child _ _ _ _ => exact successProtected child
  | tailRejected _ _ _ _ child _ _ tail =>
      exact (successProtected child).append (tail.cascadeFilters successProtected rejectProtected)

end Solcore.Syntax.DeclarativeGrammar
