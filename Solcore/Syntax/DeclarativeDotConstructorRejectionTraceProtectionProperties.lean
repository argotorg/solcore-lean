import Solcore.Syntax.DeclarativeDotConstructorRejectionTraceGrammar
import Solcore.Syntax.DeclarativeDelimitedNoTrailingTraceProtectionProperties
import Solcore.Syntax.DeclarativeExpressionNameTraceProtectionProperties

/-! A checked constructor name remains protected when its argument list
later rejects. Protected child events follow it in order, while the separate
uncommitted failure report is not included in this preservation claim. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.Expr →
    Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}

theorem OptionalDotConstructorArgumentsTraceRejects.cascadeFilters
    (successProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected diagnostic trace},
      elementRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OptionalDotConstructorArgumentsTraceRejects elementTrace elementRejects
      source endByte input rejected diagnostic trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | present _ _ arguments => exact arguments.cascadeFilters successProtected rejectProtected

theorem DotConstructorTraceRejects.cascadeFilters
    (successProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected diagnostic trace},
      elementRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DotConstructorTraceRejects elementTrace elementRejects
      source endByte input rejected diagnostic trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | dotMissing => exact .nil
  | nameRejected _ _ name => exact name.cascadeFilters text lexical
  | argumentsRejected _ _ name arguments =>
      exact (name.cascadeFilters text lexical).append
        (arguments.cascadeFilters successProtected rejectProtected)

end Solcore.Syntax.DeclarativeGrammar
