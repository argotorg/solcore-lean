import Solcore.Syntax.DeclarativeDotConstructorTraceGrammar
import Solcore.Syntax.DeclarativeExpressionNameTraceProtectionProperties
import Solcore.Syntax.DeclarativeDelimitedNoTrailingTraceProtectionProperties

/-! Checked name events are intrinsically protected; protected argument
events follow them without reordering, dropping metadata, or deduplication. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.Expr →
    Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}

theorem OptionalDotConstructorArgumentsTraceParses.cascadeFilters
    (elementProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {arguments : Option (DelimitedList Syntax.Expr)} {trace : List ParseDiagnostic}
    (parsed : OptionalDotConstructorArgumentsTraceParses elementTrace source endByte input arguments output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | absent => exact .nil
  | present args => exact args.cascadeFilters elementProtected

theorem DotConstructorTraceParses.cascadeFilters
    (elementProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : DotConstructorTraceParses elementTrace source endByte input value output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed span dot name args =>
      exact (name.cascadeFilters text lexical).append (args.cascadeFilters elementProtected)

end Solcore.Syntax.DeclarativeGrammar
