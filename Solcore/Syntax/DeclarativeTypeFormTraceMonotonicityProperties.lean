import Solcore.Syntax.DeclarativeDelimitedTrailingTraceMonotonicityProperties
import Solcore.Syntax.DeclarativeNamedTypeTraceGrammar
import Solcore.Syntax.DeclarativeMappingTypeTraceGrammar
import Solcore.Syntax.DeclarativeProxyTypeTraceGrammar
import Solcore.Syntax.DeclarativeTupleTypeTraceGrammar
import Solcore.Syntax.DeclarativeComptimeTypeTraceGrammar
import Solcore.Syntax.DeclarativeFunctionTypeTraceGrammar

/-! Raw type forms preserve all source-shaped data and events when their child
success relation is enlarged at the same source and end byte. Qualified names,
finishing events, optional guards, and delimiter policies are unchanged. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace otherTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop} {source : SourceId} {endByte : Nat}
  (childMap : ∀ {input value output trace},
    elementTrace source endByte input value output trace → otherTrace source endByte input value output trace)

include childMap

theorem NamedTypeArgumentsTraceParses.mono
    {input output : Remainder} {values : Option (NonemptyDelimitedList Syntax.TypeExpr)}
    {trace : List ParseDiagnostic}
    (parsed : NamedTypeArgumentsTraceParses elementTrace source endByte input values output trace) :
    NamedTypeArgumentsTraceParses otherTrace source endByte input values output trace := by
  cases parsed with
  | absent absent => exact .absent absent
  | present values => exact .present (values.mono childMap)

theorem NamedTypeTraceParses.mono
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : NamedTypeTraceParses elementTrace source endByte input value output trace) :
    NamedTypeTraceParses otherTrace source endByte input value output trace := by
  cases parsed with
  | parsed name arguments finished => exact .parsed name (arguments.mono childMap) finished

theorem MappingTypeTraceParses.mono
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : MappingTypeTraceParses elementTrace source endByte input value output trace) :
    MappingTypeTraceParses otherTrace source endByte input value output trace := by
  cases parsed with
  | parsed markerSpan openingSpan arrowSpan closingSpan marker opening key arrow value closing =>
      exact .parsed markerSpan openingSpan arrowSpan closingSpan marker opening
        (childMap key) arrow (childMap value) closing

theorem ProxyTypeTraceParses.mono
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ProxyTypeTraceParses elementTrace source endByte input value output trace) :
    ProxyTypeTraceParses otherTrace source endByte input value output trace := by
  cases parsed with
  | parsed span marker inner => exact .parsed span marker (childMap inner)

theorem TupleTypeTraceParses.mono
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TupleTypeTraceParses elementTrace source endByte input value output trace) :
    TupleTypeTraceParses otherTrace source endByte input value output trace := by
  cases parsed with
  | parsed values => exact .parsed (values.mono childMap)

theorem ComptimeTypeTraceParses.mono
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ComptimeTypeTraceParses elementTrace source endByte input value output trace) :
    ComptimeTypeTraceParses otherTrace source endByte input value output trace := by
  cases parsed with
  | parsed markerSpan openingSpan closingSpan marker opening inner closing =>
      exact .parsed markerSpan openingSpan closingSpan marker opening (childMap inner) closing

theorem FunctionReturnsTraceParses.mono
    {input output : Remainder} {values : Option (DelimitedList Syntax.TypeExpr)}
    {trace : List ParseDiagnostic}
    (parsed : FunctionReturnsTraceParses elementTrace source endByte input values output trace) :
    FunctionReturnsTraceParses otherTrace source endByte input values output trace := by
  cases parsed with
  | absent absent => exact .absent absent
  | present span marker values => exact .present span marker (values.mono childMap)

theorem FunctionTypeTraceParses.mono
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : FunctionTypeTraceParses elementTrace source endByte input value output trace) :
    FunctionTypeTraceParses otherTrace source endByte input value output trace := by
  cases parsed with
  | parsed span marker parameters returns =>
      exact .parsed span marker (parameters.mono childMap) (returns.mono childMap)

end Solcore.Syntax.DeclarativeGrammar
