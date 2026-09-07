import Solcore.Syntax.DeclarativeTypeFormTraceMonotonicityProperties
import Solcore.Syntax.DeclarativeNamedTypeRejectionTraceGrammar
import Solcore.Syntax.DeclarativeMappingTypeRejectionTraceGrammar
import Solcore.Syntax.DeclarativeProxyTypeRejectionTraceGrammar
import Solcore.Syntax.DeclarativeTupleTypeRejectionTraceGrammar
import Solcore.Syntax.DeclarativeComptimeTypeRejectionTraceGrammar
import Solcore.Syntax.DeclarativeFunctionTypeRejectionTraceGrammar

/-! Enlarging child relations preserves raw type rejection at the same source
and end byte. The full report, remainder, and ordered successful/rejected child
events are identical; no terminal report is inserted into those events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace otherTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop}
  {elementRejects otherRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop} {source : SourceId} {endByte : Nat}
  (successMap : ∀ {input value output trace},
    elementTrace source endByte input value output trace → otherTrace source endByte input value output trace)
  (rejectMap : ∀ {input rejected report trace},
    elementRejects source endByte input rejected report trace → otherRejects source endByte input rejected report trace)

include successMap rejectMap in
theorem NamedTypeArgumentsTraceRejects.mono
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedTypeArgumentsTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    NamedTypeArgumentsTraceRejects otherTrace otherRejects source endByte input rejected report trace := by
  cases rejection with
  | present span opening values => exact .present span opening (values.mono successMap rejectMap)

include successMap rejectMap in
theorem NamedTypeTraceRejects.mono
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    NamedTypeTraceRejects otherTrace otherRejects source endByte input rejected report trace := by
  cases rejection with
  | nameRejected name => exact .nameRejected name
  | argumentsRejected name arguments => exact .argumentsRejected name (arguments.mono successMap rejectMap)

include successMap rejectMap in
theorem MappingTypeTraceRejects.mono
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : MappingTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    MappingTypeTraceRejects otherTrace otherRejects source endByte input rejected report trace := by
  cases rejection with
  | markerMissing absent reported => exact .markerMissing absent reported
  | openingMissing span marker absent reported => exact .openingMissing span marker absent reported
  | keyRejected markerSpan openingSpan marker opening key =>
      exact .keyRejected markerSpan openingSpan marker opening (rejectMap key)
  | arrowMissing markerSpan openingSpan marker opening key absent reported =>
      exact .arrowMissing markerSpan openingSpan marker opening (successMap key) absent reported
  | valueRejected markerSpan openingSpan arrowSpan marker opening key arrow value =>
      exact .valueRejected markerSpan openingSpan arrowSpan marker opening (successMap key) arrow (rejectMap value)
  | closingMissing markerSpan openingSpan arrowSpan marker opening key arrow value absent reported =>
      exact .closingMissing markerSpan openingSpan arrowSpan marker opening (successMap key) arrow
        (successMap value) absent reported

include rejectMap in
theorem ProxyTypeTraceRejects.mono
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ProxyTypeTraceRejects elementRejects source endByte input rejected report trace) :
    ProxyTypeTraceRejects otherRejects source endByte input rejected report trace := by
  cases rejection with
  | markerMissing absent reported => exact .markerMissing absent reported
  | innerRejected span marker inner => exact .innerRejected span marker (rejectMap inner)

include successMap rejectMap in
theorem TupleTypeTraceRejects.mono
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TupleTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    TupleTypeTraceRejects otherTrace otherRejects source endByte input rejected report trace :=
  TrailingDelimitedListTraceRejects.mono successMap rejectMap rejection

include successMap rejectMap in
theorem ComptimeTypeTraceRejects.mono
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ComptimeTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ComptimeTypeTraceRejects otherTrace otherRejects source endByte input rejected report trace := by
  cases rejection with
  | markerMissing absent reported => exact .markerMissing absent reported
  | openingMissing span marker absent reported => exact .openingMissing span marker absent reported
  | innerRejected markerSpan openingSpan marker opening inner =>
      exact .innerRejected markerSpan openingSpan marker opening (rejectMap inner)
  | closingMissing markerSpan openingSpan marker opening inner absent reported =>
      exact .closingMissing markerSpan openingSpan marker opening (successMap inner) absent reported

include successMap rejectMap in
theorem FunctionReturnsTraceRejects.mono
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionReturnsTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    FunctionReturnsTraceRejects otherTrace otherRejects source endByte input rejected report trace := by
  cases rejection with
  | present span marker values => exact .present span marker (values.mono successMap rejectMap)

include successMap rejectMap in
theorem FunctionTypeTraceRejects.mono
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    FunctionTypeTraceRejects otherTrace otherRejects source endByte input rejected report trace := by
  cases rejection with
  | markerMissing absent reported => exact .markerMissing absent reported
  | parametersRejected span marker values => exact .parametersRejected span marker (values.mono successMap rejectMap)
  | returnsRejected span marker parameters returns =>
      exact .returnsRejected span marker (parameters.mono successMap) (returns.mono successMap rejectMap)

end Solcore.Syntax.DeclarativeGrammar
