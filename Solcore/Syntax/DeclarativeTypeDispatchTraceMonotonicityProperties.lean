import Solcore.Syntax.DeclarativeTypeDispatchTraceGrammar
import Solcore.Syntax.DeclarativeTypeFormRejectionTraceMonotonicityProperties

/-! One selected type layer is monotone in its nested relations at fixed source
coordinates. The selected branch and every negative/positive guard stay fixed;
the final rejection has no child relation to replace. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace otherTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop}
  {elementRejects otherRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop} {source : SourceId} {endByte : Nat}

theorem TypeDispatchRawTraceParses.mono
    (childMap : ∀ {input value output trace},
      elementTrace source endByte input value output trace → otherTrace source endByte input value output trace)
    {branch : TypeDispatchBranch} {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TypeDispatchRawTraceParses elementTrace branch source endByte input value output trace) :
    TypeDispatchRawTraceParses otherTrace branch source endByte input value output trace := by
  cases branch with
  | function => exact FunctionTypeTraceParses.mono childMap parsed
  | comptime => exact ComptimeTypeTraceParses.mono childMap parsed
  | mapping => exact MappingTypeTraceParses.mono childMap parsed
  | proxy => exact ProxyTypeTraceParses.mono childMap parsed
  | tuple => exact TupleTypeTraceParses.mono childMap parsed
  | named => exact NamedTypeTraceParses.mono childMap parsed
  | final => exact parsed

theorem TypeDispatchTraceParses.mono
    (childMap : ∀ {input value output trace},
      elementTrace source endByte input value output trace → otherTrace source endByte input value output trace)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TypeDispatchTraceParses elementTrace source endByte input value output trace) :
    TypeDispatchTraceParses otherTrace source endByte input value output trace := by
  cases parsed with
  | selected branch selection raw => exact .selected branch selection (TypeDispatchRawTraceParses.mono childMap raw)

theorem TypeDispatchRawTraceRejects.mono
    (successMap : ∀ {input value output trace},
      elementTrace source endByte input value output trace → otherTrace source endByte input value output trace)
    (rejectMap : ∀ {input rejected report trace},
      elementRejects source endByte input rejected report trace → otherRejects source endByte input rejected report trace)
    {branch : TypeDispatchBranch} {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TypeDispatchRawTraceRejects elementTrace elementRejects branch source endByte input rejected report trace) :
    TypeDispatchRawTraceRejects otherTrace otherRejects branch source endByte input rejected report trace := by
  cases branch with
  | function => exact FunctionTypeTraceRejects.mono successMap rejectMap rejection
  | comptime => exact ComptimeTypeTraceRejects.mono successMap rejectMap rejection
  | mapping => exact MappingTypeTraceRejects.mono successMap rejectMap rejection
  | proxy => exact ProxyTypeTraceRejects.mono rejectMap rejection
  | tuple => exact TupleTypeTraceRejects.mono successMap rejectMap rejection
  | named => exact NamedTypeTraceRejects.mono successMap rejectMap rejection
  | final => exact rejection

theorem TypeDispatchTraceRejects.mono
    (successMap : ∀ {input value output trace},
      elementTrace source endByte input value output trace → otherTrace source endByte input value output trace)
    (rejectMap : ∀ {input rejected report trace},
      elementRejects source endByte input rejected report trace → otherRejects source endByte input rejected report trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TypeDispatchTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    TypeDispatchTraceRejects otherTrace otherRejects source endByte input rejected report trace := by
  cases rejection with
  | selected branch selection raw =>
      exact .selected branch selection (TypeDispatchRawTraceRejects.mono successMap rejectMap raw)

end Solcore.Syntax.DeclarativeGrammar
