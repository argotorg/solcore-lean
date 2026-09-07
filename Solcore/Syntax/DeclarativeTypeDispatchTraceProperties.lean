import Solcore.Syntax.DeclarativeTypeDispatchTraceOutcomeProperties
import Solcore.Syntax.DeclarativeFunctionTypeRejectionTraceProperties
import Solcore.Syntax.DeclarativeComptimeTypeRejectionTraceProperties
import Solcore.Syntax.DeclarativeMappingTypeTraceOutcomeProperties
import Solcore.Syntax.DeclarativeMappingTypeRejectionTraceProtectionProperties
import Solcore.Syntax.DeclarativeProxyTypeRejectionTraceProperties
import Solcore.Syntax.DeclarativeTupleTypeRejectionTraceProperties
import Solcore.Syntax.DeclarativeNamedTypeTraceOutcomeProperties
import Solcore.Syntax.DeclarativeNamedTypeRejectionTraceProtectionProperties

/-! Concrete raw-form exactness and protected-event laws lift to the selected
type layer. Child carrier preservation is separate from all exactness claims. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem typeDispatchRawTraceExactOutcomeSpec
    (children : TraceExactOutcomeSpec elementTrace elementRejects source endByte)
    (branch : TypeDispatchBranch) :
    TraceExactOutcomeSpec (TypeDispatchRawTraceParses elementTrace branch)
      (TypeDispatchRawTraceRejects elementTrace elementRejects branch) source endByte := by
  cases branch with
  | function => exact functionTypeTraceExactOutcomeSpec children
  | comptime => exact comptimeTypeTraceExactOutcomeSpec children
  | mapping => exact mappingTypeTraceExactOutcomeSpec children
  | proxy => exact proxyTypeTraceExactOutcomeSpec children
  | tuple => exact tupleTypeTraceExactOutcomeSpec children
  | named => exact namedTypeTraceExactOutcomeSpec children
  | final =>
      refine ⟨?_, TypeDispatchFinalTraceRejects.result_unique, ?_⟩
      · intro _ _ _ _ _ _ _ impossible; exact False.elim impossible
      · intro _ _ _ _ _ ⟨_, _, _, impossible⟩; exact impossible

theorem typeDispatchTraceExactOutcomeSpec
    (children : TraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    TraceExactOutcomeSpec (TypeDispatchTraceParses elementTrace)
      (TypeDispatchTraceRejects elementTrace elementRejects) source endByte :=
  typeDispatchTraceExactOutcomeSpec_of_raw (typeDispatchRawTraceExactOutcomeSpec children)

theorem TypeDispatchTraceParses.output_window
    (childWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TypeDispatchTraceParses elementTrace source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | selected branch selection raw =>
      cases branch <;> simp only [TypeDispatchRawTraceParses] at raw
      case function => exact raw.output_window childWindow
      case comptime => exact raw.output_window childWindow
      case mapping => exact raw.output_window childWindow
      case proxy => exact raw.output_window childWindow
      case tuple => exact raw.output_window childWindow
      case named => exact raw.output_window childWindow

theorem TypeDispatchTraceParses.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TypeDispatchTraceParses elementTrace source endByte input value output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | selected branch selection raw =>
      cases branch <;> simp only [TypeDispatchRawTraceParses] at raw
      case function => exact raw.cascadeFilters childProtected
      case comptime => exact raw.cascadeFilters childProtected
      case mapping => exact raw.cascadeFilters childProtected
      case proxy => exact raw.cascadeFilters childProtected
      case tuple => exact raw.cascadeFilters childProtected
      case named => exact raw.cascadeFilters childProtected

theorem TypeDispatchTraceRejects.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (successProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TypeDispatchTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | selected branch selection raw =>
      cases branch <;> simp only [TypeDispatchRawTraceRejects] at raw
      case function => exact raw.cascadeFilters successProtected rejectProtected
      case comptime => exact raw.cascadeFilters successProtected rejectProtected
      case mapping => exact raw.cascadeFilters successProtected rejectProtected
      case proxy => exact raw.cascadeFilters rejectProtected
      case tuple => exact TupleTypeTraceRejects.cascadeFilters successProtected rejectProtected raw
      case named => exact raw.cascadeFilters successProtected rejectProtected
      case final => cases raw; exact .nil

end Solcore.Syntax.DeclarativeGrammar
