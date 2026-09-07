import Solcore.Syntax.DeclarativeNamedTypeArgumentsRejectionTraceGrammar
import Solcore.Syntax.DeclarativeNamedTypeArgumentsTraceGrammar
import Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceProperties
import Solcore.Syntax.DeclarativeCoreTypeOutcomeGrammar

/-! Exact rejection is restricted to present arguments. Independent child laws
determine the report and every event; ordinary erasure preserves the existing
selected nonempty-angle rejection rather than admitting absent arguments. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {ordinaryRejects : Remainder → Remainder → Prop} {source : SourceId} {endByte : Nat}

theorem NamedTypeArgumentsTraceRejects.opening_present
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedTypeArgumentsTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .less } := by
  cases rejection with
  | present span opening => exact ⟨span, opening⟩

theorem NamedTypeArgumentsTraceRejects.ordinary
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ordinaryRejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedTypeArgumentsTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    NamedTypeArgumentsRejects ordinaryRejects input rejected := by
  cases rejection with
  | present span opening arguments =>
      exact .selected span ⟨opening, rfl⟩ (arguments.ordinary successErases rejectErases)

variable
  (successUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
    elementTrace source endByte input left afterLeft leftTrace →
    elementTrace source endByte input right afterRight rightTrace →
      left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
  (rejectUnique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
    elementRejects source endByte input afterLeft leftReport leftTrace →
    elementRejects source endByte input afterRight rightReport rightTrace →
      afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace)
  (disjoint : ∀ {input rejected diagnostic trace},
    elementRejects source endByte input rejected diagnostic trace →
      ¬ ∃ value output events, elementTrace source endByte input value output events)

include successUnique rejectUnique disjoint in
theorem NamedTypeArgumentsTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : NamedTypeArgumentsTraceRejects elementTrace elementRejects source endByte input afterLeft leftReport leftTrace)
    (right : NamedTypeArgumentsTraceRejects elementTrace elementRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | present _ _ left =>
      cases right with
      | present _ _ right => exact left.result_unique successUnique rejectUnique disjoint right

include successUnique disjoint in
theorem NamedTypeArgumentsTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedTypeArgumentsTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ¬ ∃ arguments output events, NamedTypeArgumentsTraceParses elementTrace source endByte input arguments output events := by
  rintro ⟨arguments, output, events, parsed⟩
  cases rejection with
  | present span opening rejection =>
      cases parsed with
      | absent absent => exact absent ⟨span, opening⟩
      | present parsed => exact rejection.disjoint_success successUnique disjoint ⟨_, _, _, parsed⟩

end Solcore.Syntax.DeclarativeGrammar
