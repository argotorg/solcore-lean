import Solcore.Syntax.DeclarativeNamedTypeRejectionTraceGrammar
import Solcore.Syntax.DeclarativeNamedTypeTraceGrammar
import Solcore.Syntax.DeclarativeQualifiedNameRejectionTraceProperties
import Solcore.Syntax.DeclarativeNamedTypeArgumentsRejectionTraceProperties

/-! Raw named-type rejection erases to the existing raw branch rejection.
It does not claim the type dispatcher's extra branch-selection conditions. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {ordinaryRejects : Remainder → Remainder → Prop} {source : SourceId} {endByte : Nat}

theorem NamedTypeTraceRejects.ordinary
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ordinaryRejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    NamedTypeRejects ordinaryRejects input rejected := by
  cases rejection with
  | nameRejected name => exact .nameRejected name.ordinary
  | argumentsRejected name arguments =>
      exact .argumentsRejected name.ordinary (arguments.ordinary successErases rejectErases)

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
theorem NamedTypeTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : NamedTypeTraceRejects elementTrace elementRejects source endByte input afterLeft leftReport leftTrace)
    (right : NamedTypeTraceRejects elementTrace elementRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | nameRejected name =>
      cases right with
      | nameRejected other => exact name.result_unique other
      | argumentsRejected other arguments => exact False.elim (name.disjoint_success ⟨_, _, _, other⟩)
  | argumentsRejected name arguments =>
      cases right with
      | nameRejected other => exact False.elim (other.disjoint_success ⟨_, _, _, name⟩)
      | argumentsRejected otherName otherArguments =>
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          rcases arguments.result_unique successUnique rejectUnique disjoint otherArguments with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

include successUnique disjoint in
theorem NamedTypeTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, NamedTypeTraceParses elementTrace source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases parsed with
  | parsed name arguments finishing =>
      cases rejection with
      | nameRejected rejected => exact rejected.disjoint_success ⟨_, _, _, name⟩
      | argumentsRejected otherName rejected =>
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          exact rejected.disjoint_success successUnique disjoint ⟨_, _, _, arguments⟩

end Solcore.Syntax.DeclarativeGrammar
