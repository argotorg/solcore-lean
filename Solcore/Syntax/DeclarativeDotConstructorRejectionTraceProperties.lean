import Solcore.Syntax.DeclarativeDotConstructorRejectionTraceGrammar
import Solcore.Syntax.DeclarativeDelimitedNoTrailingRejectionTraceProperties
import Solcore.Syntax.DeclarativeExpressionNameTraceProperties

/-! Independent rejection erasure, functionality, and exclusion. The older
ordinary dot relation is dispatcher-selected, so raw-dot erasure explicitly
separates missing-dot rejection instead of silently strengthening that relation. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {ordinaryParses : Remainder → Syntax.Expr → Remainder → Prop}
  {ordinaryRejects : Remainder → Remainder → Prop} {source : SourceId} {endByte : Nat}

theorem OptionalDotConstructorArgumentsTraceRejects.ordinary
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ordinaryParses input value output)
    (rejectErases : ∀ {input rejected diagnostic trace}, elementRejects source endByte input rejected diagnostic trace →
      ordinaryRejects input rejected)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OptionalDotConstructorArgumentsTraceRejects elementTrace elementRejects source endByte
      input rejected diagnostic trace) :
    OptionalDotConstructorArgumentsRejects ordinaryParses ordinaryRejects input rejected := by
  cases rejection with
  | present span opening arguments => exact .present span opening (arguments.ordinary successErases rejectErases)

theorem DotConstructorTraceRejects.ordinary_cases
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ordinaryParses input value output)
    (rejectErases : ∀ {input rejected diagnostic trace}, elementRejects source endByte input rejected diagnostic trace →
      ordinaryRejects input rejected)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DotConstructorTraceRejects elementTrace elementRejects source endByte input rejected diagnostic trace) :
    (TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .dot) ∧ rejected = input) ∨
      DotConstructorRejects ordinaryParses ordinaryRejects input rejected := by
  cases rejection with
  | dotMissing absent reported => exact .inl ⟨absent, rfl⟩
  | nameRejected span dot name => exact .inr (.nameRejected span dot name.ordinary)
  | argumentsRejected span dot name arguments =>
      exact .inr (.argumentsRejected span dot name.ordinary (arguments.ordinary successErases rejectErases))

theorem DotConstructorTraceRejects.ordinary_of_dot_present
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ordinaryParses input value output)
    (rejectErases : ∀ {input rejected diagnostic trace}, elementRejects source endByte input rejected diagnostic trace →
      ordinaryRejects input rejected)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (selected : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .dot })
    (rejection : DotConstructorTraceRejects elementTrace elementRejects source endByte input rejected diagnostic trace) :
    DotConstructorRejects ordinaryParses ordinaryRejects input rejected := by
  rcases rejection.ordinary_cases successErases rejectErases with missing | ordinary
  · exact False.elim (missing.1 selected)
  · exact ordinary

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
theorem OptionalDotConstructorArgumentsTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : OptionalDotConstructorArgumentsTraceRejects elementTrace elementRejects source endByte
      input afterLeft leftReport leftTrace)
    (right : OptionalDotConstructorArgumentsTraceRejects elementTrace elementRejects source endByte
      input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | present _ _ left =>
      cases right with
      | present _ _ right => exact left.result_unique successUnique rejectUnique disjoint right

include successUnique rejectUnique disjoint in
theorem DotConstructorTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : DotConstructorTraceRejects elementTrace elementRejects source endByte
      input afterLeft leftReport leftTrace)
    (right : DotConstructorTraceRejects elementTrace elementRejects source endByte
      input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | dotMissing absent reported =>
      cases right with
      | dotMissing _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | nameRejected span dot _ | argumentsRejected span dot _ _ => exact False.elim (absent ⟨span, dot.1⟩)
  | nameRejected span dot name =>
      cases right with
      | dotMissing absent _ => exact False.elim (absent ⟨span, dot.1⟩)
      | nameRejected _ otherDot otherName =>
          cases dot.output_unique otherDot
          exact name.result_unique otherName
      | argumentsRejected _ otherDot otherName _ =>
          cases dot.output_unique otherDot
          exact False.elim (name.disjoint_success otherName)
  | argumentsRejected span dot name arguments =>
      cases right with
      | dotMissing absent _ => exact False.elim (absent ⟨span, dot.1⟩)
      | nameRejected _ otherDot otherName =>
          cases dot.output_unique otherDot
          exact False.elim (otherName.disjoint_success name)
      | argumentsRejected _ otherDot otherName otherArguments =>
          cases dot.output_unique otherDot
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          rcases arguments.result_unique successUnique rejectUnique disjoint otherArguments with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

include successUnique disjoint in
theorem OptionalDotConstructorArgumentsTraceRejects.disjoint_success
    {input rejected after : Remainder} {diagnostic : ParseDiagnostic} {trace events : List ParseDiagnostic}
    {arguments : Option (DelimitedList Syntax.Expr)}
    (rejection : OptionalDotConstructorArgumentsTraceRejects elementTrace elementRejects source endByte
      input rejected diagnostic trace)
    (success : OptionalDotConstructorArgumentsTraceParses elementTrace source endByte input arguments after events) : False := by
  cases rejection with
  | present span opening rejected =>
      cases success with
      | absent absent => exact absent ⟨span, opening⟩
      | present parsed => exact rejected.disjoint_success successUnique disjoint ⟨_, _, _, parsed⟩

include successUnique disjoint in
theorem DotConstructorTraceRejects.disjoint_success
    {input rejected after : Remainder} {diagnostic : ParseDiagnostic} {trace events : List ParseDiagnostic}
    {value : Syntax.Expr}
    (rejection : DotConstructorTraceRejects elementTrace elementRejects source endByte input rejected diagnostic trace)
    (success : DotConstructorTraceParses elementTrace source endByte input value after events) : False := by
  cases success with
  | parsed _ dot name arguments =>
      cases rejection with
      | dotMissing absent reported => exact absent ⟨_, dot.1⟩
      | nameRejected _ otherDot rejectedName =>
          cases dot.output_unique otherDot
          exact rejectedName.disjoint_success name
      | argumentsRejected _ otherDot otherName rejectedArguments =>
          cases dot.output_unique otherDot
          cases (name.result_unique otherName).2.1
          exact rejectedArguments.disjoint_success successUnique disjoint arguments

end Solcore.Syntax.DeclarativeGrammar
