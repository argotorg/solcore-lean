import Solcore.Syntax.DeclarativeOptionalLambdaReturnTypeTraceProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties
import Solcore.Syntax.DeclarativeTraceOutcomeSpec

/-! Conditional uniqueness and disjointness of the optional annotation. This
bundle does not assert that the supplied type relation has an outcome. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop}
  {typeRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem OptionalLambdaReturnTypeTraceParses.result_unique
    (unique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      typeTrace source endByte input left afterLeft leftTrace →
      typeTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Option Syntax.TypeExpr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : OptionalLambdaReturnTypeTraceParses typeTrace source endByte input left afterLeft leftTrace)
    (rightParsed : OptionalLambdaReturnTypeTraceParses typeTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | absent absent =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl, rfl⟩
      | present span arrow _ => exact False.elim (absent ⟨span, arrow.1⟩)
  | present span arrow type =>
      cases rightParsed with
      | absent absent => exact False.elim (absent ⟨span, arrow.1⟩)
      | present _ otherArrow other =>
          rcases arrow.result_unique otherArrow with ⟨rfl, rfl⟩
          rcases unique type other with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem OptionalLambdaReturnTypeTraceRejects.result_unique
    (unique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
      typeRejects source endByte input afterLeft leftReport leftTrace →
      typeRejects source endByte input afterRight rightReport rightTrace →
        afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : OptionalLambdaReturnTypeTraceRejects typeRejects source endByte
      input afterLeft leftReport leftTrace)
    (rightRejected : OptionalLambdaReturnTypeTraceRejects typeRejects source endByte
      input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases leftRejected with
  | typeRejected span arrow type =>
      cases rightRejected with
      | typeRejected _ otherArrow other =>
          rcases arrow.result_unique otherArrow with ⟨rfl, rfl⟩
          exact unique type other

theorem OptionalLambdaReturnTypeTraceRejects.disjoint_success
    (disjoint : ∀ {input rejected diagnostic trace},
      typeRejects source endByte input rejected diagnostic trace →
        ¬ ∃ type output events, typeTrace source endByte input type output events)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OptionalLambdaReturnTypeTraceRejects typeRejects source endByte
      input rejected diagnostic trace) :
    ¬ ∃ type output events, OptionalLambdaReturnTypeTraceParses typeTrace source endByte input type output events := by
  rintro ⟨type, output, events, parsed⟩
  cases rejection with
  | typeRejected span arrow rejected =>
      cases parsed with
      | absent absent => exact absent ⟨span, arrow.1⟩
      | present _ otherArrow parsed =>
          rcases arrow.result_unique otherArrow with ⟨rfl, rfl⟩
          exact disjoint rejected ⟨_, _, _, parsed⟩

theorem optionalLambdaReturnTypeTraceExactOutcomeSpec
    (types : TraceExactOutcomeSpec typeTrace typeRejects source endByte) :
    TraceExactOutcomeSpec (OptionalLambdaReturnTypeTraceParses typeTrace)
      (OptionalLambdaReturnTypeTraceRejects typeRejects) source endByte where
  successResultUnique := OptionalLambdaReturnTypeTraceParses.result_unique types.successResultUnique
  rejectResultUnique := OptionalLambdaReturnTypeTraceRejects.result_unique types.rejectResultUnique
  successRejectDisjoint := OptionalLambdaReturnTypeTraceRejects.disjoint_success types.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
