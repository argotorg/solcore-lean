import Solcore.Syntax.DeclarativeTupleTypeRejectionTraceGrammar
import Solcore.Syntax.DeclarativeTupleTypeTraceProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceProtectionProperties
import Solcore.Syntax.DeclarativeCoreTypeOutcomeGrammar
import Solcore.Syntax.DeclarativeTraceOutcomeSpec

/-! Raw tuple rejection includes an absent opening marker. Its erasure keeps
that case separate from the selected ordinary tuple branch. Exactness concerns
uniqueness/disjointness, and protection excludes the uncommitted final report. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop}
  {typeRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem TupleTypeTraceRejects.ordinary_cases
    {ordinaryRejects : Remainder → Remainder → Prop}
    (successErases : ∀ {input value output trace},
      typeTrace source endByte input value output trace → TypeExprParses input value output)
    (rejectErases : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace → ordinaryRejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TupleTypeTraceRejects typeTrace typeRejects source endByte input rejected report trace) :
    (TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftParen) ∧ rejected = input) ∨
      TupleTypeRejects ordinaryRejects input rejected := by
  have ordinary := TrailingDelimitedListTraceRejects.ordinary successErases rejectErases rejection
  cases rejection with
  | openingMissing absent reported => exact .inl ⟨absent, rfl⟩
  | firstRejected span opening continues child => exact .inr (.selected span opening ordinary)
  | tailRejected span opening continues child progress tail => exact .inr (.selected span opening ordinary)

theorem TupleTypeTraceRejects.ordinary_of_opening_present
    {ordinaryRejects : Remainder → Remainder → Prop}
    (successErases : ∀ {input value output trace},
      typeTrace source endByte input value output trace → TypeExprParses input value output)
    (rejectErases : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace → ordinaryRejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (opening : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .leftParen })
    (rejection : TupleTypeTraceRejects typeTrace typeRejects source endByte input rejected report trace) :
    TupleTypeRejects ordinaryRejects input rejected := by
  rcases TupleTypeTraceRejects.ordinary_cases successErases rejectErases rejection with missing | ordinary
  · exact False.elim (missing.1 opening)
  · exact ordinary

theorem TupleTypeTraceRejects.result_unique
    (successUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      typeTrace source endByte input left afterLeft leftTrace →
      typeTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    (rejectUnique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
      typeRejects source endByte input afterLeft leftReport leftTrace →
      typeRejects source endByte input afterRight rightReport rightTrace →
        afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace)
    (disjoint : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace →
        ¬ ∃ value output events, typeTrace source endByte input value output events)
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : TupleTypeTraceRejects typeTrace typeRejects source endByte input afterLeft leftReport leftTrace)
    (right : TupleTypeTraceRejects typeTrace typeRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace :=
  TrailingDelimitedListTraceRejects.result_unique successUnique rejectUnique disjoint left right

theorem TupleTypeTraceRejects.disjoint_success
    (successUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      typeTrace source endByte input left afterLeft leftTrace →
      typeTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    (disjoint : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace →
        ¬ ∃ value output events, typeTrace source endByte input value output events)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TupleTypeTraceRejects typeTrace typeRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, TupleTypeTraceParses typeTrace source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases parsed with
  | parsed elements =>
      exact TrailingDelimitedListTraceRejects.disjoint_success successUnique disjoint rejection ⟨_, _, _, elements⟩

theorem TupleTypeTraceRejects.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (successProtected : ∀ {input value output trace},
      typeTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TupleTypeTraceRejects typeTrace typeRejects source endByte input rejected report trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace :=
  TrailingDelimitedListTraceRejects.cascadeFilters successProtected rejectProtected rejection

theorem tupleTypeTraceExactOutcomeSpec
    (types : TraceExactOutcomeSpec typeTrace typeRejects source endByte) :
    TraceExactOutcomeSpec (TupleTypeTraceParses typeTrace)
      (TupleTypeTraceRejects typeTrace typeRejects) source endByte where
  successResultUnique := TupleTypeTraceParses.result_unique types.successResultUnique
  rejectResultUnique := TupleTypeTraceRejects.result_unique types.successResultUnique
    types.rejectResultUnique types.successRejectDisjoint
  successRejectDisjoint := TupleTypeTraceRejects.disjoint_success types.successResultUnique
    types.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
