import Solcore.Syntax.DeclarativeLiteralDiagnosticTraceGrammar
import Solcore.Syntax.DeclarativeCoreExpressionLeafExactnessProperties
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties

/-! Independent total, disjoint, and exact literal/Boolean diagnostic outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

theorem CoreLiteralTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.CoreLiteral}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : CoreLiteralTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : CoreLiteralTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace :=
  ⟨(leftParsed.1.result_unique rightParsed.1).1,
    (leftParsed.1.result_unique rightParsed.1).2, leftParsed.2.trans rightParsed.2.symm⟩

theorem BooleanIdentifierTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.Identifier}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : BooleanIdentifierTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : BooleanIdentifierTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  refine ⟨leftParsed.1.value_unique rightParsed.1, ?_, leftParsed.2.trans rightParsed.2.symm⟩
  cases leftParsed.1 <;> cases rightParsed.1 <;> rfl

theorem LiteralExpressionTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.Expr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : LiteralExpressionTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : LiteralExpressionTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace :=
  ⟨LiteralExpressionOrdinaryParses.value_unique leftParsed.1 rightParsed.1,
    LiteralExpressionOrdinaryParses.output_unique leftParsed.1 rightParsed.1,
    leftParsed.2.trans rightParsed.2.symm⟩

theorem CoreLiteralTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {left right : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : CoreLiteralTraceRejects source endByte input afterLeft left leftTrace)
    (rightRejected : CoreLiteralTraceRejects source endByte input afterRight right rightTrace) :
    afterLeft = afterRight ∧ left = right ∧ leftTrace = rightTrace := by
  rcases leftRejected with ⟨leftOrdinary, leftReport, leftEvents⟩
  rcases rightRejected with ⟨rightOrdinary, rightReport, rightEvents⟩
  cases leftOrdinary
  cases rightOrdinary
  exact ⟨rfl, leftReport.diagnostic_unique rightReport, leftEvents.trans rightEvents.symm⟩

theorem BooleanIdentifierTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {left right : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : BooleanIdentifierTraceRejects source endByte input afterLeft left leftTrace)
    (rightRejected : BooleanIdentifierTraceRejects source endByte input afterRight right rightTrace) :
    afterLeft = afterRight ∧ left = right ∧ leftTrace = rightTrace :=
  ⟨leftRejected.2.1.trans rightRejected.2.1.symm,
    leftRejected.2.2.1.diagnostic_unique rightRejected.2.2.1,
    leftRejected.2.2.2.trans rightRejected.2.2.2.symm⟩

theorem CoreLiteralTraceRejects.disjoint_success
    {input rejected after : Remainder} {diagnostic : ParseDiagnostic} {literal : Syntax.CoreLiteral}
    {rejectTrace successTrace : List ParseDiagnostic}
    (rejectedTrace : CoreLiteralTraceRejects source endByte input rejected diagnostic rejectTrace)
    (successful : CoreLiteralTraceParses source endByte input literal after successTrace) : False :=
  rejectedTrace.1.disjointOrdinary ⟨literal, after, successful.1⟩

theorem BooleanIdentifierTraceRejects.disjoint_success
    {input rejected after : Remainder} {diagnostic : ParseDiagnostic} {name : Syntax.Identifier}
    {rejectTrace successTrace : List ParseDiagnostic}
    (rejectedTrace : BooleanIdentifierTraceRejects source endByte input rejected diagnostic rejectTrace)
    (successful : BooleanIdentifierTraceParses source endByte input name after successTrace) : False := by
  cases successful.1 with
  | trueKeyword token => exact rejectedTrace.1.1 ⟨_, token⟩
  | falseKeyword token => exact rejectedTrace.1.2 ⟨_, token⟩

/-- Every carrier has one literal success or silent first-failure report,
independently of all parser states, executable fuel, and input validity. -/
theorem coreLiteralTrace_outcome_total (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ literal after trace, CoreLiteralTraceParses source endByte input literal after trace) ∨
    ∃ rejected diagnostic trace, CoreLiteralTraceRejects source endByte input rejected diagnostic trace := by
  classical
  by_cases success : ∃ literal after, CoreLiteralParses input literal after
  · rcases success with ⟨literal, after, parsed⟩
    exact Or.inl ⟨literal, after, [], parsed, rfl⟩
  · have absent : CoreLiteralAbsentAt input := by
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨span, spelling, token⟩; exact success ⟨_, _, .decimal token⟩
      · rintro ⟨span, spelling, token⟩; exact success ⟨_, _, .hexadecimal token⟩
      · rintro ⟨span, spelling, token⟩; exact success ⟨_, _, .string token⟩
    rcases rejectAtReports_total source endByte { head := .coreLiteral, tail := [] }
      .expression input with ⟨diagnostic, reported⟩
    exact Or.inr ⟨input, diagnostic, [], .absent absent, reported, rfl⟩

theorem booleanIdentifierTrace_outcome_total (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ name after trace, BooleanIdentifierTraceParses source endByte input name after trace) ∨
    ∃ rejected diagnostic trace,
      BooleanIdentifierTraceRejects source endByte input rejected diagnostic trace := by
  classical
  by_cases success : ∃ name after, BooleanIdentifierParses input name after
  · rcases success with ⟨name, after, parsed⟩
    exact Or.inl ⟨name, after, [], parsed, rfl⟩
  · have absent : BooleanPatternAbsentAt input := by
      constructor
      · rintro ⟨span, token⟩; exact success ⟨_, _, .trueKeyword token⟩
      · rintro ⟨span, token⟩; exact success ⟨_, _, .falseKeyword token⟩
    rcases rejectAtReports_total source endByte { head := .expression, tail := [] }
      .expression input with ⟨diagnostic, reported⟩
    exact Or.inr ⟨input, diagnostic, [], absent, rfl, reported, rfl⟩

theorem LiteralExpressionTraceRejects.disjoint_success
    {input rejected after : Remainder} {diagnostic : ParseDiagnostic} {value : Syntax.Expr}
    {rejectTrace successTrace : List ParseDiagnostic}
    (rejectedTrace : LiteralExpressionTraceRejects source endByte input rejected diagnostic rejectTrace)
    (successful : LiteralExpressionTraceParses source endByte input value after successTrace) : False := by
  cases successful.1 with
  | parsed literalParsed => exact rejectedTrace.1.disjointOrdinary ⟨_, after, literalParsed⟩

theorem literalExpressionTrace_outcome_total (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ value after trace, LiteralExpressionTraceParses source endByte input value after trace) ∨
    ∃ rejected diagnostic trace,
      LiteralExpressionTraceRejects source endByte input rejected diagnostic trace := by
  rcases coreLiteralTrace_outcome_total source endByte input with successful | rejected
  · rcases successful with ⟨literal, after, trace, literalParsed, events⟩
    exact Or.inl ⟨_, after, trace, .parsed literalParsed, events⟩
  · exact Or.inr rejected

end Solcore.Syntax.DeclarativeGrammar
