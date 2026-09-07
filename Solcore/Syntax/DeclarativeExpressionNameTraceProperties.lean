import Solcore.Syntax.DeclarativeExpressionNameTraceGrammar
import Solcore.Syntax.DeclarativeLiteralDiagnosticTraceProperties
import Solcore.Syntax.DeclarativeIdentifierTraceProperties
import Solcore.Syntax.DeclarativeExpressionTraceOutcomeSpec

/-! Independent exactness, ordinary erasure, and total Boolean-first name traces. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

theorem ExpressionNameTraceParses.ordinary
    {input output : Remainder} {name : Syntax.Identifier} {trace : List ParseDiagnostic}
    (parsed : ExpressionNameTraceParses source endByte input name output trace) :
    ExpressionNameParses input name output := by
  cases parsed with
  | boolean parsed => exact .boolean parsed.1
  | identifier absent parsed => exact .identifier absent.1 absent.2 (identifierTraceParses_iff.mp parsed).1

theorem ExpressionNameTraceParses.output_eq
    {input output : Remainder} {name : Syntax.Identifier} {trace : List ParseDiagnostic}
    (parsed : ExpressionNameTraceParses source endByte input name output trace) :
    output = { input with cursor := input.cursor + 1 } := by
  cases parsed with
  | boolean parsed => cases parsed.1 <;> rfl
  | identifier _ parsed =>
      have ordinary := (identifierTraceParses_iff.mp parsed).1
      rcases output with ⟨tokens, endIndex, cursor⟩
      rcases ordinary.2 with ⟨rfl, rfl, rfl⟩
      rfl

theorem ExpressionNameTraceRejects.ordinary
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : ExpressionNameTraceRejects source endByte input rejected diagnostic trace) :
    ExpressionNameRejects input rejected := by
  rcases traced with ⟨booleanAbsent, identifierRejected, _, _⟩
  cases identifierRejected with
  | absent nameAbsent => exact .absent ⟨booleanAbsent.1, booleanAbsent.2, nameAbsent⟩

theorem ExpressionNameTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.Identifier}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ExpressionNameTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : ExpressionNameTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | boolean left =>
      cases rightParsed with
      | boolean right => exact left.result_unique right
      | identifier absent _ =>
          cases left.1 with
          | trueKeyword token => exact False.elim (absent.1 ⟨_, token⟩)
          | falseKeyword token => exact False.elim (absent.2 ⟨_, token⟩)
  | identifier absent left =>
      cases rightParsed with
      | identifier _ right => exact left.result_unique right
      | boolean right =>
          cases right.1 with
          | trueKeyword token => exact False.elim (absent.1 ⟨_, token⟩)
          | falseKeyword token => exact False.elim (absent.2 ⟨_, token⟩)

theorem ExpressionNameTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {left right : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : ExpressionNameTraceRejects source endByte input afterLeft left leftTrace)
    (rightRejected : ExpressionNameTraceRejects source endByte input afterRight right rightTrace) :
    afterLeft = afterRight ∧ left = right ∧ leftTrace = rightTrace := by
  rcases leftRejected with ⟨_, leftOrdinary, leftReport, leftEvents⟩
  rcases rightRejected with ⟨_, rightOrdinary, rightReport, rightEvents⟩
  cases leftOrdinary
  cases rightOrdinary
  exact ⟨rfl, leftReport.diagnostic_unique rightReport, leftEvents.trans rightEvents.symm⟩

theorem ExpressionNameTraceRejects.disjoint_success
    {input rejected after : Remainder} {diagnostic : ParseDiagnostic} {name : Syntax.Identifier}
    {rejectTrace successTrace : List ParseDiagnostic}
    (rejectedTrace : ExpressionNameTraceRejects source endByte input rejected diagnostic rejectTrace)
    (successful : ExpressionNameTraceParses source endByte input name after successTrace) : False :=
  rejectedTrace.ordinary.disjointOrdinary ⟨name, after, successful.ordinary⟩

theorem expressionNameTrace_outcome_total (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ name after trace, ExpressionNameTraceParses source endByte input name after trace) ∨
    ∃ rejected diagnostic trace,
      ExpressionNameTraceRejects source endByte input rejected diagnostic trace := by
  classical
  rcases booleanIdentifierTrace_outcome_total source endByte input with boolean | noBoolean
  · rcases boolean with ⟨name, after, trace, parsed⟩
    exact Or.inl ⟨name, after, trace, .boolean parsed⟩
  · rcases noBoolean with ⟨_, _, _, absent, _, _, _⟩
    by_cases success : ∃ name after, IdentifierParses input name after
    · rcases success with ⟨name, after, ordinary⟩
      rcases identifierDiagnosticTrace_total name with ⟨trace, checked⟩
      exact Or.inl ⟨name, after, trace, .identifier absent (.parsed ordinary checked)⟩
    · have noName : IdentifierAbsentAt input := by
        rintro ⟨span, text, token⟩
        exact success ⟨{ span, value := text }, { input with cursor := input.cursor + 1 },
          token, rfl, rfl, rfl⟩
      rcases rejectAtReports_total source endByte { head := .identifier, tail := [] }
        .expression input with ⟨diagnostic, reported⟩
      exact Or.inr ⟨input, diagnostic, [], absent, .absent noName, reported, rfl⟩

theorem IdentifierExpressionTraceParses.ordinary
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : IdentifierExpressionTraceParses source endByte input value output trace) :
    IdentifierExpressionParses input value output := by
  cases parsed with
  | parsed name => exact .parsed name.ordinary

theorem IdentifierExpressionTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.Expr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : IdentifierExpressionTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : IdentifierExpressionTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed leftName =>
      cases rightParsed with
      | parsed rightName =>
          rcases leftName.result_unique rightName with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem identifierExpressionTrace_exactOutcomeSpec (source : SourceId) (endByte : Nat) :
    ExpressionTraceExactOutcomeSpec IdentifierExpressionTraceParses IdentifierExpressionTraceRejects
      source endByte where
  successResultUnique := IdentifierExpressionTraceParses.result_unique
  rejectResultUnique := ExpressionNameTraceRejects.result_unique
  successRejectDisjoint := by
    rintro input rejected diagnostic trace rejecting ⟨value, after, events, successful⟩
    cases successful with
    | parsed name => exact rejecting.disjoint_success name

theorem identifierExpressionTrace_outcomeExists (source : SourceId) (endByte : Nat) :
    ExpressionTraceOutcomeExists IdentifierExpressionTraceParses IdentifierExpressionTraceRejects
      source endByte := by
  intro input
  rcases expressionNameTrace_outcome_total source endByte input with successful | rejected
  · rcases successful with ⟨name, after, trace, parsed⟩
    exact Or.inl ⟨_, after, trace, .parsed parsed⟩
  · exact Or.inr rejected

end Solcore.Syntax.DeclarativeGrammar
