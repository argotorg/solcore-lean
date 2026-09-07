import Solcore.Syntax.DeclarativeBlockStatementTraceGrammar
import Solcore.Syntax.DeclarativeCoreBlockTraceExactnessProperties

/-! Independent ordinary erasure and exact block-statement outcome laws.
The raw block's complete AST, remainder, reports, and event order are retained. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
    Remainder → List ParseDiagnostic → Prop}
  {statementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
  {ordinaryRejects : Remainder → Remainder → Prop}
  {source : SourceId} {endByte : Nat}

theorem BlockStatementTraceParses.ordinary
    (erases : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace → statementOrdinary input statement output)
    {input output : Remainder} {statement : Syntax.Statement} {trace : List ParseDiagnostic}
    (parsed : BlockStatementTraceParses statementTrace source endByte input statement output trace) :
    BlockStatementOrdinaryParses statementOrdinary input statement output := by
  cases parsed with
  | parsed body => exact .parsed (body.ordinary erases)

theorem BlockStatementTraceRejects.ordinary
    (successErases : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace → statementOrdinary input statement output)
    (rejectErases : ∀ {input rejected diagnostic trace},
      statementRejects source endByte input rejected diagnostic trace → ordinaryRejects input rejected)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : BlockStatementTraceRejects statementTrace statementRejects source endByte
      input rejected diagnostic trace) : BlockStatementRejects statementOrdinary ordinaryRejects input rejected := by
  cases rejection with
  | rejected body => exact body.ordinary successErases rejectErases

theorem BlockStatementTraceParses.cursor_lt
    {input output : Remainder} {statement : Syntax.Statement} {trace : List ParseDiagnostic}
    (parsed : BlockStatementTraceParses statementTrace source endByte input statement output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed body => exact body.cursor_lt

theorem BlockStatementTraceParses.output_cursor_le_endIndex
    {input output : Remainder} {statement : Syntax.Statement} {trace : List ParseDiagnostic}
    (parsed : BlockStatementTraceParses statementTrace source endByte input statement output trace) :
    output.cursor ≤ output.endIndex := by
  cases parsed with
  | parsed body => exact body.output_cursor_le_endIndex

theorem BlockStatementTraceParses.output_window
    (statementWindow : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {statement : Syntax.Statement} {trace : List ParseDiagnostic}
    (parsed : BlockStatementTraceParses statementTrace source endByte input statement output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed body => exact body.output_window statementWindow

theorem BlockStatementTraceParses.result_unique
    (successUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      statementTrace source endByte input left afterLeft leftTrace →
      statementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Syntax.Statement}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : BlockStatementTraceParses statementTrace source endByte input left afterLeft leftTrace)
    (rightParsed : BlockStatementTraceParses statementTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed leftBody =>
      cases rightParsed with
      | parsed rightBody =>
          rcases leftBody.result_unique successUnique rightBody with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem BlockStatementTraceRejects.result_unique
    (statements : StatementTraceExactOutcomeSpec statementTrace statementRejects source endByte)
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : BlockStatementTraceRejects statementTrace statementRejects source endByte
      input afterLeft leftReport leftTrace)
    (right : BlockStatementTraceRejects statementTrace statementRejects source endByte
      input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | rejected leftBody =>
      cases right with
      | rejected rightBody =>
          exact leftBody.result_unique statements.successResultUnique statements.rejectResultUnique
            statements.successRejectDisjoint rightBody

theorem BlockStatementTraceRejects.disjoint_success
    (statements : StatementTraceExactOutcomeSpec statementTrace statementRejects source endByte)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : BlockStatementTraceRejects statementTrace statementRejects source endByte
      input rejected diagnostic trace) :
    ¬ ∃ statement output events,
      BlockStatementTraceParses statementTrace source endByte input statement output events := by
  rintro ⟨_, _, _, parsed⟩
  cases rejection with
  | rejected bodyRejected =>
      cases parsed with
      | parsed bodyParsed =>
          exact bodyRejected.disjoint_success statements.successResultUnique
            statements.successRejectDisjoint ⟨_, _, _, bodyParsed⟩

theorem blockStatementTraceExactOutcomeSpec
    (statements : StatementTraceExactOutcomeSpec statementTrace statementRejects source endByte) :
    StatementTraceExactOutcomeSpec (BlockStatementTraceParses statementTrace)
      (BlockStatementTraceRejects statementTrace statementRejects) source endByte where
  successResultUnique := BlockStatementTraceParses.result_unique statements.successResultUnique
  rejectResultUnique := BlockStatementTraceRejects.result_unique statements
  successRejectDisjoint := BlockStatementTraceRejects.disjoint_success statements

end Solcore.Syntax.DeclarativeGrammar
