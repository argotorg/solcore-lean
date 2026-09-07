import Solcore.Syntax.DeclarativeExpressionTraceOutcomeSpec
import Solcore.Syntax.DeclarativeReturnStatementRejectionTraceProperties
import Solcore.Syntax.DeclarativeCoreBlockTraceExactnessProperties

/-! Independent expression trace laws lift through return statements and
restricted raw/isolated blocks. Conditional outcome existence is proved apart. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {expressionTrace : SourceId → Nat → Remainder → Syntax.Expr →
    Remainder → List ParseDiagnostic → Prop}
  {expressionRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem returnStatementTraceExactOutcomeSpec
    (expressions : ExpressionTraceExactOutcomeSpec expressionTrace expressionRejects source endByte) :
    StatementTraceExactOutcomeSpec (ReturnStatementTraceParses expressionTrace)
      (ReturnStatementTraceRejects expressionTrace expressionRejects) source endByte where
  successResultUnique := ReturnStatementTraceParses.result_unique expressions.successResultUnique
  rejectResultUnique := ReturnStatementTraceRejects.result_unique expressions.successResultUnique
    expressions.rejectResultUnique expressions.successRejectDisjoint
  successRejectDisjoint := ReturnStatementTraceRejects.disjoint_success
    expressions.successResultUnique expressions.successRejectDisjoint

/-- This describes blocks restricted to return statements; no mixed Core
statement-dispatch or concrete expression trace claim is implicit. -/
theorem returnCoreBlockTraceExactOutcomeSpec (policy : CoreBlockTailPolicy)
    (expressions : ExpressionTraceExactOutcomeSpec expressionTrace expressionRejects source endByte) :
    BlockTraceExactOutcomeSpec (CoreBlockTraceParses (ReturnStatementTraceParses expressionTrace) policy)
      (CoreBlockTraceRejects (ReturnStatementTraceParses expressionTrace)
        (ReturnStatementTraceRejects expressionTrace expressionRejects) policy) source endByte :=
  coreBlockTraceExactOutcomeSpec policy (returnStatementTraceExactOutcomeSpec expressions)

theorem isolatedReturnCoreBlockTraceExactOutcomeSpec (policy : CoreBlockTailPolicy)
    (expressions : ∀ childEndByte,
      ExpressionTraceExactOutcomeSpec expressionTrace expressionRejects source childEndByte) :
    BlockTraceExactOutcomeSpec
      (IsolatedBlockTraceParses (CoreBlockTraceParses (ReturnStatementTraceParses expressionTrace) policy)
        (CoreBlockTraceRejects (ReturnStatementTraceParses expressionTrace)
          (ReturnStatementTraceRejects expressionTrace expressionRejects) policy))
      (IsolatedBlockTraceRejects (CoreBlockTraceRejects (ReturnStatementTraceParses expressionTrace)
        (ReturnStatementTraceRejects expressionTrace expressionRejects) policy)) source endByte :=
  isolatedCoreBlockTraceExactOutcomeSpec policy (fun childEndByte =>
    returnStatementTraceExactOutcomeSpec (expressions childEndByte))

/-- The semicolon guard either skips the expression or uses one of its
independent outcomes. No uniqueness, cursor, or window premise is needed. -/
theorem optionalReturnValueTrace_exists_outcome
    (expressions : ExpressionTraceOutcomeExists expressionTrace expressionRejects source endByte)
    (input : Remainder) :
    (∃ value output trace,
      OptionalReturnValueTraceParses expressionTrace source endByte input value output trace) ∨
    (∃ rejected diagnostic trace,
      OptionalReturnValueTraceRejects expressionRejects source endByte input rejected diagnostic trace) := by
  by_cases current : ∃ span, TokenAt input.tokens input.endIndex input.cursor
      { span, value := .symbol .semicolon }
  · rcases current with ⟨span, current⟩
    exact Or.inl ⟨none, input, [], .absent span current⟩
  · rcases expressions input with successful | rejected
    · rcases successful with ⟨value, output, trace, parsed⟩
      exact Or.inl ⟨some value, output, trace, .present current parsed⟩
    · rcases rejected with ⟨output, diagnostic, trace, rejection⟩
      exact Or.inr ⟨output, diagnostic, trace, .expressionRejected current rejection⟩

/-- Return outcome existence follows from expression existence alone, keeping
the exact first report and all expression events. It does not assert block totality. -/
theorem returnStatementTrace_exists_outcome
    (expressions : ExpressionTraceOutcomeExists expressionTrace expressionRejects source endByte)
    (input : Remainder) :
    (∃ statement output trace,
      ReturnStatementTraceParses expressionTrace source endByte input statement output trace) ∨
    (∃ rejected diagnostic trace,
      ReturnStatementTraceRejects expressionTrace expressionRejects source endByte
        input rejected diagnostic trace) := by
  by_cases current : ∃ span, TokenAt input.tokens input.endIndex input.cursor
      { span, value := .keyword .returnKw }
  · rcases current with ⟨markerSpan, current⟩
    let afterMarker : Remainder := { input with cursor := input.cursor + 1 }
    have marker : ExactTokenParses (.keyword .returnKw) input markerSpan afterMarker := ⟨current, rfl⟩
    rcases optionalReturnValueTrace_exists_outcome expressions afterMarker with successful | rejected
    · rcases successful with ⟨value, afterValue, trace, parsed⟩
      by_cases semicolon : ∃ span, TokenAt afterValue.tokens afterValue.endIndex afterValue.cursor
          { span, value := .symbol .semicolon }
      · rcases semicolon with ⟨semicolonSpan, semicolon⟩
        exact Or.inl ⟨_, _, trace, .parsed markerSpan semicolonSpan marker parsed ⟨semicolon, rfl⟩⟩
      · rcases rejectAtReports_total source endByte { head := .symbol .semicolon, tail := [] }
            .statement afterValue with ⟨diagnostic, reported⟩
        exact Or.inr ⟨afterValue, diagnostic, trace,
          .semicolonRejected markerSpan marker parsed semicolon reported⟩
    · rcases rejected with ⟨output, diagnostic, trace, rejection⟩
      exact Or.inr ⟨output, diagnostic, trace, .valueRejected markerSpan marker rejection⟩
  · rcases rejectAtReports_total source endByte { head := .keyword .returnKw, tail := [] }
        .statement input with ⟨diagnostic, reported⟩
    exact Or.inr ⟨input, diagnostic, [], .markerRejected current reported⟩

end Solcore.Syntax.DeclarativeGrammar
