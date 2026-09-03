import Solcore.Syntax.DeclarativeTransactionalFallbackExactnessProperties
import Solcore.Syntax.DeclarativeYulFunctionExactnessProperties
import Solcore.Syntax.DeclarativeYulStatementBasicExactnessProperties
import Solcore.Syntax.DeclarativeYulStatementControlExactnessProperties
import Solcore.Syntax.DeclarativeYulStatementCoreOutcomeProperties
import Solcore.Syntax.DeclarativeYulSwitchExactnessProperties

/-! Exact AST and rejection outcomes of the prioritized Yul statement core. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Name-start assignment-or-expression choice fixes the complete selected AST. -/
theorem YulNameStatementOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulNameStatementOrdinaryParses input left afterLeft)
    (rightParsed : YulNameStatementOrdinaryParses input right afterRight) :
    left = right :=
  TransactionalFallbackOrdinaryParses.value_unique_of_success
    (fallbackParses := YulExpressionStatementOrdinaryParses)
    yulAssignmentDeterministicOutcomeSpec YulAssignmentOrdinaryParses.value_unique
    YulExpressionStatementOrdinaryParses.value_unique leftParsed rightParsed

private theorem recognized_value_unique
    {primaryParses : Remainder → Syntax.YulStmt → Remainder → Prop}
    {primaryRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec primaryParses primaryRejects)
    (values : ∀ {input left right afterLeft afterRight},
      primaryParses input left afterLeft → primaryParses input right afterRight → left = right)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulRecognizedStatementOrdinaryParses primaryParses primaryRejects
      input left afterLeft)
    (rightParsed : YulRecognizedStatementOrdinaryParses primaryParses primaryRejects
      input right afterRight) : left = right :=
  TransactionalFallbackOrdinaryParses.value_unique_of_success
    (fallbackParses := YulExpressionStatementOrdinaryParses) outcomes values
    YulExpressionStatementOrdinaryParses.value_unique leftParsed rightParsed

/-- Stage priority and exact primary ASTs fix the complete statement-core AST. -/
theorem YulStatementCoreOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulStatementCoreOrdinaryParses statementOrdinary statementRejects
      input left afterLeft)
    (rightParsed : YulStatementCoreOrdinaryParses statementOrdinary statementRejects
      input right afterRight) : left = right := by
  rcases leftParsed with ⟨leftStage, leftParsed⟩
  rcases rightParsed with ⟨rightStage, rightParsed⟩
  have selected := yulStatementCore_selectedStage_unique leftParsed.priority
    leftParsed.guard rightParsed.priority rightParsed.guard
  subst rightStage
  cases leftParsed <;> cases rightParsed
  all_goals first
    | exact recognized_value_unique
        (yulBlockStatementDeterministicOutcomeSpec outcomes.toDeterministicOutcomeSpec)
        (YulBlockStatementOrdinaryParses.value_unique outcomes) (by assumption) (by assumption)
    | exact recognized_value_unique yulLetStatementDeterministicOutcomeSpec
        YulLetStatementOrdinaryParses.value_unique (by assumption) (by assumption)
    | exact recognized_value_unique
        (yulIfStatementDeterministicOutcomeSpec outcomes.toDeterministicOutcomeSpec)
        (YulIfStatementOrdinaryParses.value_unique outcomes) (by assumption) (by assumption)
    | exact recognized_value_unique
        (yulForStatementDeterministicOutcomeSpec outcomes.toDeterministicOutcomeSpec)
        (YulForStatementOrdinaryParses.value_unique outcomes) (by assumption) (by assumption)
    | exact recognized_value_unique
        (yulSwitchStatementDeterministicOutcomeSpec outcomes.toDeterministicOutcomeSpec)
        (YulSwitchStatementOrdinaryParses.value_unique outcomes) (by assumption) (by assumption)
    | exact recognized_value_unique
        (yulFunctionStatementDeterministicOutcomeSpec outcomes.toDeterministicOutcomeSpec)
        (YulFunctionStatementOrdinaryParses.value_unique outcomes) (by assumption) (by assumption)
    | exact recognized_value_unique yulReturnBuiltinDeterministicOutcomeSpec
        YulReturnBuiltinOrdinaryParses.value_unique (by assumption) (by assumption)
    | exact recognized_value_unique (yulControlTokenDeterministicOutcomeSpec _ _)
        YulControlTokenOrdinaryParses.value_unique (by assumption) (by assumption)
    | exact YulNameStatementOrdinaryParses.value_unique (by assumption) (by assumption)
    | exact YulExpressionStatementOrdinaryParses.value_unique (by assumption) (by assumption)

private theorem transactional_output_eq
    {primaryRejects fallbackRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : TransactionalFallbackRejects primaryRejects fallbackRejects input rejected) :
    rejected = input := by
  cases rejection
  rfl

/-- Every core branch rejects at the original remainder after transactional rewind. -/
theorem YulStatementCoreRejects.output_eq
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : YulStatementCoreRejects statementOrdinary statementRejects
      input rejected) : rejected = input := by
  rcases rejection with ⟨stage, rejection⟩
  cases rejection
  all_goals first
    | exact YulExpressionStatementRejects.output_eq (by assumption)
    | exact transactional_output_eq (by assumption)

/-- Exact recursive statements give exact outcomes of the entire Yul core. -/
theorem yulStatementCoreExactOutcomeSpec
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects) :
    ExactDeterministicOutcomeSpec
      (YulStatementCoreOrdinaryParses statementOrdinary statementRejects)
      (YulStatementCoreRejects statementOrdinary statementRejects) where
  toDeterministicOutcomeSpec :=
    yulStatementCoreDeterministicOutcomeSpec outcomes.toDeterministicOutcomeSpec
  successValueUnique := YulStatementCoreOrdinaryParses.value_unique outcomes
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    rw [leftRejected.output_eq, rightRejected.output_eq]

end Solcore.Syntax.DeclarativeGrammar
