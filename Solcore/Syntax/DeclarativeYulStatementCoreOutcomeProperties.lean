import Solcore.Syntax.DeclarativeYulStatementCorePriorityProperties

/-! Deterministic outcome laws for the prioritized Yul statement core. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- An ordinary core success retains its exact negative prefix. -/
theorem YulStatementCoreOrdinaryParsesAt.priority
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {stage input statement output}
    (parsed : YulStatementCoreOrdinaryParsesAt statementOrdinary
      statementRejects stage input statement output) :
    YulStatementCorePrefixAbsent input stage := by
  cases parsed <;> assumption

/-- An ordinary core success retains positive evidence for its selected
guard; the final fallback guard is trivially true. -/
theorem YulStatementCoreOrdinaryParsesAt.guard
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {stage input statement output}
    (parsed : YulStatementCoreOrdinaryParsesAt statementOrdinary
      statementRejects stage input statement output) :
    YulStatementCoreGuardAt input stage := by
  cases parsed <;> simp_all [YulStatementCoreGuardAt]

/-- An exact core rejection retains its exact negative prefix. -/
theorem YulStatementCoreRejectsAt.priority
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {stage input rejected}
    (rejection : YulStatementCoreRejectsAt statementOrdinary statementRejects
      stage input rejected) :
    YulStatementCorePrefixAbsent input stage := by
  cases rejection <;> assumption

/-- An exact core rejection retains positive evidence for its selected
guard; the final fallback guard is trivially true. -/
theorem YulStatementCoreRejectsAt.guard
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {stage input rejected}
    (rejection : YulStatementCoreRejectsAt statementOrdinary statementRejects
      stage input rejected) :
    YulStatementCoreGuardAt input stage := by
  cases rejection <;> simp_all [YulStatementCoreGuardAt]

/-- Ordinary core success has a unique output remainder. -/
theorem YulStatementCoreOrdinaryParses.output_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulStatementCoreOrdinaryParses statementOrdinary
      statementRejects input left afterLeft)
    (rightParsed : YulStatementCoreOrdinaryParses statementOrdinary
      statementRejects input right afterRight) : afterLeft = afterRight := by
  rcases leftParsed with ⟨leftStage, leftParsed⟩
  rcases rightParsed with ⟨rightStage, rightParsed⟩
  have selected := yulStatementCore_selectedStage_unique leftParsed.priority
    leftParsed.guard rightParsed.priority rightParsed.guard
  subst rightStage
  cases leftParsed <;> cases rightParsed
  all_goals first
    | exact TransactionalFallbackOrdinaryParses.output_unique
        (yulBlockStatementDeterministicOutcomeSpec statementOutcomes)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          (by assumption)
    | exact TransactionalFallbackOrdinaryParses.output_unique
        yulLetStatementDeterministicOutcomeSpec
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          (by assumption)
    | exact TransactionalFallbackOrdinaryParses.output_unique
        (yulIfStatementDeterministicOutcomeSpec statementOutcomes)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          (by assumption)
    | exact TransactionalFallbackOrdinaryParses.output_unique
        (yulForStatementDeterministicOutcomeSpec statementOutcomes)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          (by assumption)
    | exact TransactionalFallbackOrdinaryParses.output_unique
        (yulSwitchStatementDeterministicOutcomeSpec statementOutcomes)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          (by assumption)
    | exact TransactionalFallbackOrdinaryParses.output_unique
        (yulFunctionStatementDeterministicOutcomeSpec statementOutcomes)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          (by assumption)
    | exact TransactionalFallbackOrdinaryParses.output_unique
        yulReturnBuiltinDeterministicOutcomeSpec
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          (by assumption)
    | exact TransactionalFallbackOrdinaryParses.output_unique
        (yulControlTokenDeterministicOutcomeSpec .leaveKw .leave)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          (by assumption)
    | exact TransactionalFallbackOrdinaryParses.output_unique
        (yulControlTokenDeterministicOutcomeSpec .breakKw .break)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          (by assumption)
    | exact TransactionalFallbackOrdinaryParses.output_unique
        (yulControlTokenDeterministicOutcomeSpec .continueKw .continue)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          (by assumption)
    | exact yulNameStatementDeterministicOutcomeSpec.successOutputUnique
        (by assumption) (by assumption)
    | exact yulExpressionStatementDeterministicOutcomeSpec.successOutputUnique
        (by assumption) (by assumption)

/-- Exact core rejection excludes every ordinary core success. -/
theorem YulStatementCoreRejects.disjointOrdinary
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : YulStatementCoreRejects statementOrdinary statementRejects
      input rejected) :
    ¬ ∃ statement output,
      YulStatementCoreOrdinaryParses statementOrdinary statementRejects input
        statement output := by
  rintro ⟨statement, output, successful⟩
  rcases rejection with ⟨rejectedStage, rejection⟩
  rcases successful with ⟨successfulStage, successful⟩
  have selected := yulStatementCore_selectedStage_unique rejection.priority
    rejection.guard successful.priority successful.guard
  subst successfulStage
  cases rejection <;> cases successful
  all_goals first
    | exact TransactionalFallbackRejects.disjointOrdinary
        (yulBlockStatementDeterministicOutcomeSpec statementOutcomes)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          ⟨_, _, by assumption⟩
    | exact TransactionalFallbackRejects.disjointOrdinary
        yulLetStatementDeterministicOutcomeSpec
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          ⟨_, _, by assumption⟩
    | exact TransactionalFallbackRejects.disjointOrdinary
        (yulIfStatementDeterministicOutcomeSpec statementOutcomes)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          ⟨_, _, by assumption⟩
    | exact TransactionalFallbackRejects.disjointOrdinary
        (yulForStatementDeterministicOutcomeSpec statementOutcomes)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          ⟨_, _, by assumption⟩
    | exact TransactionalFallbackRejects.disjointOrdinary
        (yulSwitchStatementDeterministicOutcomeSpec statementOutcomes)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          ⟨_, _, by assumption⟩
    | exact TransactionalFallbackRejects.disjointOrdinary
        (yulFunctionStatementDeterministicOutcomeSpec statementOutcomes)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          ⟨_, _, by assumption⟩
    | exact TransactionalFallbackRejects.disjointOrdinary
        yulReturnBuiltinDeterministicOutcomeSpec
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          ⟨_, _, by assumption⟩
    | exact TransactionalFallbackRejects.disjointOrdinary
        (yulControlTokenDeterministicOutcomeSpec .leaveKw .leave)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          ⟨_, _, by assumption⟩
    | exact TransactionalFallbackRejects.disjointOrdinary
        (yulControlTokenDeterministicOutcomeSpec .breakKw .break)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          ⟨_, _, by assumption⟩
    | exact TransactionalFallbackRejects.disjointOrdinary
        (yulControlTokenDeterministicOutcomeSpec .continueKw .continue)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          ⟨_, _, by assumption⟩
    | exact yulNameStatementDeterministicOutcomeSpec.successRejectDisjoint
        (by assumption) ⟨_, _, by assumption⟩
    | exact yulExpressionStatementDeterministicOutcomeSpec
        |>.successRejectDisjoint (by assumption) ⟨_, _, by assumption⟩

/-- Construct the complete ordinary statement-core outcome contract. -/
theorem yulStatementCoreDeterministicOutcomeSpec
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects) :
    DeterministicOutcomeSpec
      (YulStatementCoreOrdinaryParses statementOrdinary statementRejects)
      (YulStatementCoreRejects statementOrdinary statementRejects) where
  successOutputUnique :=
    YulStatementCoreOrdinaryParses.output_unique statementOutcomes
  successRejectDisjoint :=
    YulStatementCoreRejects.disjointOrdinary statementOutcomes

end Solcore.Syntax.DeclarativeGrammar
