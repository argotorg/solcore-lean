import Solcore.Syntax.DeclarativeCoreLambdaParameterCoreValueProperties
import Solcore.Syntax.DeclarativeCoreLambdaParameterPublicOutcomeProperties
import Solcore.Syntax.DeclarativeCoreTypeExactnessProperties
import Solcore.Syntax.DeclarativeFunctionParameterRecoveryExactnessProperties

/-! Exact outcomes for recovery-aware ordinary lambda parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Lambda recovery preserves the unique span of malformed named recovery. -/
theorem LambdaParameterRecoveryParses.value_unique
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : LambdaParameterRecoveryParses input left afterLeft)
    (rightParsed : LambdaParameterRecoveryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | recovered leftRecovery =>
      cases rightParsed with
      | recovered rightRecovery =>
          have parameterEq := leftRecovery.value_unique rightRecovery
          subst parameterEq
          rfl

/-- Complete lambda recovery fixes its error AST and final remainder. -/
theorem LambdaParameterRecoveryParses.result_unique
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : LambdaParameterRecoveryParses input left afterLeft)
    (rightParsed : LambdaParameterRecoveryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Retagging named-parameter recovery gives exact lambda recovery outcomes. -/
theorem lambdaParameterRecoveryExactOutcomeSpec :
    ExactDeterministicOutcomeSpec LambdaParameterRecoveryParses
      LambdaParameterRecoveryRejects where
  toDeterministicOutcomeSpec := lambdaParameterRecoveryDeterministicOutcomeSpec
  successValueUnique := LambdaParameterRecoveryParses.value_unique
  rejectOutputUnique := FunctionParameterRecoveryRejects.output_unique

/-- Exact type outcomes make direct and recovered lambda values unique. -/
theorem LambdaParameterOrdinaryParses.value_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : LambdaParameterOrdinaryParses typeOrdinary typeRejects
      input left afterLeft)
    (rightParsed : LambdaParameterOrdinaryParses typeOrdinary typeRejects
      input right afterRight) : left = right := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore =>
          exact leftCore.value_unique typeOutcomes rightCore
      | recovered rightRejected rightContinues rightRecovery =>
          rcases rightRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim
            (lambdaParameterCoreDeterministicOutcomeSpec
              typeOutcomes.toDeterministicOutcomeSpec
              |>.successRejectDisjoint coreRejected ⟨_, _, leftCore⟩)
  | recovered leftRejected leftContinues leftRecovery =>
      cases rightParsed with
      | core rightCore =>
          rcases leftRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim
            (lambdaParameterCoreDeterministicOutcomeSpec
              typeOutcomes.toDeterministicOutcomeSpec
              |>.successRejectDisjoint coreRejected ⟨_, _, rightCore⟩)
      | recovered rightRejected rightContinues rightRecovery =>
          exact leftRecovery.value_unique rightRecovery

/-- Recovery-aware lambda success fixes the complete AST and remainder. -/
theorem LambdaParameterOrdinaryParses.result_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : LambdaParameterOrdinaryParses typeOrdinary typeRejects
      input left afterLeft)
    (rightParsed : LambdaParameterOrdinaryParses typeOrdinary typeRejects
      input right afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique typeOutcomes rightParsed,
    leftParsed.output_unique typeOutcomes.toDeterministicOutcomeSpec
      rightParsed⟩

/-- Every public lambda rejection has the same nonconsuming endpoint. -/
theorem LambdaParameterRejects.output_unique
    {typeRejects : Remainder → Remainder → Prop}
    {input left right : Remainder}
    (leftRejected : LambdaParameterRejects typeRejects input left)
    (rightRejected : LambdaParameterRejects typeRejects input right) :
    left = right := by
  rw [leftRejected.output_eq, rightRejected.output_eq]

/-- Exact type outcomes lift through ordinary lambda parameters and recovery. -/
theorem lambdaParameterExactOutcomeSpec
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects) :
    ExactDeterministicOutcomeSpec
      (LambdaParameterOrdinaryParses typeOrdinary typeRejects)
      (LambdaParameterRejects typeRejects) where
  toDeterministicOutcomeSpec := lambdaParameterDeterministicOutcomeSpec
    typeOutcomes.toDeterministicOutcomeSpec
  successValueUnique := LambdaParameterOrdinaryParses.value_unique typeOutcomes
  rejectOutputUnique := LambdaParameterRejects.output_unique

/-- Public recursive Core types discharge every lambda-parameter premise. -/
theorem lambdaParameterPublicExactOutcomeSpec :
    ExactDeterministicOutcomeSpec
      (LambdaParameterOrdinaryParses TypeExprOrdinaryParses TypeExprRejects)
      (LambdaParameterRejects TypeExprRejects) :=
  lambdaParameterExactOutcomeSpec typeExprExactOutcomeSpec

end Solcore.Syntax.DeclarativeGrammar
