import Solcore.Syntax.DeclarativeCoreExpressionAtomPublicOutcomeProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact recovery ASTs and public Core atom rewind outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A fixed recovery prefix determines the complete diagnosed error AST and span. -/
theorem ExpressionAtomRecoveryScanParses.value_unique
    {first last : SourceSpan} {input : Remainder}
    {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionAtomRecoveryScanParses first last input left afterLeft)
    (rightParsed : ExpressionAtomRecoveryScanParses first last input right afterRight) :
    left = right := by
  induction leftParsed generalizing right afterRight with
  | stop leftStops =>
      cases rightParsed with
      | stop => rfl
      | next rightContinues _ _ => exact False.elim (rightContinues leftStops)
  | next leftContinues leftToken leftTail ih =>
      cases rightParsed with
      | stop rightStops => exact False.elim (leftContinues rightStops)
      | next _ rightToken rightTail =>
          have tokenEq := leftToken.token_unique rightToken
          cases tokenEq
          exact ih rightTail

/-- A complete recovery fixes its initial token and exact error AST. -/
theorem ExpressionAtomRecoveryParses.value_unique
    {input : Remainder} {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionAtomRecoveryParses input left afterLeft)
    (rightParsed : ExpressionAtomRecoveryParses input right afterRight) : left = right := by
  cases leftParsed with
  | recovered leftToken leftScan =>
      cases rightParsed with
      | recovered rightToken rightScan =>
          have tokenEq := leftToken.token_unique rightToken
          cases tokenEq
          exact leftScan.value_unique rightScan

/-- Atom recovery has exact successful error ASTs and non-consuming rejections. -/
theorem expressionAtomRecoveryExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ExpressionAtomRecoveryParses ExpressionAtomRecoveryRejects where
  toDeterministicOutcomeSpec := expressionAtomRecoveryDeterministicOutcomeSpec
  successValueUnique := ExpressionAtomRecoveryParses.value_unique
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    rw [leftRejected.output_eq, rightRejected.output_eq]

/-- Public atom rewind preserves exact successful ASTs without needing raw core
rejection endpoints to be unique. -/
theorem ExpressionAtomOrdinaryParses.value_unique_of_success
    {coreOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec coreOrdinary coreRejects)
    (values : ∀ {input left right afterLeft afterRight},
      coreOrdinary input left afterLeft → coreOrdinary input right afterRight → left = right)
    {input : Remainder} {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionAtomOrdinaryParses coreOrdinary coreRejects input left afterLeft)
    (rightParsed : ExpressionAtomOrdinaryParses coreOrdinary coreRejects input right afterRight) :
    left = right := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore => exact values leftCore rightCore
      | recovered rightRejected _ _ =>
          rcases rightRejected with ⟨failed, rejected, tokensEq, endIndexEq⟩
          exact False.elim (outcomes.successRejectDisjoint rejected ⟨_, _, leftCore⟩)
  | recovered leftRejected _ leftRecovery =>
      cases rightParsed with
      | core rightCore =>
          rcases leftRejected with ⟨failed, rejected, tokensEq, endIndexEq⟩
          exact False.elim (outcomes.successRejectDisjoint rejected ⟨_, _, rightCore⟩)
      | recovered _ _ rightRecovery => exact leftRecovery.value_unique rightRecovery

/-- Rewinding all public rejection paths gives one complete atom endpoint. -/
theorem ExpressionAtomRejects.output_unique
    {coreRejects : Remainder → Remainder → Prop} {input left right : Remainder}
    (leftRejected : ExpressionAtomRejects coreRejects input left)
    (rightRejected : ExpressionAtomRejects coreRejects input right) : left = right := by
  rw [leftRejected.output_eq, rightRejected.output_eq]

/-- Exact core success values suffice for fully exact public atom outcomes. -/
theorem expressionAtomExactOutcomeSpecOfSuccess
    {coreOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec coreOrdinary coreRejects)
    (values : ∀ {input left right afterLeft afterRight},
      coreOrdinary input left afterLeft → coreOrdinary input right afterRight → left = right) :
    ExactDeterministicOutcomeSpec (ExpressionAtomOrdinaryParses coreOrdinary coreRejects)
      (ExpressionAtomRejects coreRejects) where
  toDeterministicOutcomeSpec := expressionAtomDeterministicOutcomeSpec outcomes
  successValueUnique := ExpressionAtomOrdinaryParses.value_unique_of_success outcomes values
  rejectOutputUnique := ExpressionAtomRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
