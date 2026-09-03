import Solcore.Syntax.DeclarativeYulExpressionCoreExactnessProperties
import Solcore.Syntax.DeclarativeYulExpressionOrdinaryOutcomeProperties

/-! Exact recovery spans and full outcomes of one inline-Yul expression layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A recovery scan fixes its error AST when both accumulated spans are fixed. -/
theorem YulExpressionRecoveryScanParses.value_unique :
    ∀ {first last : SourceSpan} {input : Remainder}
      {left right : Syntax.YulExpr} {afterLeft afterRight : Remainder},
      YulExpressionRecoveryScanParses first last input left afterLeft →
      YulExpressionRecoveryScanParses first last input right afterRight →
      left = right := by
  intro first last input left right afterLeft afterRight leftParsed
  induction leftParsed generalizing right afterRight with
  | stop leftStops =>
      intro rightParsed
      cases rightParsed with
      | stop => rfl
      | next rightContinues _ _ => exact False.elim (rightContinues leftStops)
  | next leftContinues leftCurrent leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | stop rightStops => exact False.elim (leftContinues rightStops)
      | next _ rightCurrent rightTail =>
          have currentEq := leftCurrent.token_unique rightCurrent
          cases currentEq
          exact inductionHypothesis rightTail

/-- A recovery scan fixes both the error AST and its complete remainder. -/
theorem YulExpressionRecoveryScanParses.result_unique
    {first last : SourceSpan} {input : Remainder}
    {left right : Syntax.YulExpr} {afterLeft afterRight : Remainder}
    (leftParsed : YulExpressionRecoveryScanParses first last input left afterLeft)
    (rightParsed : YulExpressionRecoveryScanParses first last input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- An ordinary recovering Yul-expression layer fixes its complete AST. -/
theorem YulExpressionLayerOrdinaryParses.value_unique
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input : Remainder} {left right : Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulExpressionLayerOrdinaryParses ordinaryParses nestedRejects
      input left afterLeft)
    (rightParsed : YulExpressionLayerOrdinaryParses ordinaryParses nestedRejects
      input right afterRight) : left = right := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore => exact leftCore.value_unique outcomes rightCore
      | recovered rightRejected _ _ _ =>
          exact False.elim (rightRejected.disjointOrdinary ⟨_, _, leftCore⟩)
  | recovered leftRejected _ leftCurrent leftScan =>
      cases rightParsed with
      | core rightCore =>
          exact False.elim (leftRejected.disjointOrdinary ⟨_, _, rightCore⟩)
      | recovered _ _ rightCurrent rightScan =>
          have currentEq := leftCurrent.token_unique rightCurrent
          cases currentEq
          exact leftScan.value_unique rightScan

/-- An ordinary recovering Yul-expression layer fixes its AST and remainder. -/
theorem YulExpressionLayerOrdinaryParses.result_unique
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input : Remainder} {left right : Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulExpressionLayerOrdinaryParses ordinaryParses nestedRejects
      input left afterLeft)
    (rightParsed : YulExpressionLayerOrdinaryParses ordinaryParses nestedRejects
      input right afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique outcomes rightParsed,
    leftParsed.output_unique outcomes.toDeterministicOutcomeSpec rightParsed⟩

/-- Every Yul-expression rejection has the same non-consuming endpoint. -/
theorem YulExpressionRejects.output_unique {input left right : Remainder}
    (leftRejected : YulExpressionRejects input left)
    (rightRejected : YulExpressionRejects input right) : left = right := by
  rw [leftRejected.output_eq, rightRejected.output_eq]

/-- One recovering Yul-expression layer preserves exact ordinary outcomes. -/
theorem yulExpressionLayerExactOutcomeSpec
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects) :
    ExactDeterministicOutcomeSpec
      (YulExpressionLayerOrdinaryParses ordinaryParses nestedRejects)
      YulExpressionRejects where
  toDeterministicOutcomeSpec :=
    yulExpressionDeterministicOutcomeSpec outcomes.toDeterministicOutcomeSpec
  successValueUnique := YulExpressionLayerOrdinaryParses.value_unique outcomes
  rejectOutputUnique := YulExpressionRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
