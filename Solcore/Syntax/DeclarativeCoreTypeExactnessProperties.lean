import Solcore.Syntax.DeclarativeCoreTypeDispatcherRejectionExactnessProperties
import Solcore.Syntax.DeclarativeCoreTypeOutcomeProperties
import Solcore.Syntax.DeclarativeCoreTypeCompositeSuccessExactnessProperties

/-! Full value and rejection-endpoint functionality for recursive Core types. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Recursive Core type success fixes its AST and final remainder. -/
theorem TypeExprParses.result_unique
    {input : Remainder} {left right : Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeExprParses input left afterLeft)
    (rightParsed : TypeExprParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Every executable recursion-fuel layer has exact success values and exact
rejection endpoints. -/
theorem typeExprExactOutcomeSpecWithFuel :
    ∀ fuel, ExactDeterministicOutcomeSpec TypeExprOrdinaryParses
      (TypeExprRejectsWithFuel fuel)
  | 0 => {
      toDeterministicOutcomeSpec := typeExprDeterministicOutcomeSpecWithFuel 0
      successValueUnique := TypeExprParses.value_unique
      rejectOutputUnique := by
        simp [TypeExprRejectsWithFuel]
    }
  | fuel + 1 =>
      let nestedOutcomes := typeExprExactOutcomeSpecWithFuel fuel
      {
        toDeterministicOutcomeSpec :=
          typeExprDeterministicOutcomeSpecWithFuel (fuel + 1)
        successValueUnique := TypeExprParses.value_unique
        rejectOutputUnique :=
          TypeExprCoreRejects.output_unique nestedOutcomes
      }

/-- Public Core type rejection has one exact first failing endpoint. -/
theorem TypeExprRejects.output_unique
    {input left right : Remainder}
    (leftRejects : TypeExprRejects input left)
    (rightRejects : TypeExprRejects input right) : left = right :=
  (typeExprExactOutcomeSpecWithFuel
    (typeExprPublicFuel input)).rejectOutputUnique leftRejects rightRejects

/-- The public recursive Core type grammar has fully exact ordinary outcomes. -/
theorem typeExprExactOutcomeSpec :
    ExactDeterministicOutcomeSpec TypeExprOrdinaryParses TypeExprRejects where
  toDeterministicOutcomeSpec := typeExprDeterministicOutcomeSpec
  successValueUnique := TypeExprParses.value_unique
  rejectOutputUnique := TypeExprRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
