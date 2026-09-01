import Solcore.Syntax.DeclarativeYulExpressionFuelGrammar
import Solcore.Syntax.Parser.YulExpressionLayerOrdinarySoundnessProperties
import Solcore.Syntax.Parser.YulExpressionLayerSoundnessProperties
import Solcore.Syntax.Parser.Yul.ExpressionProperties

/-!
Fuel-indexed executable reflection for ordinary inline-Yul expression
successes, rejections, and diagnostic preservation.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace YulExpressionInternals

/-- Every executable fuel-level rejection follows that level's exact binary
rejection relation.  Fuel zero cannot reject because it returns an invariant. -/
theorem withFuel_reject_fuel_sound : ∀ fuel,
    ∀ {input rejected : State} {failure : Failure},
      withFuel fuel input = .reject failure rejected →
      DeclarativeGrammar.YulExpressionRejectsWithFuel fuel
        input.declarativeRemainder rejected.declarativeRemainder := by
  intro fuel
  cases fuel with
  | zero =>
      intro input rejected failure result
      simp [withFuel] at result
  | succ fuel =>
      intro input rejected failure result
      apply DeclarativeGrammar.YulExpressionRejectsWithFuel.succ_iff.mpr
      exact withFuel_succ_reject_sound fuel result

/-- Every successful executable fuel level follows the corresponding broad
ordinary-success relation. -/
theorem withFuel_success_ordinary_fuel_sound : ∀ fuel,
    ∀ {input output : State} {expression : YulExpr},
      withFuel fuel input = .ok expression output →
      DeclarativeGrammar.YulExpressionOrdinaryParsesWithFuel fuel
        input.declarativeRemainder expression output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro input output expression result
      simp [withFuel] at result
  | succ fuel inductionHypothesis =>
      intro input output expression result
      apply
        DeclarativeGrammar.YulExpressionOrdinaryParsesWithFuel.succ_iff.mpr
      exact layer_success_ordinary_sound (withFuel fuel)
        (DeclarativeGrammar.YulExpressionOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.YulExpressionRejectsWithFuel fuel)
        inductionHypothesis (withFuel_reject_fuel_sound fuel)
        (withFuel_preservesTokenWindow fuel) result

/-- Recursive diagnostic reflection used by the clean fuel-indexed proof.
This theorem is kept distinct from the statement-layer compatibility export. -/
theorem withFuel_reflectsDiagnosticFreeForDeclarativeSoundness : ∀ fuel,
    Parser.ReflectsDiagnosticFreeOnSuccess (withFuel fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro input expression output result diagnosticFree
      simp [withFuel] at result
  | succ fuel inductionHypothesis =>
      exact yulExpressionLayer_reflectsDiagnosticFreeOnSuccess
        (withFuel fuel) inductionHypothesis

end YulExpressionInternals

end Solcore.Syntax.Parser
