import Solcore.Syntax.Parser.DelimitedFallbackRejectionSoundnessProperties
import Solcore.Syntax.Parser.YulExpressionFuelOrdinarySoundnessProperties

/-! Diagnostic-free soundness for the fuel-indexed inline-Yul expression. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace YulExpressionInternals

/-- Every diagnostic-free executable success follows the clean grammar at the
same fuel.  Transactional argument rejection is instantiated from the exact
ordinary success/rejection pair at the preceding level. -/
theorem withFuel_success_clean_fuel_sound : ∀ fuel,
    ∀ {input output : State} {expression : YulExpr},
      output.diagnosticsRev = [] →
      withFuel fuel input = .ok expression output →
      DeclarativeGrammar.YulExpressionCleanParsesWithFuel fuel
        input.declarativeRemainder expression output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro input output expression diagnosticFree result
      simp [withFuel] at result
  | succ fuel inductionHypothesis =>
      intro input output expression diagnosticFree result
      apply DeclarativeGrammar.YulExpressionCleanParsesWithFuel.succ_iff.mpr
      apply yulExpressionLayer_success_sound
        (withFuel fuel)
        (DeclarativeGrammar.YulExpressionCleanParsesWithFuel fuel)
        (DeclarativeGrammar.yulExpressionCallArgumentsFallbackWithFuel fuel)
        (withFuel_reflectsDiagnosticFreeForDeclarativeSoundness fuel)
        inductionHypothesis
        (withFuel_preservesTokenWindow fuel)
      · intro argumentsInput argumentsFailed argumentsFailure
          argumentsResult
        exact yulCallArguments_fallback_reject_sound
          (withFuel fuel)
          (DeclarativeGrammar.YulExpressionOrdinaryParsesWithFuel fuel)
          (DeclarativeGrammar.YulExpressionCleanParsesWithFuel fuel)
          (DeclarativeGrammar.YulExpressionRejectsWithFuel fuel)
          (DeclarativeGrammar.yulExpressionOutcomeSpecWithFuel fuel)
          (fun parsed => parsed.toOrdinary)
          (withFuel_success_ordinary_fuel_sound fuel)
          (withFuel_reject_fuel_sound fuel) argumentsResult
      · exact diagnosticFree
      · exact result

end YulExpressionInternals

end Solcore.Syntax.Parser
