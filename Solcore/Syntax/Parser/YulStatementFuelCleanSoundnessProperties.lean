import Solcore.Syntax.DeclarativeYulStatementFuelGrammar
import Solcore.Syntax.Parser.YulAssignmentPublicFallbackSoundnessProperties
import Solcore.Syntax.Parser.YulStatementLayerSoundnessProperties
import Solcore.Syntax.Parser.YulStatementRecursiveDiagnosticReflectionProperties

/-! Diagnostic-free reflection for recursive fuel-indexed Yul statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every diagnostic-free executable success at explicit fuel follows the
clean declarative relation at that same fuel. -/
theorem yulStatementWithFuel_success_clean_sound : ∀ fuel,
    ∀ {input output : State} {statement : YulStmt},
      output.diagnosticsRev = [] →
      yulStatementWithFuel fuel input = .ok statement output →
        DeclarativeGrammar.YulStatementCleanParsesWithFuel fuel
          input.declarativeRemainder statement output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro input output statement diagnosticFree result
      simp [yulStatementWithFuel] at result
  | succ fuel inductionHypothesis =>
      intro input output statement diagnosticFree result
      apply (DeclarativeGrammar.YulStatementCleanParsesWithFuel.succ_iff).2
      exact yulStatementLayer_success_sound
        (yulStatementWithFuel fuel)
        (DeclarativeGrammar.YulStatementCleanParsesWithFuel fuel)
        DeclarativeGrammar.YulExpressionParses
        DeclarativeGrammar.yulAssignmentPublicFallbackSpec
        yulAssignment_publicFallback_reject_sound
        (yulStatementWithFuel_reflectsDiagnosticFreeOnSuccess fuel)
        inductionHypothesis yulExpression_success_clean_sound diagnosticFree
        result

end Solcore.Syntax.Parser
