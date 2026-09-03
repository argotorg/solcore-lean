import Solcore.Syntax.DeclarativeCoreTermExactnessProperties

/-! Unconditional exact public Core terms and isolated block boundaries. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Input-selected expression fuel preserves complete ordinary exactness. -/
theorem coreExpressionPublicExactOutcomeSpec :
    ExactDeterministicOutcomeSpec CoreExpressionOrdinaryParses CoreExpressionPublicRejects where
  toDeterministicOutcomeSpec := coreExpressionPublicOutcomeSpec
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact (coreExpressionExactOutcomeSpecWithFuel (coreExpressionPublicFuel input))
      |>.successValueUnique leftParsed rightParsed
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    exact (coreExpressionExactOutcomeSpecWithFuel (coreExpressionPublicFuel input))
      |>.rejectOutputUnique leftRejected rightRejected

/-- Input-selected pattern fuel preserves complete ordinary exactness. -/
theorem corePatternPublicExactOutcomeSpec :
    ExactDeterministicOutcomeSpec CorePatternOrdinaryParses CorePatternPublicRejects where
  toDeterministicOutcomeSpec := corePatternPublicOutcomeSpec
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact (corePatternExactOutcomeSpecWithFuel (corePatternPublicFuel input))
      |>.successValueUnique leftParsed rightParsed
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    exact (corePatternExactOutcomeSpecWithFuel (corePatternPublicFuel input))
      |>.rejectOutputUnique leftRejected rightRejected

/-- Input-selected statement fuel preserves complete ordinary exactness. -/
theorem coreStatementPublicExactOutcomeSpec :
    ExactDeterministicOutcomeSpec CoreStatementOrdinaryParses CoreStatementPublicRejects where
  toDeterministicOutcomeSpec := coreStatementPublicOutcomeSpec
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact (coreStatementExactOutcomeSpecWithFuel (coreStatementPublicFuel input))
      |>.successValueUnique leftParsed rightParsed
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    exact (coreStatementExactOutcomeSpecWithFuel (coreStatementPublicFuel input))
      |>.rejectOutputUnique leftRejected rightRejected

/-- Both Core block tail policies now have unconditional public exactness. -/
theorem coreBlockPublicExactOutcomeSpec (policy : CoreBlockTailPolicy) :
    ExactDeterministicOutcomeSpec (CoreBlockPublicOrdinaryParses policy)
      (CoreBlockPublicRejects policy) :=
  coreBlockPublicExactOutcomeSpecOfStatementFuel coreStatementExactOutcomeSpecWithFuel policy

/-- Captured-body isolation preserves unconditional exactness for both policies. -/
theorem isolatedCoreBlockPublicExactOutcomeSpec (policy : CoreBlockTailPolicy) :
    ExactDeterministicOutcomeSpec (IsolatedCoreBlockPublicOrdinaryParses policy)
      (IsolatedCoreBlockPublicRejects policy) :=
  isolatedCoreBlockPublicExactOutcomeSpecOfStatementFuel
    coreStatementExactOutcomeSpecWithFuel policy

/-- Public Core expressions fix their complete AST and final remainder. -/
theorem CoreExpressionOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : CoreExpressionOrdinaryParses input left afterLeft)
    (rightParsed : CoreExpressionOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  coreExpressionPublicExactOutcomeSpec.successResultUnique leftParsed rightParsed

/-- Public Core patterns fix their complete AST and final remainder. -/
theorem CorePatternOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.Pattern} {afterLeft afterRight : Remainder}
    (leftParsed : CorePatternOrdinaryParses input left afterLeft)
    (rightParsed : CorePatternOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  corePatternPublicExactOutcomeSpec.successResultUnique leftParsed rightParsed

/-- Public Core statements fix their complete AST and final remainder. -/
theorem CoreStatementOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.Statement} {afterLeft afterRight : Remainder}
    (leftParsed : CoreStatementOrdinaryParses input left afterLeft)
    (rightParsed : CoreStatementOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  coreStatementPublicExactOutcomeSpec.successResultUnique leftParsed rightParsed

/-- Public Core expression rejection fixes the complete endpoint. -/
theorem CoreExpressionPublicRejects.output_unique {input left right : Remainder}
    (leftRejected : CoreExpressionPublicRejects input left)
    (rightRejected : CoreExpressionPublicRejects input right) : left = right :=
  coreExpressionPublicExactOutcomeSpec.rejectOutputUnique leftRejected rightRejected

/-- Public Core pattern rejection fixes the complete endpoint. -/
theorem CorePatternPublicRejects.output_unique {input left right : Remainder}
    (leftRejected : CorePatternPublicRejects input left)
    (rightRejected : CorePatternPublicRejects input right) : left = right :=
  corePatternPublicExactOutcomeSpec.rejectOutputUnique leftRejected rightRejected

/-- Public Core statement rejection fixes the complete endpoint. -/
theorem CoreStatementPublicRejects.output_unique {input left right : Remainder}
    (leftRejected : CoreStatementPublicRejects input left)
    (rightRejected : CoreStatementPublicRejects input right) : left = right :=
  coreStatementPublicExactOutcomeSpec.rejectOutputUnique leftRejected rightRejected

end Solcore.Syntax.DeclarativeGrammar
