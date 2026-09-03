import Solcore.Syntax.DeclarativeYulStatementCoreExactnessProperties
import Solcore.Syntax.DeclarativeYulStatementFuelGrammar
import Solcore.Syntax.DeclarativeYulStatementLayerExactnessProperties

/-! Exact recursive fixed-fuel and public inline-Yul statement outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every recursive statement fuel fixes successful ASTs and rejecting endpoints. -/
theorem yulStatementExactOutcomeSpecWithFuel (fuel : Nat) :
    ExactDeterministicOutcomeSpec (YulStatementOrdinaryParsesWithFuel fuel)
      (YulStatementRejectsWithFuel fuel) := by
  induction fuel with
  | zero =>
      exact {
        toDeterministicOutcomeSpec := yulStatementOutcomeSpecWithFuel 0
        successValueUnique := by
          intro input left right afterLeft afterRight leftParsed
          exact False.elim (YulStatementOrdinaryParsesWithFuel.zero leftParsed)
        rejectOutputUnique := by
          intro input left right leftRejected
          exact False.elim (YulStatementRejectsWithFuel.zero leftRejected)
      }
  | succ fuel ih =>
      exact yulStatementLayerExactOutcomeSpec
        (yulStatementTerminatedExactOutcomeSpec (yulStatementCoreExactOutcomeSpec ih))
        (YulStatementRejects.disjointTerminatedOrdinary
          (YulStatementRejects.disjointCoreOrdinary ih.toDeterministicOutcomeSpec))

/-- Fixed-fuel ordinary statements fix their complete AST and remainder. -/
theorem YulStatementOrdinaryParsesWithFuel.result_unique {fuel : Nat}
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulStatementOrdinaryParsesWithFuel fuel input left afterLeft)
    (rightParsed : YulStatementOrdinaryParsesWithFuel fuel input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  (yulStatementExactOutcomeSpecWithFuel fuel).successResultUnique leftParsed rightParsed

/-- Fixed-fuel ordinary statement rejection fixes the complete endpoint. -/
theorem YulStatementRejectsWithFuel.output_unique {fuel : Nat}
    {input left right : Remainder}
    (leftRejected : YulStatementRejectsWithFuel fuel input left)
    (rightRejected : YulStatementRejectsWithFuel fuel input right) : left = right :=
  (yulStatementExactOutcomeSpecWithFuel fuel).rejectOutputUnique leftRejected rightRejected

/-- Input-selected public fuel preserves fully exact ordinary statement outcomes. -/
theorem yulStatementPublicExactOutcomeSpec :
    ExactDeterministicOutcomeSpec YulStatementOrdinaryParses
      YulStatementPublicRejects where
  toDeterministicOutcomeSpec := yulStatementPublicOutcomeSpec
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact (yulStatementExactOutcomeSpecWithFuel (yulStatementPublicFuel input)).successValueUnique
      leftParsed rightParsed
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    exact (yulStatementExactOutcomeSpecWithFuel (yulStatementPublicFuel input)).rejectOutputUnique
      leftRejected rightRejected

/-- Exact public statement outcomes with the concrete recovery-boundary rejection. -/
theorem yulStatementExactOutcomeSpec :
    ExactDeterministicOutcomeSpec YulStatementOrdinaryParses YulStatementRejects where
  toDeterministicOutcomeSpec := yulStatementPublicDeterministicOutcomeSpec
  successValueUnique := yulStatementPublicExactOutcomeSpec.successValueUnique
  rejectOutputUnique := YulStatementRejects.output_unique

/-- Public ordinary statements fix their complete AST and final remainder. -/
theorem YulStatementOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulStatementOrdinaryParses input left afterLeft)
    (rightParsed : YulStatementOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  yulStatementExactOutcomeSpec.successResultUnique leftParsed rightParsed

/-- Public fuel-indexed statement rejection fixes its complete endpoint. -/
theorem YulStatementPublicRejects.output_unique {input left right : Remainder}
    (leftRejected : YulStatementPublicRejects input left)
    (rightRejected : YulStatementPublicRejects input right) : left = right :=
  yulStatementPublicExactOutcomeSpec.rejectOutputUnique leftRejected rightRejected

end Solcore.Syntax.DeclarativeGrammar
