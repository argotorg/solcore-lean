import Solcore.Syntax.DeclarativeYulStatementExactnessProperties
import Solcore.Syntax.Parser.YulStatementFuelCleanSoundnessProperties
import Solcore.Syntax.Parser.YulStatementFuelOrdinarySoundnessProperties

/-! Concrete public-fuel soundness for `yulStatement`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The executable `remainingCount + 1` is exactly the parser-independent
public statement fuel on the same active token window and cursor. -/
@[simp] theorem yulStatement_executableFuel_eq_publicFuel (input : State) :
    input.remainingCount + 1 =
      DeclarativeGrammar.yulStatementPublicFuel
        input.declarativeRemainder := by
  rfl

/-- Every diagnostic-free public statement success follows the clean grammar
at the exact public fuel selected from its input remainder. -/
theorem yulStatement_success_clean_sound
    {input output : State} {statement : YulStmt}
    (diagnosticFree : output.diagnosticsRev = [])
    (result : yulStatement input = .ok statement output) :
    DeclarativeGrammar.YulStatementParses input.declarativeRemainder statement
      output.declarativeRemainder := by
  unfold yulStatement at result
  unfold DeclarativeGrammar.YulStatementParses
  rw [← yulStatement_executableFuel_eq_publicFuel input]
  exact yulStatementWithFuel_success_clean_sound
    (input.remainingCount + 1) diagnosticFree result

/-- Every public statement success follows the ordinary public grammar,
including diagnosed recovery success. -/
theorem yulStatement_success_ordinary_sound
    {input output : State} {statement : YulStmt}
    (result : yulStatement input = .ok statement output) :
    DeclarativeGrammar.YulStatementOrdinaryParses
      input.declarativeRemainder statement output.declarativeRemainder := by
  unfold yulStatement at result
  unfold DeclarativeGrammar.YulStatementOrdinaryParses
  rw [← yulStatement_executableFuel_eq_publicFuel input]
  exact yulStatementWithFuel_success_ordinary_sound
    (input.remainingCount + 1) result

/-- Every public statement rejection follows the exact public fuel-indexed
rejection relation. -/
theorem yulStatement_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : yulStatement input = .reject failure rejected) :
    DeclarativeGrammar.YulStatementPublicRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold yulStatement at result
  unfold DeclarativeGrammar.YulStatementPublicRejects
  rw [← yulStatement_executableFuel_eq_publicFuel input]
  exact yulStatementWithFuel_reject_ordinary_sound
    (input.remainingCount + 1) result

/-- Public executable rejection is equivalently the concrete nonconsuming
outer statement boundary. -/
theorem yulStatement_reject_boundary_sound
    {input rejected : State} {failure : Failure}
    (result : yulStatement input = .reject failure rejected) :
    DeclarativeGrammar.YulStatementRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  DeclarativeGrammar.yulStatementPublicRejects_iff.mp
    (yulStatement_reject_ordinary_sound result)

/-- Re-export full ordinary statement exactness at each recursive fuel. -/
theorem yulStatementWithFuel_exactOutcomeSpec (fuel : Nat) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel)
      (DeclarativeGrammar.YulStatementRejectsWithFuel fuel) :=
  DeclarativeGrammar.yulStatementExactOutcomeSpecWithFuel fuel

/-- Fixed-fuel executable successes agree on their complete statement result. -/
theorem yulStatementWithFuel_success_result_unique (fuel : Nat)
    {input leftOutput rightOutput : State} {left right : YulStmt}
    (leftResult : yulStatementWithFuel fuel input = .ok left leftOutput)
    (rightResult : yulStatementWithFuel fuel input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel.result_unique
    (yulStatementWithFuel_success_ordinary_sound fuel leftResult)
    (yulStatementWithFuel_success_ordinary_sound fuel rightResult)

/-- Fixed-fuel executable rejections agree on the complete declarative endpoint. -/
theorem yulStatementWithFuel_reject_output_unique (fuel : Nat)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : yulStatementWithFuel fuel input = .reject leftFailure leftOutput)
    (rightResult : yulStatementWithFuel fuel input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.YulStatementRejectsWithFuel.output_unique
    (yulStatementWithFuel_reject_ordinary_sound fuel leftResult)
    (yulStatementWithFuel_reject_ordinary_sound fuel rightResult)

/-- Re-export public statement exactness with the input-selected fuel relation. -/
theorem yulStatement_publicExactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.YulStatementOrdinaryParses
      DeclarativeGrammar.YulStatementPublicRejects :=
  DeclarativeGrammar.yulStatementPublicExactOutcomeSpec

/-- Exact public statements against the concrete recovery-boundary rejection. -/
theorem yulStatement_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.YulStatementOrdinaryParses
      DeclarativeGrammar.YulStatementRejects :=
  DeclarativeGrammar.yulStatementExactOutcomeSpec

/-- Public executable statement successes agree on their AST and remainder. -/
theorem yulStatement_success_result_unique
    {input leftOutput rightOutput : State} {left right : YulStmt}
    (leftResult : yulStatement input = .ok left leftOutput)
    (rightResult : yulStatement input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.YulStatementOrdinaryParses.result_unique
    (yulStatement_success_ordinary_sound leftResult)
    (yulStatement_success_ordinary_sound rightResult)

/-- Public executable statement rejections agree on their complete endpoint. -/
theorem yulStatement_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : yulStatement input = .reject leftFailure leftOutput)
    (rightResult : yulStatement input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.YulStatementPublicRejects.output_unique
    (yulStatement_reject_ordinary_sound leftResult)
    (yulStatement_reject_ordinary_sound rightResult)

end Solcore.Syntax.Parser
