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

end Solcore.Syntax.Parser
