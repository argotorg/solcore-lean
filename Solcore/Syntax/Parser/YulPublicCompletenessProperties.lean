import Solcore.Syntax.Parser.OrdinaryOutcomeCompletenessProperties
import Solcore.Syntax.Parser.Yul.BodyTotalityProperties
import Solcore.Syntax.Parser.YulBodyPublicSoundnessProperties
import Solcore.Syntax.Parser.YulExpressionPublicFuelSoundnessProperties

/-! Complete public Yul grammar correspondence on valid parser states. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Public Yul expression grammar success is exactly execution with the same
AST and declarative remainder, including diagnosed recovery. -/
theorem yulExpression_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : YulExpr} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.YulExpressionOrdinaryParses
        input.declarativeRemainder value remainder ↔
      ∃ output, yulExpression input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok yulExpression yulExpression_publicExactOutcomeSpec
    (yulExpression_ne_invariant input inputValid)
    yulExpression_success_ordinary_sound yulExpression_reject_public_sound

/-- Public Yul expression rejection is exactly execution at the same declarative
endpoint, without fixing the failure payload or diagnostic accumulator. -/
theorem yulExpression_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.YulExpressionPublicRejects input.declarativeRemainder rejected ↔
      ∃ failure output, yulExpression input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject yulExpression yulExpression_publicExactOutcomeSpec
    (yulExpression_ne_invariant input inputValid)
    yulExpression_success_ordinary_sound yulExpression_reject_public_sound

/-- The equivalent concrete expression boundary has the same rejection completeness. -/
theorem yulExpression_boundary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.YulExpressionRejects input.declarativeRemainder rejected ↔
      ∃ failure output, yulExpression input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  DeclarativeGrammar.yulExpressionPublicRejects_iff.symm.trans
    (yulExpression_ordinary_reject_iff inputValid)

/-- Public Yul statement grammar success is exactly execution with the same
located statement and complete declarative remainder. -/
theorem yulStatement_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : YulStmt} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.YulStatementOrdinaryParses
        input.declarativeRemainder value remainder ↔
      ∃ output, yulStatement input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok yulStatement yulStatement_publicExactOutcomeSpec
    (yulStatement_ne_invariant input inputValid)
    yulStatement_success_ordinary_sound yulStatement_reject_ordinary_sound

/-- Public Yul statement rejection is exactly execution at its declarative endpoint. -/
theorem yulStatement_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.YulStatementPublicRejects input.declarativeRemainder rejected ↔
      ∃ failure output, yulStatement input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject yulStatement yulStatement_publicExactOutcomeSpec
    (yulStatement_ne_invariant input inputValid)
    yulStatement_success_ordinary_sound yulStatement_reject_ordinary_sound

/-- The equivalent concrete statement boundary has the same rejection completeness. -/
theorem yulStatement_boundary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.YulStatementRejects input.declarativeRemainder rejected ↔
      ∃ failure output, yulStatement input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  DeclarativeGrammar.yulStatementPublicRejects_iff.symm.trans
    (yulStatement_ordinary_reject_iff inputValid)

private theorem yulBody_parsedBlock_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (fun input (value : YulParsedBlock) output =>
        DeclarativeGrammar.YulBodyOrdinaryParses input value.span value.body output)
      DeclarativeGrammar.YulBodyRejects where
  successOutputUnique := fun left right =>
    (DeclarativeGrammar.YulBodyOrdinaryParses.result_unique left right).2.2
  successRejectDisjoint := by
    intro input rejected rejection
    rintro ⟨body, output, parsed⟩
    exact yulBody_exactOutcomeSpec.successRejectDisjoint rejection
      ⟨{ span := body.span, body := body.body }, output, parsed⟩
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    have resultEq := DeclarativeGrammar.YulBodyOrdinaryParses.result_unique
      leftParsed rightParsed
    cases left
    cases right
    simp_all
  rejectOutputUnique := yulBody_exactOutcomeSpec.rejectOutputUnique

/-- The public braced Yul block grammar is exactly execution with the same
span, forward statement list, and complete declarative remainder. -/
theorem yulBody_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : YulParsedBlock} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.YulBodyOrdinaryParses
        input.declarativeRemainder value.span value.body remainder ↔
      ∃ output, yulBody input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok yulBody yulBody_parsedBlock_exactOutcomeSpec
    (yulBody_ne_invariant input inputValid)
    yulBody_success_ordinary_sound yulBody_reject_ordinary_sound

/-- Public Yul block rejection is exactly execution at the grammar's first-failure
endpoint; no equality of failure contents or whole states is claimed. -/
theorem yulBody_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.YulBodyRejects input.declarativeRemainder rejected ↔
      ∃ failure output, yulBody input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject yulBody yulBody_parsedBlock_exactOutcomeSpec
    (yulBody_ne_invariant input inputValid)
    yulBody_success_ordinary_sound yulBody_reject_ordinary_sound

end Solcore.Syntax.Parser
