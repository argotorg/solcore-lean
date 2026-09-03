import Solcore.Syntax.Parser.CoreTermPublicExactnessProperties
import Solcore.Syntax.Parser.OrdinaryOutcomeCompletenessProperties
import Solcore.Syntax.Parser.PublicCoreTermTotalityProperties

/-! Complete ordinary grammar correspondence for public Core term parsers
on valid states, at the AST and declarative remainder boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Public expression grammar success is equivalent to execution with the
same AST and declarative remainder on a valid input. -/
theorem expression_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : Expr} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.CoreExpressionOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, expression input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok expression expression_exactOutcomeSpec
    (expression_invariantFreeOnValid.ne_invariant input inputValid)
    expression_success_ordinary_sound expression_reject_ordinary_sound

/-- Public expression grammar rejection is equivalent to execution at the
same declarative endpoint on a valid input. -/
theorem expression_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.CoreExpressionPublicRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, expression input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject expression expression_exactOutcomeSpec
    (expression_invariantFreeOnValid.ne_invariant input inputValid)
    expression_success_ordinary_sound expression_reject_ordinary_sound

/-- Public pattern grammar success is equivalent to execution with the
same AST and declarative remainder on a valid input. -/
theorem pattern_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : Pattern} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.CorePatternOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, pattern input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok pattern pattern_exactOutcomeSpec
    (pattern_invariantFreeOnValid.ne_invariant input inputValid)
    pattern_success_ordinary_sound pattern_reject_ordinary_sound

/-- Public pattern grammar rejection is equivalent to execution at the
same declarative endpoint on a valid input. -/
theorem pattern_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.CorePatternPublicRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, pattern input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject pattern pattern_exactOutcomeSpec
    (pattern_invariantFreeOnValid.ne_invariant input inputValid)
    pattern_success_ordinary_sound pattern_reject_ordinary_sound

/-- Public statement grammar success is equivalent to execution with the
same AST and declarative remainder on a valid input. -/
theorem statement_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : Statement} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.CoreStatementOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, statement input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok statement statement_exactOutcomeSpec
    (statement_invariantFreeOnValid.ne_invariant input inputValid)
    statement_success_ordinary_sound statement_reject_ordinary_sound

/-- Public statement grammar rejection is equivalent to execution at the
same declarative endpoint on a valid input. -/
theorem statement_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.CoreStatementPublicRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, statement input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject statement statement_exactOutcomeSpec
    (statement_invariantFreeOnValid.ne_invariant input inputValid)
    statement_success_ordinary_sound statement_reject_ordinary_sound

end Solcore.Syntax.Parser
