import Solcore.Syntax.DeclarativeYulBlockStatementOutcomeProperties
import Solcore.Syntax.Parser.YulBlockOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.Yul.Statement

/-! Executable ordinary outcome bridges for Yul blocks in statement form. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful executable block statement lifts the exact ordinary
underlying block outcome. -/
theorem yulBlockStatement_success_ordinary_sound
    (nested : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {statement : YulStmt},
      nested input = .ok statement output →
        statementOrdinary input.declarativeRemainder statement
          output.declarativeRemainder)
    {input output : State} {statement : YulStmt}
    (result : yulBlockStatement nested input = .ok statement output) :
    DeclarativeGrammar.YulBlockStatementOrdinaryParses statementOrdinary
      input.declarativeRemainder statement output.declarativeRemainder := by
  unfold yulBlockStatement at result
  cases blockResult : yulBlock nested input with
  | invariant error => simp [bind, blockResult] at result
  | reject failure rejected => simp [bind, blockResult] at result
  | ok block afterBlock =>
      simp only [bind, blockResult, pure] at result
      cases result
      exact .parsed (yulBlock_success_ordinary_sound nested statementOrdinary
        nestedSuccessSound blockResult)

/-- Every executable block-statement rejection is exactly the underlying
block rejection. -/
theorem yulBlockStatement_reject_ordinary_sound
    (nested : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {statement : YulStmt},
      nested input = .ok statement output →
        statementOrdinary input.declarativeRemainder statement
          output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : yulBlockStatement nested input = .reject failure rejected) :
    DeclarativeGrammar.YulBlockStatementRejects statementOrdinary
      statementRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold yulBlockStatement at result
  cases blockResult : yulBlock nested input with
  | invariant error => simp [bind, blockResult] at result
  | ok block afterBlock => simp [bind, blockResult, pure] at result
  | reject blockFailure blockRejected =>
      simp only [bind, blockResult] at result
      cases result
      exact yulBlock_reject_ordinary_sound nested statementOrdinary
        statementRejects nestedSuccessSound nestedRejectSound blockResult

end Solcore.Syntax.Parser
