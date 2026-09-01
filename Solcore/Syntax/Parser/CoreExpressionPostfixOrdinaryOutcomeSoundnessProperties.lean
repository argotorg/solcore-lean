import Solcore.Syntax.Parser.CoreExpressionPostfixOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.CoreExpressionPostfixOrdinarySuccessSoundnessProperties

/-!
Composed executable ordinary outcomes for maximal Core postfix expressions.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package both complete-postfix executable bridges over supplied atom and
recursive outcomes. -/
theorem expressionPostfix_ordinaryOutcome_sound
    (nested : Parser Expr) (block : Parser Block)
    (atomOrdinary nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (atomRejects nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (atomSuccessSound : ∀ {input output : State} {expression : Expr},
      expressionAtom nested block input = .ok expression output →
        atomOrdinary input.declarativeRemainder expression
          output.declarativeRemainder)
    (atomRejectSound : ∀ {input rejected : State} {failure : Failure},
      expressionAtom nested block input = .reject failure rejected →
        atomRejects input.declarativeRemainder rejected.declarativeRemainder)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested) :
    (∀ {input output : State} {expression : Expr},
      expressionPostfix nested block input = .ok expression output →
        DeclarativeGrammar.ExpressionPostfixOrdinaryParses atomOrdinary
          nestedOrdinary input.declarativeRemainder expression
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      expressionPostfix nested block input = .reject failure rejected →
        DeclarativeGrammar.ExpressionPostfixRejects atomOrdinary
          nestedOrdinary atomRejects nestedRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨expressionPostfix_success_ordinary_sound nested block atomOrdinary
      nestedOrdinary atomSuccessSound nestedSuccessSound nestedShape,
    expressionPostfix_reject_ordinary_sound nested block atomOrdinary
      nestedOrdinary atomRejects nestedRejects atomSuccessSound atomRejectSound
        nestedSuccessSound nestedRejectSound nestedShape⟩

/-- Lift deterministic atom and recursive outcomes to the complete postfix
layer. -/
theorem expressionPostfix_ordinaryOutcomeSpec
    {atomOrdinary nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {atomRejects nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (atomOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec atomOrdinary
      atomRejects)
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      nestedOrdinary nestedRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ExpressionPostfixOrdinaryParses atomOrdinary
        nestedOrdinary)
      (DeclarativeGrammar.ExpressionPostfixRejects atomOrdinary nestedOrdinary
        atomRejects nestedRejects) :=
  DeclarativeGrammar.expressionPostfixDeterministicOutcomeSpec atomOutcomes
    nestedOutcomes

end Solcore.Syntax.Parser
