import Solcore.Syntax.DeclarativeCoreExpressionConditionalOutcomeProperties
import Solcore.Syntax.Parser.CoreExpressionConditionalOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.CoreExpressionConditionalOrdinarySuccessSoundnessProperties

/-! Composed executable ordinary outcomes for Core conditional parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

/-- Package complete conditional success and rejection over supplied recursive
and alternative outcomes. -/
theorem conditional_ordinaryOutcome_sound
    (nested alternative : Parser Expr)
    (nestedOrdinary alternativeOrdinary :
      DeclarativeGrammar.Remainder → Expr →
        DeclarativeGrammar.Remainder → Prop)
    (nestedRejects alternativeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (alternativeSuccessSound :
      ∀ {input output : State} {expression : Expr},
        alternative input = .ok expression output → alternativeOrdinary
          input.declarativeRemainder expression output.declarativeRemainder)
    (alternativeRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        alternative input = .reject failure rejected → alternativeRejects
          input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {expression : Expr},
      conditional nested alternative input = .ok expression output →
        DeclarativeGrammar.ConditionalOrdinaryParses nestedOrdinary
          alternativeOrdinary input.declarativeRemainder expression
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      conditional nested alternative input = .reject failure rejected →
        DeclarativeGrammar.ConditionalRejects nestedOrdinary
          alternativeOrdinary nestedRejects alternativeRejects
            input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨conditional_success_ordinary_sound nested alternative nestedOrdinary
      alternativeOrdinary nestedSuccessSound alternativeSuccessSound,
    conditional_reject_ordinary_sound nested alternative nestedOrdinary
      alternativeOrdinary nestedRejects alternativeRejects nestedSuccessSound
        nestedRejectSound alternativeSuccessSound alternativeRejectSound⟩

/-- Lift deterministic recursive and alternative outcomes through the
conditional layer. -/
theorem conditional_ordinaryOutcomeSpec
    {nestedOrdinary alternativeOrdinary :
      DeclarativeGrammar.Remainder → Expr →
        DeclarativeGrammar.Remainder → Prop}
    {nestedRejects alternativeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      nestedOrdinary nestedRejects)
    (alternativeOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      alternativeOrdinary alternativeRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ConditionalOrdinaryParses nestedOrdinary
        alternativeOrdinary)
      (DeclarativeGrammar.ConditionalRejects nestedOrdinary alternativeOrdinary
        nestedRejects alternativeRejects) :=
  DeclarativeGrammar.conditionalDeterministicOutcomeSpec nestedOutcomes
    alternativeOutcomes

end Solcore.Syntax.Parser.ExpressionInternals
