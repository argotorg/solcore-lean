import Solcore.Syntax.DeclarativeCoreParenthesizedOutcomeProperties
import Solcore.Syntax.Parser.CoreParenthesizedOrdinaryRejectionSoundnessProperties

/-! Packaged executable ordinary outcomes for guarded Core parentheses. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Package unconditional parenthesized success with exact rejection under
the atom dispatcher's positive opening-parenthesis guard. -/
theorem parenthesized_guardedOrdinaryOutcome_sound
    (nested : Parser Expr)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {expression : Expr},
      parenthesized nested input = .ok expression output →
        DeclarativeGrammar.ParenthesizedExpressionOrdinaryParses
          nestedOrdinary input.declarativeRemainder expression
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      isSymbol input .leftParen = true →
        parenthesized nested input = .reject failure rejected →
          DeclarativeGrammar.ParenthesizedExpressionRejects nestedOrdinary
            nestedRejects input.declarativeRemainder
              rejected.declarativeRemainder) :=
  ⟨parenthesized_success_ordinary_sound nested nestedOrdinary
      nestedSuccessSound,
    parenthesized_reject_ordinary_sound nested nestedOrdinary nestedRejects
      nestedSuccessSound nestedRejectSound⟩

/-- Lift a deterministic nested expression outcome to parentheses. -/
theorem parenthesized_ordinaryOutcomeSpec
    {nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      nestedOrdinary nestedRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ParenthesizedExpressionOrdinaryParses
        nestedOrdinary)
      (DeclarativeGrammar.ParenthesizedExpressionRejects nestedOrdinary
        nestedRejects) :=
  DeclarativeGrammar.parenthesizedExpressionDeterministicOutcomeSpec
    nestedOutcomes

end Solcore.Syntax.Parser.ExpressionAtomInternals
