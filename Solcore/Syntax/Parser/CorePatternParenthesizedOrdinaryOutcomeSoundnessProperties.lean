import Solcore.Syntax.DeclarativeCorePatternParenthesizedOutcomeProperties
import Solcore.Syntax.Parser.CorePatternParenthesizedOrdinaryRejectionSoundnessProperties

/-! Packaged executable ordinary outcomes for parenthesized patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Package unconditional executable success and rejection reflection. -/
theorem parenthesizedPattern_ordinaryOutcome_sound
    (nested : Parser Pattern)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {pattern : Pattern},
      nested input = .ok pattern output → nestedOrdinary
        input.declarativeRemainder pattern output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {pattern : Pattern},
      parenthesizedPattern nested input = .ok pattern output →
        DeclarativeGrammar.ParenthesizedPatternOrdinaryParses nestedOrdinary
          input.declarativeRemainder pattern output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      parenthesizedPattern nested input = .reject failure rejected →
        DeclarativeGrammar.ParenthesizedPatternRejects nestedOrdinary
          nestedRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨parenthesizedPattern_success_ordinary_sound nested nestedOrdinary
      nestedSuccessSound,
    parenthesizedPattern_reject_ordinary_sound nested nestedOrdinary
      nestedRejects nestedSuccessSound nestedRejectSound⟩

/-- Re-export deterministic parenthesized-pattern outcomes. -/
theorem parenthesizedPattern_ordinaryOutcomeSpec
    {nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop}
    {nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      nestedOrdinary nestedRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ParenthesizedPatternOrdinaryParses nestedOrdinary)
      (DeclarativeGrammar.ParenthesizedPatternRejects nestedOrdinary
        nestedRejects) :=
  DeclarativeGrammar.parenthesizedPatternDeterministicOutcomeSpec
    nestedOutcomes

end Solcore.Syntax.Parser.PatternInternals
