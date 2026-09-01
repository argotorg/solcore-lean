import Solcore.Syntax.DeclarativeCorePatternQualifiedOutcomeProperties
import Solcore.Syntax.Parser.CorePatternQualifiedOrdinaryRejectionSoundnessProperties

/-! Packaged executable ordinary outcomes for `qualifiedPattern`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Package exact success and rejection over supplied nested-pattern outcome
bridges. -/
theorem qualifiedPattern_ordinaryOutcome_sound
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
        input.declarativeRemainder rejected.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested) :
    (∀ {input output : State} {pattern : Pattern},
      qualifiedPattern nested input = .ok pattern output →
        DeclarativeGrammar.QualifiedPatternOrdinaryParses nestedOrdinary
          nestedRejects input.declarativeRemainder pattern
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      qualifiedPattern nested input = .reject failure rejected →
        DeclarativeGrammar.QualifiedPatternRejects nestedOrdinary
          nestedRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨qualifiedPattern_success_ordinary_sound nested nestedOrdinary
      nestedRejects nestedSuccessSound nestedRejectSound nestedShape,
    qualifiedPattern_reject_ordinary_sound nested nestedOrdinary
      nestedRejects⟩

/-- Re-export deterministic qualified-pattern outcomes. -/
theorem qualifiedPattern_ordinaryOutcomeSpec
    {nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop}
    {nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      nestedOrdinary nestedRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.QualifiedPatternOrdinaryParses nestedOrdinary
        nestedRejects)
      (DeclarativeGrammar.QualifiedPatternRejects nestedOrdinary
        nestedRejects) :=
  DeclarativeGrammar.qualifiedPatternDeterministicOutcomeSpec nestedOutcomes

end Solcore.Syntax.Parser.PatternInternals
