import Solcore.Syntax.Parser.CorePatternPublicOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.CorePatternPublicOrdinarySuccessSoundnessProperties

/-! Packaged executable ordinary outcomes for the public Core pattern layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package both public pattern outcomes over one supplied Core bridge. -/
theorem patternLayer_ordinaryOutcome_sound
    (nested : Parser Pattern) (expression : Parser Expr)
    (coreOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (coreRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (coreSuccessSound : ∀ {input output : State} {pattern : Pattern},
      PatternInternals.patternCore nested expression input =
          .ok pattern output →
        coreOrdinary input.declarativeRemainder pattern
          output.declarativeRemainder)
    (coreRejectSound : ∀ {input rejected : State} {failure : Failure},
      PatternInternals.patternCore nested expression input =
          .reject failure rejected →
        coreRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (coreWindow : Parser.PreservesTokenWindow
      (PatternInternals.patternCore nested expression)) :
    (∀ {input output : State} {pattern : Pattern},
      patternLayer nested expression input = .ok pattern output →
        DeclarativeGrammar.PatternLayerOrdinaryParses coreOrdinary coreRejects
          input.declarativeRemainder pattern output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      patternLayer nested expression input = .reject failure rejected →
        DeclarativeGrammar.PatternLayerRejects coreRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨patternLayer_success_ordinaryOutcome_sound nested expression coreOrdinary
      coreRejects coreSuccessSound coreRejectSound coreWindow,
    patternLayer_reject_ordinaryOutcome_sound nested expression coreRejects
      coreRejectSound coreWindow⟩

/-- Lift a deterministic Core-pattern contract through public recovery. -/
theorem patternLayer_ordinaryOutcomeSpec
    {coreOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop}
    {coreRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (coreOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec coreOrdinary
      coreRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.PatternLayerOrdinaryParses coreOrdinary coreRejects)
      (DeclarativeGrammar.PatternLayerRejects coreRejects) :=
  DeclarativeGrammar.patternLayerDeterministicOutcomeSpec coreOutcomes

end Solcore.Syntax.Parser
