import Solcore.Syntax.DeclarativeCorePatternCoreOutcomeProperties
import Solcore.Syntax.Parser.CorePatternCoreOutcomeRejectionSoundnessProperties

/-! Packaged generic executable ordinary outcomes for `patternCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Package executable success and rejection reflection over four supplied
recursive-branch outcome bridges. -/
theorem patternCore_ordinaryOutcome_sound
    (nested : Parser Pattern) (expression : Parser Expr)
    (parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
      qualifiedOrdinary : DeclarativeGrammar.Remainder → Pattern →
        DeclarativeGrammar.Remainder → Prop)
    (parenthesizedRejects dotConstructorRejects comptimeRejects
      qualifiedRejects : DeclarativeGrammar.Remainder →
        DeclarativeGrammar.Remainder → Prop)
    (parenthesizedSuccessSound :
      ∀ {input output : State} {pattern : Pattern},
        parenthesizedPattern nested input = .ok pattern output →
          parenthesizedOrdinary input.declarativeRemainder pattern
            output.declarativeRemainder)
    (dotConstructorSuccessSound :
      ∀ {input output : State} {pattern : Pattern},
        dotConstructorPattern nested input = .ok pattern output →
          dotConstructorOrdinary input.declarativeRemainder pattern
            output.declarativeRemainder)
    (comptimeSuccessSound :
      ∀ {input output : State} {pattern : Pattern},
        comptimePattern expression input = .ok pattern output →
          comptimeOrdinary input.declarativeRemainder pattern
            output.declarativeRemainder)
    (qualifiedSuccessSound :
      ∀ {input output : State} {pattern : Pattern},
        qualifiedPattern nested input = .ok pattern output →
          qualifiedOrdinary input.declarativeRemainder pattern
            output.declarativeRemainder)
    (parenthesizedRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        parenthesizedPattern nested input = .reject failure rejected →
          parenthesizedRejects input.declarativeRemainder
            rejected.declarativeRemainder)
    (dotConstructorRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        dotConstructorPattern nested input = .reject failure rejected →
          dotConstructorRejects input.declarativeRemainder
            rejected.declarativeRemainder)
    (comptimeRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        comptimePattern expression input = .reject failure rejected →
          comptimeRejects input.declarativeRemainder
            rejected.declarativeRemainder)
    (qualifiedRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        qualifiedPattern nested input = .reject failure rejected →
          qualifiedRejects input.declarativeRemainder
            rejected.declarativeRemainder) :
    (∀ {input output : State} {pattern : Pattern},
      patternCore nested expression input = .ok pattern output →
        DeclarativeGrammar.PatternCoreOrdinaryParses parenthesizedOrdinary
          dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary
            input.declarativeRemainder pattern
              output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      patternCore nested expression input = .reject failure rejected →
        DeclarativeGrammar.PatternCoreRejects parenthesizedRejects
          dotConstructorRejects comptimeRejects qualifiedRejects
            input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨patternCore_success_ordinary_sound nested expression
      parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
        qualifiedOrdinary parenthesizedSuccessSound
          dotConstructorSuccessSound comptimeSuccessSound
            qualifiedSuccessSound,
    patternCore_reject_ordinary_sound nested expression
      parenthesizedRejects dotConstructorRejects comptimeRejects
        qualifiedRejects parenthesizedRejectSound dotConstructorRejectSound
          comptimeRejectSound qualifiedRejectSound⟩

/-- Lift four deterministic recursive outcomes through the public executable
dispatcher relations. -/
theorem patternCore_ordinaryOutcomeSpec
    {parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
      qualifiedOrdinary : DeclarativeGrammar.Remainder → Pattern →
        DeclarativeGrammar.Remainder → Prop}
    {parenthesizedRejects dotConstructorRejects comptimeRejects
      qualifiedRejects : DeclarativeGrammar.Remainder →
        DeclarativeGrammar.Remainder → Prop}
    (parenthesizedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      parenthesizedOrdinary parenthesizedRejects)
    (dotConstructorOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      dotConstructorOrdinary dotConstructorRejects)
    (comptimeOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      comptimeOrdinary comptimeRejects)
    (qualifiedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      qualifiedOrdinary qualifiedRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.PatternCoreOrdinaryParses parenthesizedOrdinary
        dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary)
      (DeclarativeGrammar.PatternCoreRejects parenthesizedRejects
        dotConstructorRejects comptimeRejects qualifiedRejects) :=
  DeclarativeGrammar.patternCoreDeterministicOutcomeSpec
    parenthesizedOutcomes dotConstructorOutcomes comptimeOutcomes
      qualifiedOutcomes

end Solcore.Syntax.Parser.PatternInternals
