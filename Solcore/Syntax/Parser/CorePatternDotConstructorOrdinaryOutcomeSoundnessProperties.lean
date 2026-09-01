import Solcore.Syntax.DeclarativeCorePatternDotConstructorOutcomeProperties
import Solcore.Syntax.Parser.CorePatternArgumentsOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CorePatternNameOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties

/-! Executable ordinary outcomes for leading-dot Core constructor patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Every executable success retains its exact dot, diagnostic-inclusive
Boolean-first name, transactional optional arguments, AST, span, and final
remainder. -/
theorem dotConstructorPattern_success_ordinary_sound
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
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input output : State} {pattern : Pattern}
    (result : dotConstructorPattern nested input = .ok pattern output) :
    DeclarativeGrammar.DotConstructorPatternOrdinaryParses nestedOrdinary
      nestedRejects input.declarativeRemainder pattern
        output.declarativeRemainder := by
  unfold dotConstructorPattern at result
  cases dotResult : symbol .dot .pattern input with
  | invariant error => simp [bind, dotResult] at result
  | reject failure rejected => simp [bind, dotResult] at result
  | ok dot afterDot =>
      simp only [bind, dotResult] at result
      cases nameResult : patternName afterDot with
      | invariant error => simp [nameResult] at result
      | reject failure rejected => simp [nameResult] at result
      | ok name afterName =>
          simp only [nameResult] at result
          cases argumentsResult : optionalConstructorArguments nested
              afterName with
          | invariant error => simp [argumentsResult] at result
          | reject failure rejected => simp [argumentsResult] at result
          | ok arguments afterArguments =>
              simp only [argumentsResult, pure] at result
              cases result
              exact .parsed dot.span
                (symbol_success_exactTokenParses .dot .pattern dotResult)
                (patternName_success_ordinary_sound nameResult)
                (optionalConstructorArguments_success_ordinary_sound nested
                  nestedOrdinary nestedRejects nestedSuccessSound
                    nestedRejectSound nestedShape argumentsResult)

/-- Every executable rejection records the first failing sequential stage.
In particular, a missing dot is non-consuming, while a rejected name follows
the exact consumed dot. -/
theorem dotConstructorPattern_reject_ordinary_sound
    (nested : Parser Pattern)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    {input rejected : State} {failure : Failure}
    (result : dotConstructorPattern nested input = .reject failure rejected) :
    DeclarativeGrammar.DotConstructorPatternRejects nestedOrdinary
      nestedRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold dotConstructorPattern at result
  cases dotResult : symbol .dot .pattern input with
  | invariant error => simp [bind, dotResult] at result
  | reject dotFailure afterDot =>
      simp only [bind, dotResult] at result
      have rejectedEq : afterDot = rejected := by injection result
      subst rejected
      have stateEq := symbol_reject_state_eq .dot .pattern dotResult
      rw [stateEq]
      exact .dotMissing
        (symbol_reject_tokenKindAbsentAt .dot .pattern dotResult)
  | ok dot afterDot =>
      simp only [bind, dotResult] at result
      cases nameResult : patternName afterDot with
      | invariant error => simp [nameResult] at result
      | reject nameFailure afterName =>
          simp only [nameResult] at result
          cases result
          exact .nameRejected dot.span
            (symbol_success_exactTokenParses .dot .pattern dotResult)
            (patternName_reject_ordinary_sound nameResult)
      | ok name afterName =>
          simp only [nameResult] at result
          cases argumentsResult : optionalConstructorArguments nested
              afterName with
          | invariant error => simp [argumentsResult] at result
          | ok arguments afterArguments =>
              simp [argumentsResult, pure] at result
          | reject argumentsFailure afterArguments =>
              simp only [argumentsResult] at result
              cases result
              exact .argumentsRejected dot.span
                (symbol_success_exactTokenParses .dot .pattern dotResult)
                (patternName_success_ordinary_sound nameResult)
                (optionalConstructorArguments_reject_ordinary_sound nested
                  argumentsResult)

/-- Package both executable leading-dot constructor-pattern outcomes. -/
theorem dotConstructorPattern_ordinaryOutcome_sound
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
      dotConstructorPattern nested input = .ok pattern output →
        DeclarativeGrammar.DotConstructorPatternOrdinaryParses
          nestedOrdinary nestedRejects input.declarativeRemainder pattern
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      dotConstructorPattern nested input = .reject failure rejected →
        DeclarativeGrammar.DotConstructorPatternRejects nestedOrdinary
          nestedRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨dotConstructorPattern_success_ordinary_sound nested nestedOrdinary
      nestedRejects nestedSuccessSound nestedRejectSound nestedShape,
    dotConstructorPattern_reject_ordinary_sound nested nestedOrdinary
      nestedRejects⟩

/-- Lift deterministic nested outcomes through the executable leading-dot
constructor-pattern relation. -/
theorem dotConstructorPattern_ordinaryOutcomeSpec
    {nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop}
    {nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      nestedOrdinary nestedRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.DotConstructorPatternOrdinaryParses nestedOrdinary
        nestedRejects)
      (DeclarativeGrammar.DotConstructorPatternRejects nestedOrdinary
        nestedRejects) :=
  DeclarativeGrammar.dotConstructorPatternDeterministicOutcomeSpec
    nestedOutcomes

end Solcore.Syntax.Parser.PatternInternals
