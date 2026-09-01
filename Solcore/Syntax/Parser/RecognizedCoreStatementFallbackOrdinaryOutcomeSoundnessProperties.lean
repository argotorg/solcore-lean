import Solcore.Syntax.Parser.RecognizedCoreStatementFallbackOutcomeProperties

/-! Packaged ordinary outcomes for recognized Core-statement fallback. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/-- Package executable success and rejection of one recognized branch with
transactional fallback at the original input. -/
theorem recognizedStatementOrFallback_ordinaryOutcome_sound
    (primary fallback : Parser Statement)
    (primaryParses fallbackParses :
      DeclarativeGrammar.Remainder → Statement →
        DeclarativeGrammar.Remainder → Prop)
    (primaryRejects fallbackRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (primarySuccessSound : ∀ {input output : State} {value : Statement},
      primary input = .ok value output → primaryParses
        input.declarativeRemainder value output.declarativeRemainder)
    (primaryRejectSound : ∀ {input rejected : State} {failure : Failure},
      primary input = .reject failure rejected → primaryRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (fallbackSuccessSound : ∀ {input output : State} {value : Statement},
      fallback input = .ok value output → fallbackParses
        input.declarativeRemainder value output.declarativeRemainder)
    (fallbackRejectSound : ∀ {input rejected : State} {failure : Failure},
      fallback input = .reject failure rejected → fallbackRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {value : Statement},
      recognizedStatementOrFallback primary fallback input =
          .ok value output →
        DeclarativeGrammar.TransactionalFallbackOrdinaryParses primaryParses
          primaryRejects fallbackParses input.declarativeRemainder value
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      recognizedStatementOrFallback primary fallback input =
          .reject failure rejected →
        DeclarativeGrammar.TransactionalFallbackRejects primaryRejects
          fallbackRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨recognizedStatementOrFallback_success_ordinary_sound primary fallback
      primaryParses fallbackParses primaryRejects primarySuccessSound
        primaryRejectSound fallbackSuccessSound,
    recognizedStatementOrFallback_reject_sound primary fallback
      primaryRejects fallbackRejects primaryRejectSound fallbackRejectSound⟩

/-- Lift deterministic primary and fallback outcomes through the executable
transactional wrapper relation. -/
theorem recognizedStatementOrFallback_ordinaryOutcomeSpec
    (primaryParses fallbackParses :
      DeclarativeGrammar.Remainder → Statement →
        DeclarativeGrammar.Remainder → Prop)
    (primaryRejects fallbackRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (primaryOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      primaryParses primaryRejects)
    (fallbackOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      fallbackParses fallbackRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.TransactionalFallbackOrdinaryParses primaryParses
        primaryRejects fallbackParses)
      (DeclarativeGrammar.TransactionalFallbackRejects primaryRejects
        fallbackRejects) :=
  DeclarativeGrammar.transactionalFallbackDeterministicOutcomeSpec
    primaryParses fallbackParses primaryRejects fallbackRejects
      primaryOutcomes fallbackOutcomes

end Solcore.Syntax.Parser.TermInternals
