import Solcore.Syntax.Parser.CoreMatchCasesOrdinaryRejectionSoundnessProperties

/-! Packaged production outcomes for the Core match-case loop. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/-- Package success and rejection for the exact production fuel selection. -/
theorem matchCases_ordinaryOutcome_sound
    (statement : Parser Statement) (pattern : Parser Pattern)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (patternRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (patternSuccessSound : ∀ {input output : State} {value : Pattern},
      pattern input = .ok value output → patternOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (patternRejectSound : ∀ {input rejected : State} {failure : Failure},
      pattern input = .reject failure rejected → patternRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {cases : List MatchCase},
      matchCases statement pattern (input.remainingCount + 1) [] input =
          .ok cases output →
        DeclarativeGrammar.MatchCasesOrdinaryParses statementOrdinary
          patternOrdinary input.declarativeRemainder cases
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      matchCases statement pattern (input.remainingCount + 1) [] input =
          .reject failure rejected →
        DeclarativeGrammar.MatchCasesRejects statementOrdinary
          statementRejects patternOrdinary patternRejects
            input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨matchCases_success_ordinary_sound statement pattern statementOrdinary
      statementRejects patternOrdinary statementSuccessSound
        statementRejectSound patternSuccessSound,
    matchCases_reject_ordinary_sound statement pattern statementOrdinary
      statementRejects patternOrdinary patternRejects statementSuccessSound
        statementRejectSound patternSuccessSound patternRejectSound⟩

/-- Re-export deterministic match-case sequence outcomes. -/
theorem matchCases_ordinaryOutcomeSpec
    {statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop}
    {statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop}
    {patternRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (statementOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      statementOrdinary statementRejects)
    (patternOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      patternOrdinary patternRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.MatchCasesOrdinaryParses statementOrdinary
        patternOrdinary)
      (DeclarativeGrammar.MatchCasesRejects statementOrdinary
        statementRejects patternOrdinary patternRejects) :=
  DeclarativeGrammar.matchCasesDeterministicOutcomeSpec statementOutcomes
    patternOutcomes

end Solcore.Syntax.Parser.MatchInternals
