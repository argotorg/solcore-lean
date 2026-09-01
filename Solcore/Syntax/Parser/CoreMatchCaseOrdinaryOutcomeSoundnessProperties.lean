import Solcore.Syntax.DeclarativeCoreMatchCaseOutcomeProperties
import Solcore.Syntax.Parser.CoreBlockOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.Statement.Match
import Solcore.Syntax.Parser.YulKeywordRejectionSoundnessProperties

/-! Executable ordinary success and exact rejection for one Core match case. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/-- Every executable match-case success retains its marker, pattern, raw
required block, span, and exact remainder. -/
theorem matchCase_success_ordinary_sound
    (statement : Parser Statement) (pattern : Parser Pattern)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
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
    {input output : State} {arm : MatchCase}
    (result : matchCase statement pattern input = .ok arm output) :
    DeclarativeGrammar.MatchCaseOrdinaryParses statementOrdinary
      patternOrdinary input.declarativeRemainder arm
        output.declarativeRemainder := by
  unfold matchCase at result
  cases markerResult : keyword .caseKw .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject failure rejected => simp [bind, markerResult] at result
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases patternResult : pattern afterMarker with
      | invariant error => simp [patternResult] at result
      | reject failure rejected => simp [patternResult] at result
      | ok retainedPattern afterPattern =>
          simp only [patternResult] at result
          cases bodyResult : coreBlock statement .require afterPattern with
          | invariant error => simp [bodyResult] at result
          | reject failure rejected => simp [bodyResult] at result
          | ok body afterBody =>
              simp only [bodyResult, pure] at result
              cases result
              exact .parsed marker.span
                (keyword_success_exactTokenParses .caseKw .statement
                  markerResult)
                (patternSuccessSound patternResult)
                ((coreBlock_ordinaryOutcome_sound statement .require
                  statementOrdinary statementRejects statementSuccessSound
                    statementRejectSound).1 bodyResult)

/-- Every executable match-case rejection records its first failing stage. -/
theorem matchCase_reject_ordinary_sound
    (statement : Parser Statement) (pattern : Parser Pattern)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects patternRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
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
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : matchCase statement pattern input = .reject failure rejected) :
    DeclarativeGrammar.MatchCaseRejects statementOrdinary statementRejects
      patternOrdinary patternRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold matchCase at result
  cases markerResult : keyword .caseKw .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have rejectedEq := keyword_reject_state_eq .caseKw .statement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (keyword_reject_tokenKindAbsentAt .caseKw .statement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := keyword_success_exactTokenParses .caseKw .statement
        markerResult
      cases patternResult : pattern afterMarker with
      | invariant error => simp [patternResult] at result
      | reject patternFailure patternRejected =>
          simp only [patternResult] at result
          cases result
          exact .patternRejected marker.span markerParsed
            (patternRejectSound patternResult)
      | ok retainedPattern afterPattern =>
          simp only [patternResult] at result
          cases bodyResult : coreBlock statement .require afterPattern with
          | invariant error => simp [bodyResult] at result
          | reject bodyFailure bodyRejected =>
              simp only [bodyResult] at result
              cases result
              exact .bodyRejected marker.span markerParsed
                (patternSuccessSound patternResult)
                ((coreBlock_ordinaryOutcome_sound statement .require
                  statementOrdinary statementRejects statementSuccessSound
                    statementRejectSound).2 bodyResult)
          | ok body output => simp [bodyResult, pure] at result

/-- Package both executable match-case outcomes. -/
theorem matchCase_ordinaryOutcome_sound
    (statement : Parser Statement) (pattern : Parser Pattern)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects patternRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
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
    (∀ {input output : State} {arm : MatchCase},
      matchCase statement pattern input = .ok arm output →
        DeclarativeGrammar.MatchCaseOrdinaryParses statementOrdinary
          patternOrdinary input.declarativeRemainder arm
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      matchCase statement pattern input = .reject failure rejected →
        DeclarativeGrammar.MatchCaseRejects statementOrdinary
          statementRejects patternOrdinary patternRejects
            input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨matchCase_success_ordinary_sound statement pattern statementOrdinary
      statementRejects patternOrdinary statementSuccessSound
        statementRejectSound patternSuccessSound,
    matchCase_reject_ordinary_sound statement pattern statementOrdinary
      statementRejects patternRejects patternOrdinary statementSuccessSound
        statementRejectSound patternSuccessSound patternRejectSound⟩

/-- Re-export deterministic match-case outcomes. -/
theorem matchCase_ordinaryOutcomeSpec
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
      (DeclarativeGrammar.MatchCaseOrdinaryParses statementOrdinary
        patternOrdinary)
      (DeclarativeGrammar.MatchCaseRejects statementOrdinary statementRejects
        patternOrdinary patternRejects) :=
  DeclarativeGrammar.matchCaseDeterministicOutcomeSpec statementOutcomes
    patternOutcomes

end Solcore.Syntax.Parser.MatchInternals
