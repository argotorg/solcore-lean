import Solcore.Syntax.Parser.CoreMatchCasesOrdinarySuccessSoundnessProperties

/-! Exact rejection for the guarded Core match-case loop. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

private theorem keyword_eq_ok_of_isKeyword_eq_true (value : HardKeyword)
    (context : ParseContext) {input : State}
    (present : isKeyword input value = true) :
    ∃ token, keyword value context input =
      .ok token { input with cursor := input.cursor + 1 } := by
  unfold isKeyword State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      change (token.value == .keyword value) = true at present
      refine ⟨token, ?_⟩
      unfold keyword acceptToken
      simp only [found, present, if_true]

private theorem keywordPresentAt_of_isKeyword_eq_true (value : HardKeyword)
    {input : State} (present : isKeyword input value = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .keyword value } := by
  rcases keyword_eq_ok_of_isKeyword_eq_true value .statement present with
    ⟨token, result⟩
  have parsed := keyword_success_exactTokenParses value .statement result
  exact ⟨token.span, parsed.1⟩

/-- Every arbitrary-fuel rejection records the first rejected arm after the
exact ordinary prefix; the prior reverse accumulator does not affect it. -/
theorem matchCasesWithFuel_reject_ordinary_sound
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
    ∀ fuel casesRev input failure rejected,
      matchCases statement pattern fuel casesRev input =
        .reject failure rejected →
      DeclarativeGrammar.MatchCasesRejects statementOrdinary statementRejects
        patternOrdinary patternRejects input.declarativeRemainder
          rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro casesRev input failure rejected result
      simp [matchCases] at result
  | succ fuel inductionHypothesis =>
      intro casesRev input failure rejected result
      unfold matchCases at result
      cases casePresent : isKeyword input .caseKw with
      | false => simp [casePresent] at result
      | true =>
          simp only [casePresent, if_true] at result
          cases armResult : matchCase statement pattern input with
          | invariant error => simp [armResult] at result
          | reject armFailure armRejected =>
              simp only [armResult] at result
              cases result
              exact .firstRejected
                (keywordPresentAt_of_isKeyword_eq_true .caseKw casePresent)
                (matchCase_reject_ordinary_sound statement pattern
                  statementOrdinary statementRejects patternRejects
                    patternOrdinary statementSuccessSound
                      statementRejectSound patternSuccessSound
                        patternRejectSound armResult)
          | ok arm afterArm =>
              simp only [armResult] at result
              by_cases progress : afterArm.cursor > input.cursor
              · simp only [progress, if_true] at result
                exact .laterRejected
                  (matchCase_success_ordinary_sound statement pattern
                    statementOrdinary statementRejects patternOrdinary
                      statementSuccessSound statementRejectSound
                        patternSuccessSound armResult)
                  (by simpa [State.declarativeRemainder] using progress)
                  (inductionHypothesis (arm :: casesRev) afterArm failure
                    rejected result)
              · simp only [progress, if_false] at result
                contradiction

/-- Production-sized loop rejection has the exact guarded relation. -/
theorem matchCases_reject_ordinary_sound
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
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : matchCases statement pattern (input.remainingCount + 1) [] input
      = .reject failure rejected) :
    DeclarativeGrammar.MatchCasesRejects statementOrdinary statementRejects
      patternOrdinary patternRejects input.declarativeRemainder
        rejected.declarativeRemainder :=
  matchCasesWithFuel_reject_ordinary_sound statement pattern
    statementOrdinary statementRejects patternOrdinary patternRejects
    statementSuccessSound statementRejectSound patternSuccessSound
    patternRejectSound (input.remainingCount + 1) [] input failure rejected
    result

end Solcore.Syntax.Parser.MatchInternals
