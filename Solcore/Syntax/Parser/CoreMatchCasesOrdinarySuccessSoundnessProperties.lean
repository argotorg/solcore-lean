import Solcore.Syntax.DeclarativeCoreMatchCasesOutcomeProperties
import Solcore.Syntax.Parser.CoreMatchCaseOrdinaryOutcomeSoundnessProperties

/-!
Diagnostic-inclusive success for the fuel-bounded, reverse-accumulating Core
match-case loop.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/-- An arbitrary successful loop retains the prior reverse accumulator and
describes its newly parsed suffix in forward source order. -/
theorem matchCasesWithFuel_success_ordinary_sound
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
        input.declarativeRemainder value output.declarativeRemainder) :
    ∀ fuel casesRev input cases output,
      matchCases statement pattern fuel casesRev input = .ok cases output →
      ∃ suffix,
        cases = casesRev.reverse ++ suffix ∧
        DeclarativeGrammar.MatchCasesOrdinaryParses statementOrdinary
          patternOrdinary input.declarativeRemainder suffix
            output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro casesRev input cases output result
      simp [matchCases] at result
  | succ fuel inductionHypothesis =>
      intro casesRev input cases output result
      unfold matchCases at result
      cases casePresent : isKeyword input .caseKw with
      | false =>
          simp only [casePresent, Bool.false_eq_true, if_false] at result
          cases result
          exact ⟨[], by simp, .done
            (keywordAbsentAt_of_isKeyword_eq_false .caseKw casePresent)⟩
      | true =>
          simp only [casePresent, if_true] at result
          cases armResult : matchCase statement pattern input with
          | invariant error => simp [armResult] at result
          | reject failure rejected => simp [armResult] at result
          | ok arm afterArm =>
              simp only [armResult] at result
              by_cases progress : afterArm.cursor > input.cursor
              · simp only [progress, if_true] at result
                rcases inductionHypothesis (arm :: casesRev) afterArm cases
                    output result with ⟨suffix, casesEq, tailParsed⟩
                refine ⟨arm :: suffix, ?_, .next
                  (matchCase_success_ordinary_sound statement pattern
                    statementOrdinary statementRejects patternOrdinary
                      statementSuccessSound statementRejectSound
                        patternSuccessSound armResult)
                  (by simpa [State.declarativeRemainder] using progress)
                  tailParsed⟩
                simpa [List.reverse_cons, List.append_assoc] using casesEq
              · simp only [progress, if_false] at result
                contradiction

/-- The production fuel and empty accumulator expose the exact forward list. -/
theorem matchCases_success_ordinary_sound
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
    {input output : State} {cases : List MatchCase}
    (result : matchCases statement pattern (input.remainingCount + 1) [] input
      = .ok cases output) :
    DeclarativeGrammar.MatchCasesOrdinaryParses statementOrdinary
      patternOrdinary input.declarativeRemainder cases
        output.declarativeRemainder := by
  rcases matchCasesWithFuel_success_ordinary_sound statement pattern
      statementOrdinary statementRejects patternOrdinary
      statementSuccessSound statementRejectSound patternSuccessSound
      (input.remainingCount + 1) [] input cases output result with
    ⟨suffix, casesEq, parsed⟩
  simp only [List.reverse_nil, List.nil_append] at casesEq
  subst cases
  exact parsed

end Solcore.Syntax.Parser.MatchInternals
