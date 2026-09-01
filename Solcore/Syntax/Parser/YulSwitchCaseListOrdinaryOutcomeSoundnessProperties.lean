import Solcore.Syntax.Parser.YulSwitchCaseArmOrdinaryOutcomeSoundnessProperties

/-!
Executable ordinary-success and rejection bridges for the fuel-bounded,
reverse-accumulating Yul switch case loop.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.YulControl

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
  rcases keyword_eq_ok_of_isKeyword_eq_true value .yulStatement present with
    ⟨token, result⟩
  have parsed := keyword_success_exactTokenParses value .yulStatement result
  exact ⟨token.span, parsed.1⟩

/-- The executable reverse accumulator is the prefix of the returned cases;
the ordinary relation describes the remaining forward maximal suffix. -/
theorem caseList_success_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder) :
    ∀ fuel casesRev input cases output,
      caseList statement fuel casesRev input = .ok cases output →
      ∃ suffix,
        cases = casesRev.reverse ++ suffix ∧
        DeclarativeGrammar.YulCaseListOrdinaryParses statementOrdinary
          input.declarativeRemainder suffix output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro casesRev input cases output result
      simp [caseList] at result
  | succ fuel inductionHypothesis =>
      intro casesRev input cases output result
      unfold caseList at result
      cases casePresent : isKeyword input .caseKw with
      | false =>
          simp only [casePresent, Bool.false_eq_true, if_false] at result
          cases result
          exact ⟨[], by simp,
            .done (keywordAbsentAt_of_isKeyword_eq_false .caseKw
              casePresent)⟩
      | true =>
          simp only [casePresent, if_true] at result
          cases armResult : caseArm statement input with
          | invariant error => simp [armResult] at result
          | reject failure rejected => simp [armResult] at result
          | ok arm afterArm =>
              simp only [armResult] at result
              by_cases progress : afterArm.cursor > input.cursor
              · simp only [progress, if_true] at result
                rcases inductionHypothesis (arm :: casesRev) afterArm cases
                    output result with ⟨suffix, casesEq, tailGrammar⟩
                refine ⟨arm :: suffix, ?_,
                  .next
                    (caseArm_success_ordinary_sound statement
                      statementOrdinary statementSuccessSound armResult)
                    (by simpa [State.declarativeRemainder] using progress)
                    tailGrammar⟩
                simpa [List.reverse_cons, List.append_assoc] using casesEq
              · simp only [progress, if_false] at result
                contradiction

/-- Every executable case-list rejection records the first rejected arm
after its exact ordinary prefix. -/
theorem caseList_reject_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder) :
    ∀ fuel casesRev input failure rejected,
      caseList statement fuel casesRev input = .reject failure rejected →
      DeclarativeGrammar.YulCaseListRejects statementOrdinary
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro casesRev input failure rejected result
      simp [caseList] at result
  | succ fuel inductionHypothesis =>
      intro casesRev input failure rejected result
      unfold caseList at result
      cases casePresent : isKeyword input .caseKw with
      | false =>
          simp [casePresent] at result
      | true =>
          simp only [casePresent, if_true] at result
          cases armResult : caseArm statement input with
          | invariant error => simp [armResult] at result
          | reject armFailure armRejected =>
              simp only [armResult] at result
              cases result
              exact .firstRejected
                (keywordPresentAt_of_isKeyword_eq_true .caseKw casePresent)
                (caseArm_reject_ordinary_sound statement statementOrdinary
                  statementRejects statementSuccessSound statementRejectSound
                  armResult)
          | ok arm afterArm =>
              simp only [armResult] at result
              by_cases progress : afterArm.cursor > input.cursor
              · simp only [progress, if_true] at result
                exact .laterRejected
                  (caseArm_success_ordinary_sound statement statementOrdinary
                    statementSuccessSound armResult)
                  (by simpa [State.declarativeRemainder] using progress)
                  (inductionHypothesis (arm :: casesRev) afterArm failure
                    rejected result)
              · simp only [progress, if_false] at result
                contradiction

end Solcore.Syntax.Parser.YulControl
