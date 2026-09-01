import Solcore.Syntax.DeclarativeYulSwitchOutcomeProperties
import Solcore.Syntax.Parser.YulExpressionPublicFuelSoundnessProperties
import Solcore.Syntax.Parser.YulKeywordRejectionSoundnessProperties
import Solcore.Syntax.Parser.YulSwitchCaseListOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.YulSwitchDefaultOrdinaryOutcomeSoundnessProperties

/-!
Executable ordinary-success and exact-rejection bridges for complete inline-
Yul switches, including the diagnosed empty-case `.error` success.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem yulSwitchEnd_map_eq (scrutineeSpan : SourceSpan)
    (cases : List YulCase) (defaultBody : Option YulParsedBlock) :
    DeclarativeGrammar.yulSwitchEnd scrutineeSpan cases
        (defaultBody.map (fun body => body.span)) =
      match defaultBody with
      | some body => body.span
      | none => match cases.reverse with
        | last :: _ => last.span
        | [] => scrutineeSpan := by
  cases defaultBody <;> rfl

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

/-- Every executable switch success follows the ordinary switch relation.
The mandatory no-case diagnostic is erased only from the declarative
remainder, while its `.error` value and exact output cursor are retained. -/
theorem yulSwitchStatement_success_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    {input output : State} {value : YulStmt}
    (result : yulSwitchStatement statement input = .ok value output) :
    DeclarativeGrammar.YulSwitchStatementOrdinaryParses statementOrdinary
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold yulSwitchStatement at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, scrutineeStage⟩
  rcases bind_ok_components scrutineeStage with
    ⟨scrutinee, afterScrutinee, scrutineeResult, casesStage⟩
  rcases bind_ok_components casesStage with
    ⟨cases, afterCases, casesResult, defaultStage⟩
  rcases bind_ok_components defaultStage with
    ⟨defaultBody, afterDefault, defaultResult, finished⟩
  have markerParsed := keyword_success_exactTokenParses .switchKw
    .yulStatement markerResult
  have scrutineeParsed := yulExpression_success_ordinary_sound
    scrutineeResult
  rcases YulControl.caseList_success_ordinary_sound statement
      statementOrdinary statementSuccessSound
      (afterScrutinee.remainingCount + 1) [] afterScrutinee cases afterCases
      casesResult with ⟨suffix, casesEq, casesParsed⟩
  have suffixEq : suffix = cases := by simpa using casesEq.symm
  subst suffix
  have defaultParsed := YulControl.optionalDefault_success_ordinary_sound
    statement statementOrdinary statementSuccessSound defaultResult
  have endEq := yulSwitchEnd_map_eq scrutinee.span cases defaultBody
  cases cases with
  | nil =>
      rcases bind_ok_components finished with
        ⟨emitted, afterEmit, emittedResult, completed⟩
      cases completed
      unfold emitDiagnostic modifyState at emittedResult
      cases emittedResult
      have ordinary :=
        DeclarativeGrammar.YulSwitchStatementOrdinaryParses.empty
          marker.span markerParsed scrutineeParsed casesParsed defaultParsed
      rw [endEq] at ordinary
      change DeclarativeGrammar.YulSwitchStatementOrdinaryParses
        statementOrdinary input.declarativeRemainder _
          afterDefault.declarativeRemainder
      exact ordinary
  | cons head tail =>
      cases finished
      have ordinary :=
        DeclarativeGrammar.YulSwitchStatementOrdinaryParses.nonempty
          marker.span markerParsed scrutineeParsed casesParsed defaultParsed
      rw [endEq] at ordinary
      exact ordinary

/-- Every executable switch rejection identifies its exact sequential stage
and retains the rejected remainder reported by that stage. -/
theorem yulSwitchStatement_reject_ordinary_sound
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
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : yulSwitchStatement statement input = .reject failure rejected) :
    DeclarativeGrammar.YulSwitchStatementRejects statementOrdinary
      statementRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold yulSwitchStatement at result
  cases markerResult : keyword .switchKw .yulStatement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have rejectedEq := keyword_reject_state_eq .switchKw .yulStatement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (keyword_reject_tokenKindAbsentAt .switchKw .yulStatement
          markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases scrutineeResult : yulExpression afterMarker with
      | invariant error => simp [scrutineeResult] at result
      | reject scrutineeFailure scrutineeRejected =>
          simp only [scrutineeResult] at result
          cases result
          exact .scrutineeRejected marker.span
            (keyword_success_exactTokenParses .switchKw .yulStatement
              markerResult)
            (yulExpression_reject_sound scrutineeResult)
      | ok scrutinee afterScrutinee =>
          simp only [scrutineeResult] at result
          cases casesResult : YulControl.caseList statement
              (afterScrutinee.remainingCount + 1) [] afterScrutinee with
          | invariant error => simp [casesResult] at result
          | reject casesFailure casesRejected =>
              have casesRejection :=
                YulControl.caseList_reject_ordinary_sound statement
                  statementOrdinary statementRejects statementSuccessSound
                  statementRejectSound (afterScrutinee.remainingCount + 1) []
                  afterScrutinee casesFailure casesRejected casesResult
              simp only [casesResult] at result
              cases result
              exact .casesRejected marker.span
                (keyword_success_exactTokenParses .switchKw .yulStatement
                  markerResult)
                (yulExpression_success_ordinary_sound scrutineeResult)
                casesRejection
          | ok cases afterCases =>
              simp only [casesResult] at result
              cases defaultResult : YulControl.optionalDefault statement
                  afterCases with
              | invariant error => simp [defaultResult] at result
              | reject defaultFailure defaultRejected =>
                  have defaultRejection :=
                    YulControl.optionalDefault_reject_ordinary_sound
                      statement statementOrdinary statementRejects
                      statementSuccessSound statementRejectSound
                      defaultResult
                  simp only [defaultResult] at result
                  cases result
                  rcases YulControl.caseList_success_ordinary_sound statement
                      statementOrdinary statementSuccessSound
                      (afterScrutinee.remainingCount + 1) [] afterScrutinee
                      cases afterCases casesResult with
                    ⟨suffix, casesEq, casesParsed⟩
                  have suffixEq : suffix = cases := by
                    simpa using casesEq.symm
                  subst suffix
                  exact .defaultRejected marker.span
                    (keyword_success_exactTokenParses .switchKw .yulStatement
                      markerResult)
                    (yulExpression_success_ordinary_sound scrutineeResult)
                    casesParsed
                    defaultRejection
              | ok defaultBody afterDefault =>
                  simp only [defaultResult] at result
                  cases cases <;> simp [emitDiagnostic, modifyState, pure]
                    at result

end Solcore.Syntax.Parser
