import Solcore.Syntax.Parser.Yul.ControlProperties
import Solcore.Syntax.Parser.Yul.ExpressionProperties

/-! Contracts for complete canonical inline-Yul switch statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem switchBind_ok_components {α β : Type} {first : Parser α}
    {next : α → Parser β} {input final : State} {value : β}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst, first input = .ok firstValue afterFirst ∧
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

/-- Yul switch parsing preserves all recursive arm and default ranges. -/
theorem yulSwitchStatement_validFor (statement : Parser YulStmt)
    (statementValid : statement.ValidFor YulStmt.ValidFor)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    (yulSwitchStatement statement).ValidFor YulStmt.ValidFor := by
  intro input inputValid
  unfold yulSwitchStatement
  cases markerResult : keyword .switchKw .yulStatement input with
  | invariant error => simp only [bind, markerResult, Reply.ValidFor]
  | reject failure rejected =>
      have valid := keyword_validFor .switchKw .yulStatement input inputValid
      rw [markerResult] at valid
      simp only [bind, markerResult, Reply.ValidFor]
      exact valid
  | ok marker afterMarker =>
      have markerValid := keyword_validFor .switchKw .yulStatement input inputValid
      rw [markerResult] at markerValid
      simp only [bind, markerResult]
      cases scrutineeResult : yulExpression afterMarker with
      | invariant error => trivial
      | reject failure rejected =>
          have valid := yulExpression_validFor afterMarker markerValid.2.1
          rw [scrutineeResult] at valid
          exact valid.of_file_eq markerValid.2.2
      | ok scrutinee afterScrutinee =>
          have scrutineeValid := yulExpression_validFor afterMarker
            markerValid.2.1
          rw [scrutineeResult] at scrutineeValid
          simp only
          cases casesResult : YulControl.caseList statement
              (afterScrutinee.remainingCount + 1) [] afterScrutinee with
          | invariant error => simp only [Reply.ValidFor]
          | reject failure rejected =>
              have valid := yulCases_validFor statement statementValid
                statementPreserves (afterScrutinee.remainingCount + 1)
                afterScrutinee scrutineeValid.2.1
              rw [casesResult] at valid
              simp only [Reply.ValidFor]
              exact valid.of_file_eq
                (scrutineeValid.2.2.trans markerValid.2.2)
          | ok cases afterCases =>
              have casesValid := yulCases_validFor statement statementValid
                statementPreserves (afterScrutinee.remainingCount + 1)
                afterScrutinee scrutineeValid.2.1
              rw [casesResult] at casesValid
              simp only
              cases defaultResult : YulControl.optionalDefault statement
                  afterCases with
              | invariant error => simp only [Reply.ValidFor]
              | reject failure rejected =>
                  have valid := optionalYulDefault_validFor statement
                    statementValid statementPreserves afterCases casesValid.2.1
                  rw [defaultResult] at valid
                  simp only [Reply.ValidFor]
                  exact valid.of_file_eq (casesValid.2.2.trans
                    (scrutineeValid.2.2.trans markerValid.2.2))
              | ok defaultBody afterDefault =>
                  have defaultValid := optionalYulDefault_validFor statement
                    statementValid statementPreserves afterCases casesValid.2.1
                  rw [defaultResult] at defaultValid
                  simp only
                  have markerSpanValid : marker.span.ValidFor input.file := by
                    simpa only [Located.ValidFor] using markerValid.1
                  have scrutineeInput : YulExpr.ValidFor input.file scrutinee := by
                    simpa [markerValid.2.2] using scrutineeValid.1
                  have scrutineeSpanValid : scrutinee.span.ValidFor input.file := by
                    cases scrutineeInput <;> assumption
                  have casesInput : List.ValidFor YulCase.ValidFor input.file cases := by
                    simpa [scrutineeValid.2.2, markerValid.2.2] using casesValid.1
                  have defaultInput : Option.ValidFor
                      (YulParsedBlock.ValidFor YulStmt.ValidFor) input.file
                      defaultBody := by
                    simpa [casesValid.2.2, scrutineeValid.2.2,
                      markerValid.2.2] using defaultValid.1
                  have markerShape := acceptToken_ok_state_shape
                    (.keyword .switchKw) .yulStatement
                    (· == .keyword .switchKw) markerResult
                  have markerAt := State.getElem?_eq_some_of_peek?_eq_some
                    markerShape.1
                  rcases yulExpression_startsAtCurrentTokenOnSuccess afterMarker
                      scrutinee afterScrutinee scrutineeResult with
                    ⟨first, firstFound, scrutineeStart⟩
                  have markerAdvanced : input.advance? = some (marker, afterMarker) := by
                    unfold State.advance?; rw [markerShape.1, markerShape.2]; rfl
                  have markerBeforeScrutinee :
                      marker.span.endByte ≤ scrutinee.span.startByte := by
                    rw [← scrutineeStart]
                    exact inputValid.consumed_end_le_peek_start_after_advance
                      markerAdvanced firstFound
                  have expressionCursor := yulExpression_cursorMonotoneOnSuccess
                    afterMarker scrutinee afterScrutinee scrutineeResult
                  have markerAtScrutinee :
                      afterScrutinee.tokens[input.cursor]? = some marker := by
                    simpa [yulExpression_preservesTokensOnSuccess afterMarker
                      scrutinee afterScrutinee scrutineeResult,
                      keyword_preservesTokensOnSuccess .switchKw .yulStatement
                        input marker afterMarker markerResult] using markerAt
                  have markerBeforeCursor : input.cursor < afterScrutinee.cursor := by
                    have : input.cursor + 1 ≤ afterScrutinee.cursor := by
                      simpa [markerShape.2] using expressionCursor
                    omega
                  have casesOrdered := yulCases_ordered_after statement
                    statementValid statementPreserves
                    (afterScrutinee.remainingCount + 1) [] afterScrutinee cases
                    afterCases input.cursor marker scrutineeValid.2.1
                    markerAtScrutinee markerBeforeCursor (by simp) casesResult
                  have casesCursor := yulCases_cursorMonotoneOnSuccess statement
                    (afterScrutinee.remainingCount + 1) [] afterScrutinee cases
                    afterCases casesResult
                  have markerAtCases : afterCases.tokens[input.cursor]? = some marker := by
                    simpa [yulCases_preservesTokensOnSuccess statement
                      statementPreserves (afterScrutinee.remainingCount + 1) []
                      afterScrutinee cases afterCases casesResult] using
                      markerAtScrutinee
                  have markerBeforeCasesCursor : input.cursor < afterCases.cursor :=
                    Nat.lt_of_lt_of_le markerBeforeCursor casesCursor
                  let endSpan := match defaultBody with
                    | some body => body.span
                    | none => match cases.reverse with
                      | last :: _ => last.span
                      | [] => scrutinee.span
                  have endpoint : endSpan.ValidFor input.file ∧
                      marker.span.startByte ≤ endSpan.endByte := by
                    cases defaultBody with
                    | some body =>
                        have bodyValid : body.span.ValidFor input.file := by
                          exact defaultInput.1
                        simp only [endSpan]
                        change body.span.ValidFor input.file ∧
                          marker.span.startByte ≤ body.span.endByte
                        exact ⟨bodyValid, Nat.le_trans markerSpanValid.2.1
                          (Nat.le_trans (optionalYulDefault_some_ordered_after
                            statement statementPreserves casesValid.2.1
                            markerAtCases markerBeforeCasesCursor defaultResult)
                            bodyValid.2.1)⟩
                    | none =>
                        cases reversed : cases.reverse with
                        | nil =>
                            simp only [endSpan, reversed]
                            change scrutinee.span.ValidFor input.file ∧
                              marker.span.startByte ≤ scrutinee.span.endByte
                            exact ⟨scrutineeSpanValid,
                            Nat.le_trans markerSpanValid.2.1
                              (Nat.le_trans markerBeforeScrutinee
                                scrutineeSpanValid.2.1)⟩
                        | cons last rest =>
                            have member : last ∈ cases := by
                              have : last ∈ cases.reverse := by rw [reversed]; simp
                              simpa using this
                            have valid := (casesInput last member).span_valid
                            simp only [endSpan, reversed]
                            change last.span.ValidFor input.file ∧
                              marker.span.startByte ≤ last.span.endByte
                            exact ⟨valid, Nat.le_trans markerSpanValid.2.1
                              (Nat.le_trans (casesOrdered last member) valid.2.1)⟩
                  have outerValid := SourceSpan.cover_validFor markerSpanValid
                    endpoint.1 endpoint.2
                  cases cases with
                  | cons head tail =>
                      simp only
                      exact ⟨YulStmt.ValidFor.switch outerValid scrutineeInput
                          (by
                            intro arm member
                            exact casesInput arm (by
                              simpa [NonemptyList.toList] using member))
                          (by
                            intro statements member retained retainedMember
                            cases defaultBody with
                            | none => contradiction
                            | some body =>
                                simp at member; subst statements
                                exact defaultInput.2 retained retainedMember),
                        defaultValid.2.1,
                        defaultValid.2.2.trans (casesValid.2.2.trans
                          (scrutineeValid.2.2.trans markerValid.2.2))⟩
                  | nil =>
                      simp only
                      unfold emitDiagnostic modifyState Reply.ValidFor
                      exact ⟨YulStmt.ValidFor.error outerValid,
                        defaultValid.2.1.emit_validFor _
                          (by
                            rw [defaultValid.2.2, casesValid.2.2,
                              scrutineeValid.2.2, markerValid.2.2]
                            exact outerValid),
                        defaultValid.2.2.trans (casesValid.2.2.trans
                          (scrutineeValid.2.2.trans markerValid.2.2))⟩

/-- Yul switch parsing preserves the immutable lexer token carrier. -/
theorem yulSwitchStatement_preservesTokensOnSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    Parser.PreservesTokensOnSuccess (yulSwitchStatement statement) := by
  unfold yulSwitchStatement
  apply Parser.bind_preservesTokensOnSuccess
    (keyword_preservesTokensOnSuccess .switchKw .yulStatement)
  intro marker
  apply Parser.bind_preservesTokensOnSuccess
    yulExpression_preservesTokensOnSuccess
  intro scrutinee
  apply Parser.bind_preservesTokensOnSuccess
  · intro input cases next result
    exact yulCases_preservesTokensOnSuccess statement statementPreserves
      (input.remainingCount + 1) [] input cases next result
  intro cases
  apply Parser.bind_preservesTokensOnSuccess
    (optionalYulDefault_preservesTokensOnSuccess statement statementPreserves)
  intro defaultBody
  cases cases with
  | cons head tail => exact Parser.pure_preservesTokensOnSuccess _
  | nil =>
      apply Parser.bind_preservesTokensOnSuccess
        (emitDiagnostic_preservesTokensOnSuccess _)
      intro _emitted
      exact Parser.pure_preservesTokensOnSuccess _

/-- Yul switch parsing never rewinds the parser cursor. -/
theorem yulSwitchStatement_cursorMonotoneOnSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    Parser.CursorMonotoneOnSuccess (yulSwitchStatement statement) := by
  unfold yulSwitchStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .switchKw .yulStatement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    yulExpression_cursorMonotoneOnSuccess
  intro scrutinee
  apply Parser.bind_cursorMonotoneOnSuccess
  · intro input cases next result
    exact yulCases_cursorMonotoneOnSuccess statement
      (input.remainingCount + 1) [] input cases next result
  intro cases
  apply Parser.bind_cursorMonotoneOnSuccess
    (optionalYulDefault_cursorMonotoneOnSuccess statement statementPreserves)
  intro defaultBody
  cases cases with
  | cons head tail => exact Parser.pure_cursorMonotoneOnSuccess _
  | nil =>
      apply Parser.bind_cursorMonotoneOnSuccess
        (emitDiagnostic_cursorMonotoneOnSuccess _)
      intro _emitted
      exact Parser.pure_cursorMonotoneOnSuccess _

/-- A successful Yul switch starts at its current `switch` token. -/
theorem yulSwitchStatement_startsAtCurrentTokenOnSuccess
    (statement : Parser YulStmt) :
    Parser.StartsAtCurrentTokenOnSuccess
      (yulSwitchStatement statement) (·.span) := by
  unfold yulSwitchStatement
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess
      (.keyword .switchKw) .yulStatement (· == .keyword .switchKw))
  intro marker input value final parsed
  rcases switchBind_ok_components parsed with ⟨scrutinee, afterScrutinee, _, rest⟩
  rcases switchBind_ok_components rest with ⟨cases, afterCases, _, rest⟩
  rcases switchBind_ok_components rest with ⟨defaultBody, afterDefault, _, rest⟩
  cases cases with
  | cons head tail => cases rest; rfl
  | nil =>
      rcases switchBind_ok_components rest with
        ⟨_emitted, afterEmit, _, finished⟩
      cases finished
      rfl

end Solcore.Syntax.Parser
