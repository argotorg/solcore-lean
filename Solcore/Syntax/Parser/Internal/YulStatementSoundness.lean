import Solcore.Syntax.Parser.Internal.YulBlockSoundness
import Solcore.Syntax.Parser.Internal.YulExpressionSoundness
import Solcore.Syntax.Parser.Yul
import Solcore.Syntax.Yul
import Solcore.Syntax.Internal.YulBlockOutcomes
import Solcore.Syntax.Grammar.Yul
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Internal.DelimitedOutcomes

/-!
Soundness of the parsers of Yul statements: each success and each rejection has its
declarative derivation, and diagnostic-free runs reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.ControlSwitchProperties
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

private theorem emitDiagnostic_preservesTokenWindowForYulSwitch
    (diagnostic : ParseDiagnostic) :
    Parser.PreservesTokenWindow (emitDiagnostic diagnostic) := by
  intro input
  unfold emitDiagnostic modifyState Reply.PreservesTokenWindow
  exact ⟨rfl, rfl⟩

/-- Yul switch parsing preserves every ordinary token window. -/
theorem yulSwitchStatement_preservesTokenWindow
    (statement : Parser YulStmt)
    (statementShape : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokenWindow (yulSwitchStatement statement) := by
  unfold yulSwitchStatement
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .switchKw .yulStatement)
  intro marker
  apply Parser.bind_preservesTokenWindow yulExpression_preservesTokenWindow
  intro scrutinee
  apply Parser.bind_preservesTokenWindow
  · intro input
    exact yulCases_preservesTokenWindow statement statementShape
      (input.remainingCount + 1) [] input
  intro cases
  apply Parser.bind_preservesTokenWindow
    (optionalYulDefault_preservesTokenWindow statement statementShape)
  intro defaultBody
  cases cases with
  | cons head tail => exact Parser.pure_preservesTokenWindow _
  | nil =>
      apply Parser.bind_preservesTokenWindow
        (emitDiagnostic_preservesTokenWindowForYulSwitch _)
      intro _emitted
      exact Parser.pure_preservesTokenWindow _

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
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.StatementProperties
/-! Compositional contracts for canonical inline-Yul leaf statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem yulExpr_span_valid {file : SourceFile} {value : YulExpr}
    (valid : YulExpr.ValidFor file value) : value.span.ValidFor file := by
  cases valid <;> assumption

private theorem yulStatementBind_ok_components {α β : Type}
    {first : Parser α} {next : α → Parser β} {input final : State}
    {value : β} (parsed : (first >>= next) input = .ok value final) :
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

/-- A block statement preserves its braces and every nested statement. -/
theorem yulBlockStatement_validFor (statement : Parser YulStmt)
    (statementValid : statement.ValidFor YulStmt.ValidFor)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    (yulBlockStatement statement).ValidFor YulStmt.ValidFor := by
  unfold yulBlockStatement
  apply Parser.bind_validFor_of_value
    (yulBlock_validFor YulStmt.ValidFor statement statementValid
      statementPreserves)
  intro block input inputValid blockValid
  exact ⟨YulStmt.ValidFor.block blockValid.1 blockValid.2,
    inputValid, rfl⟩

theorem yulBlockStatement_preservesTokensOnSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    Parser.PreservesTokensOnSuccess (yulBlockStatement statement) := by
  unfold yulBlockStatement
  apply Parser.bind_preservesTokensOnSuccess
    (yulBlock_preservesTokensOnSuccess statement statementPreserves)
  intro block
  exact Parser.pure_preservesTokensOnSuccess _

/-- Block statements preserve the nested parser's ordinary token window. -/
theorem yulBlockStatement_preservesTokenWindow (statement : Parser YulStmt)
    (statementShape : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokenWindow (yulBlockStatement statement) := by
  unfold yulBlockStatement
  apply Parser.bind_preservesTokenWindow
    (yulBlock_preservesTokenWindow statement statementShape)
  intro block
  exact Parser.pure_preservesTokenWindow _

theorem yulBlockStatement_cursorMonotoneOnSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    Parser.CursorMonotoneOnSuccess (yulBlockStatement statement) := by
  unfold yulBlockStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
  intro block
  exact Parser.pure_cursorMonotoneOnSuccess _

theorem yulBlockStatement_startsAtCurrentTokenOnSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    Parser.StartsAtCurrentTokenOnSuccess
      (yulBlockStatement statement) (·.span) := by
  unfold yulBlockStatement
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (yulBlock_startsAtCurrentTokenOnSuccess statement statementPreserves)
  intros
  cases ‹_ = Reply.ok _ _›
  rfl

/-- A Yul `let` initializer preserves a present expression's provenance. -/
theorem yulLetInitializer_validFor :
    yulLetInitializer.ValidFor (Option.ValidFor YulExpr.ValidFor) := by
  unfold yulLetInitializer
  apply Parser.bind_validFor getState_validFor
  intro state
  split
  · apply Parser.bind_validFor
      (symbol_validFor .colonEqual .yulStatement)
    intro marker
    apply Parser.bind_validFor_of_value yulExpression_validFor
    intro expression input inputValid expressionValid
    exact ⟨expressionValid, inputValid, rfl⟩
  · exact Parser.pure_validFor none _ (fun _ => trivial)

/-- Optional Yul `let` initialization preserves every token window. -/
theorem yulLetInitializer_preservesTokenWindow :
    Parser.PreservesTokenWindow yulLetInitializer := by
  unfold yulLetInitializer
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindow
  intro state
  split
  · apply Parser.bind_preservesTokenWindow
      (symbol_preservesTokenWindow .colonEqual .yulStatement)
    intro marker
    apply Parser.bind_preservesTokenWindow yulExpression_preservesTokenWindow
    intro expression
    exact Parser.pure_preservesTokenWindow _
  · exact Parser.pure_preservesTokenWindow none

/-- Optional Yul `let` initialization never rewinds the cursor. -/
theorem yulLetInitializer_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulLetInitializer := by
  unfold yulLetInitializer
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro state
  split
  · apply Parser.bind_cursorMonotoneOnSuccess
      (symbol_cursorMonotoneOnSuccess .colonEqual .yulStatement)
    intro marker
    apply Parser.bind_cursorMonotoneOnSuccess
      yulExpression_cursorMonotoneOnSuccess
    intro expression
    exact Parser.pure_cursorMonotoneOnSuccess _
  · exact Parser.pure_cursorMonotoneOnSuccess none

private theorem yulLetInitializer_some_components {input next : State}
    {expression : YulExpr}
    (parsed : yulLetInitializer input = .ok (some expression) next) :
    ∃ marker afterMarker,
      symbol .colonEqual .yulStatement input = .ok marker afterMarker ∧
        yulExpression afterMarker = .ok expression next := by
  unfold yulLetInitializer at parsed
  rcases yulStatementBind_ok_components parsed with
    ⟨state, afterState, stateResult, rest⟩
  unfold getState at stateResult
  cases stateResult
  split at rest
  · rcases yulStatementBind_ok_components rest with
      ⟨marker, afterMarker, markerResult, rest⟩
    rcases yulStatementBind_ok_components rest with
      ⟨value, afterValue, valueResult, finished⟩
    cases finished
    exact ⟨marker, afterMarker, markerResult, valueResult⟩
  · cases rest

/-- A Yul `let` declaration preserves names, initializer, and outer range. -/
theorem yulLetStatement_validFor :
    yulLetStatement.ValidFor YulStmt.ValidFor := by
  have weak : yulLetStatement.ValidFor (fun _ _ => True) := by
    unfold yulLetStatement
    apply Parser.bind_validFor (keyword_validFor .letKw .yulStatement)
    intro marker
    apply Parser.bind_validFor yulNames_validFor
    intro names
    apply Parser.bind_validFor yulLetInitializer_validFor
    intro initializer
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : yulLetStatement input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok statement final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold yulLetStatement at stages
      rcases yulStatementBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases yulStatementBind_ok_components rest with
        ⟨names, afterNames, namesResult, rest⟩
      rcases yulStatementBind_ok_components rest with
        ⟨initializer, afterInitializer, initializerResult, finished⟩
      have markerValid := keyword_validFor .letKw .yulStatement input inputValid
      rw [markerResult] at markerValid
      have namesValid := yulNames_validFor afterMarker markerValid.2.1
      rw [namesResult] at namesValid
      have initializerValid := yulLetInitializer_validFor afterNames
        namesValid.2.1
      rw [initializerResult] at initializerValid
      have markerSpanValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerValid.1
      have namesValidInput : YulNameSequence.ValidFor input.file names := by
        simpa [markerValid.2.2] using namesValid.1
      have markerShape := acceptToken_ok_state_shape (.keyword .letKw)
        .yulStatement (· == .keyword .letKw) markerResult
      have markerAdvanced : input.advance? = some (marker, afterMarker) := by
        unfold State.advance?
        rw [markerShape.1, markerShape.2]
        rfl
      rcases yulNames_startsAtCurrentTokenOnSuccess afterMarker names
          afterNames namesResult with ⟨firstName, firstFound, namesStart⟩
      cases initializer with
      | none =>
          have markerBeforeNames :=
            inputValid.consumed_end_le_peek_start_after_advance
              markerAdvanced firstFound
          have ordered : marker.span.startByte ≤ names.span.endByte :=
            Nat.le_trans markerSpanValid.2.1
              (Nat.le_trans markerBeforeNames (by
                rw [namesStart]
                exact namesValidInput.1.2.1))
          cases finished
          exact ⟨YulStmt.ValidFor.letDecl
              (SourceSpan.cover_validFor markerSpanValid namesValidInput.1
                ordered)
              namesValidInput.2 trivial,
            weakResult.2.1, weakResult.2.2⟩
      | some expression =>
          rcases yulLetInitializer_some_components initializerResult with
            ⟨assignMarker, afterAssignMarker, assignResult,
              expressionResult⟩
          rcases yulExpression_startsAtCurrentTokenOnSuccess
              afterAssignMarker expression afterInitializer expressionResult with
            ⟨expressionToken, expressionFound, expressionStart⟩
          have markerAt :=
            State.getElem?_eq_some_of_peek?_eq_some markerShape.1
          have expressionAt : input.tokens[afterAssignMarker.cursor]? =
              some expressionToken := by
            have foundAt :=
              State.getElem?_eq_some_of_peek?_eq_some expressionFound
            have keywordTokens := keyword_preservesTokensOnSuccess .letKw
              .yulStatement input marker afterMarker markerResult
            have namesTokens := yulNames_preservesTokensOnSuccess afterMarker
              names afterNames namesResult
            have assignTokens := symbol_preservesTokensOnSuccess .colonEqual
              .yulStatement afterNames assignMarker afterAssignMarker assignResult
            simpa [assignTokens, namesTokens, keywordTokens] using foundAt
          have markerBeforeExpression :
              marker.span.endByte ≤ expressionToken.span.startByte := by
            apply inputValid.token_end_le_token_start_of_getElem?_lt markerAt
              expressionAt
            have namesProgress :=
              (yulNames_ok_state_shape namesResult).choose_spec.2.2.2
            have assignShape := symbol_ok_state_shape .colonEqual .yulStatement
              assignResult
            exact Nat.lt_trans (by simp [markerShape.2])
              (Nat.lt_trans namesProgress (by simp [assignShape.2]))
          have expressionValidInput :
              YulExpr.ValidFor input.file expression := by
            have validAfterNames :
                YulExpr.ValidFor afterNames.file expression := by
              simpa only [Option.ValidFor] using initializerValid.1
            simpa [namesValid.2.2, markerValid.2.2] using validAfterNames
          have expressionSpanValid := yulExpr_span_valid expressionValidInput
          have ordered : marker.span.startByte ≤ expression.span.endByte :=
            Nat.le_trans markerSpanValid.2.1
              (Nat.le_trans markerBeforeExpression (by
                rw [expressionStart]
                exact expressionSpanValid.2.1))
          cases finished
          exact ⟨YulStmt.ValidFor.letDecl
              (SourceSpan.cover_validFor markerSpanValid expressionSpanValid
                ordered)
              namesValidInput.2 expressionValidInput,
            weakResult.2.1, weakResult.2.2⟩

/-- Yul `let` parsing preserves every ordinary token window. -/
theorem yulLetStatement_preservesTokenWindow :
    Parser.PreservesTokenWindow yulLetStatement := by
  unfold yulLetStatement
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .letKw .yulStatement)
  intro marker
  apply Parser.bind_preservesTokenWindow yulNames_preservesTokenWindow
  intro names
  apply Parser.bind_preservesTokenWindow yulLetInitializer_preservesTokenWindow
  intro initializer
  exact Parser.pure_preservesTokenWindow _

theorem yulLetStatement_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess yulLetStatement :=
  yulLetStatement_preservesTokenWindow.preservesTokensOnSuccess

/-- Yul `let` parsing never rewinds the cursor. -/
theorem yulLetStatement_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulLetStatement := by
  unfold yulLetStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .letKw .yulStatement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess yulNames_cursorMonotoneOnSuccess
  intro names
  apply Parser.bind_cursorMonotoneOnSuccess
    yulLetInitializer_cursorMonotoneOnSuccess
  intro initializer
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A successful Yul `let` declaration starts at its `let` token. -/
theorem yulLetStatement_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess yulLetStatement (·.span) := by
  unfold yulLetStatement
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess (.keyword .letKw)
      .yulStatement (· == .keyword .letKw))
  intro marker input statement final parsed
  rcases yulStatementBind_ok_components parsed with
    ⟨names, afterNames, _namesResult, rest⟩
  rcases yulStatementBind_ok_components rest with
    ⟨initializer, afterInitializer, _initializerResult, finished⟩
  cases finished
  rfl

/-- A Yul assignment preserves its names, value, and covering range. -/
theorem yulAssignment_validFor :
    yulAssignment.ValidFor YulStmt.ValidFor := by
  have weak : yulAssignment.ValidFor (fun _ _ => True) := by
    unfold yulAssignment
    apply Parser.bind_validFor yulNames_validFor
    intro names
    apply Parser.bind_validFor (symbol_validFor .colonEqual .yulStatement)
    intro marker
    apply Parser.bind_validFor yulExpression_validFor
    intro value
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : yulAssignment input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok statement final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold yulAssignment at stages
      rcases yulStatementBind_ok_components stages with
        ⟨names, afterNames, namesResult, rest⟩
      rcases yulStatementBind_ok_components rest with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases yulStatementBind_ok_components rest with
        ⟨value, afterValue, valueResult, finished⟩
      have namesValid := yulNames_validFor input inputValid
      rw [namesResult] at namesValid
      have markerValid := symbol_validFor .colonEqual .yulStatement
        afterNames namesValid.2.1
      rw [markerResult] at markerValid
      have valueValid := yulExpression_validFor afterMarker markerValid.2.1
      rw [valueResult] at valueValid
      have namesSpanValid : names.span.ValidFor input.file := namesValid.1.1
      have valueValidInput : YulExpr.ValidFor input.file value := by
        simpa [markerValid.2.2, namesValid.2.2] using valueValid.1
      have valueSpanValid : value.span.ValidFor input.file :=
        yulExpr_span_valid valueValidInput
      rcases yulNames_startsAtCurrentTokenOnSuccess input names afterNames
          namesResult with ⟨firstToken, firstFound, namesStart⟩
      rcases yulExpression_startsAtCurrentTokenOnSuccess afterMarker value
          afterValue valueResult with ⟨valueToken, valueFound, valueStart⟩
      have firstAt := State.getElem?_eq_some_of_peek?_eq_some firstFound
      have valueAt : input.tokens[afterMarker.cursor]? = some valueToken := by
        have foundAt := State.getElem?_eq_some_of_peek?_eq_some valueFound
        have namesTokens := yulNames_preservesTokensOnSuccess input names
          afterNames namesResult
        have markerTokens := symbol_preservesTokensOnSuccess .colonEqual
          .yulStatement afterNames marker afterMarker markerResult
        simpa [markerTokens, namesTokens] using foundAt
      have tokenOrder : firstToken.span.endByte ≤ valueToken.span.startByte := by
        apply inputValid.token_end_le_token_start_of_getElem?_lt firstAt valueAt
        have namesProgress :=
          (yulNames_ok_state_shape namesResult).choose_spec.2.2.2
        have markerShape := symbol_ok_state_shape .colonEqual .yulStatement
          markerResult
        exact Nat.lt_trans namesProgress (by simp [markerShape.2])
      have outerOrdered : names.span.startByte ≤ value.span.endByte := by
        have firstValid := inputValid.peek?_span_validFor firstFound
        exact Nat.le_trans (by simpa [namesStart] using firstValid.2.1)
          (Nat.le_trans tokenOrder
            (by simpa [valueStart] using valueSpanValid.2.1))
      have outerValid := SourceSpan.cover_validFor namesSpanValid
        valueSpanValid outerOrdered
      cases finished
      exact ⟨YulStmt.ValidFor.assign outerValid namesValid.1.2
          valueValidInput,
        weakResult.2.1, weakResult.2.2⟩

/-- A Yul assignment preserves the immutable token carrier. -/
theorem yulAssignment_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess yulAssignment := by
  unfold yulAssignment
  apply Parser.bind_preservesTokensOnSuccess
    yulNames_preservesTokensOnSuccess
  intro names
  apply Parser.bind_preservesTokensOnSuccess
    (symbol_preservesTokensOnSuccess .colonEqual .yulStatement)
  intro marker
  apply Parser.bind_preservesTokensOnSuccess
    yulExpression_preservesTokensOnSuccess
  intro value
  exact Parser.pure_preservesTokensOnSuccess _

/-- Yul assignments preserve every ordinary token window. -/
theorem yulAssignment_preservesTokenWindow :
    Parser.PreservesTokenWindow yulAssignment := by
  unfold yulAssignment
  apply Parser.bind_preservesTokenWindow yulNames_preservesTokenWindow
  intro names
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .colonEqual .yulStatement)
  intro marker
  apply Parser.bind_preservesTokenWindow yulExpression_preservesTokenWindow
  intro value
  exact Parser.pure_preservesTokenWindow _

/-- A Yul assignment never rewinds the parser cursor. -/
theorem yulAssignment_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulAssignment := by
  unfold yulAssignment
  apply Parser.bind_cursorMonotoneOnSuccess yulNames_cursorMonotoneOnSuccess
  intro names
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .colonEqual .yulStatement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    yulExpression_cursorMonotoneOnSuccess
  intro value
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A successful Yul assignment starts at its first target name. -/
theorem yulAssignment_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess yulAssignment (·.span) := by
  unfold yulAssignment
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    yulNames_startsAtCurrentTokenOnSuccess
  intro names input statement final parsed
  rcases yulStatementBind_ok_components parsed with
    ⟨marker, afterMarker, _markerResult, rest⟩
  rcases yulStatementBind_ok_components rest with
    ⟨value, afterValue, _valueResult, finished⟩
  cases finished
  rfl

/-- An expression in statement position retains recursive provenance. -/
theorem yulExpressionStatement_validFor :
    yulExpressionStatement.ValidFor YulStmt.ValidFor := by
  unfold yulExpressionStatement
  apply Parser.bind_validFor_of_value yulExpression_validFor
  intro expression input inputValid expressionValid
  exact ⟨YulStmt.ValidFor.expression (yulExpr_span_valid expressionValid)
      expressionValid,
    inputValid, rfl⟩

/-- Expression statements preserve every ordinary token window. -/
theorem yulExpressionStatement_preservesTokenWindow :
    Parser.PreservesTokenWindow yulExpressionStatement := by
  unfold yulExpressionStatement
  apply Parser.bind_preservesTokenWindow yulExpression_preservesTokenWindow
  intro expression
  exact Parser.pure_preservesTokenWindow _

theorem yulExpressionStatement_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess yulExpressionStatement :=
  yulExpressionStatement_preservesTokenWindow.preservesTokensOnSuccess

/-- Expression statements never rewind the parser cursor. -/
theorem yulExpressionStatement_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulExpressionStatement := by
  unfold yulExpressionStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    yulExpression_cursorMonotoneOnSuccess
  intro expression
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A successful expression statement starts at its expression token. -/
theorem yulExpressionStatement_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess yulExpressionStatement (·.span) := by
  unfold yulExpressionStatement
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    yulExpression_startsAtCurrentTokenOnSuccess
  intros
  cases ‹_ = Reply.ok _ _›
  rfl

/-- Yul `return(...)` preserves its synthesized call and argument ranges. -/
theorem yulReturnBuiltin_validFor :
    yulReturnBuiltin.ValidFor YulStmt.ValidFor := by
  have argumentsContract := delimited_validFor YulExpr.ValidFor .leftParen
    .rightParen true yulExpression .yulExpression .yul
    yulExpression_validFor yulExpression_preservesTokensOnSuccess
  have weak : yulReturnBuiltin.ValidFor (fun _ _ => True) := by
    unfold yulReturnBuiltin
    apply Parser.bind_validFor (keyword_validFor .returnKw .yulStatement)
    intro marker
    apply Parser.bind_validFor argumentsContract
    intro arguments
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : yulReturnBuiltin input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok statement final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold yulReturnBuiltin at stages
      rcases yulStatementBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases yulStatementBind_ok_components rest with
        ⟨arguments, afterArguments, argumentsResult, finished⟩
      have markerValid := keyword_validFor .returnKw .yulStatement input
        inputValid
      rw [markerResult] at markerValid
      have argumentsValid := argumentsContract afterMarker markerValid.2.1
      rw [argumentsResult] at argumentsValid
      have markerSpanValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerValid.1
      have argumentsValidInput :
          DelimitedList.ValidFor YulExpr.ValidFor input.file arguments := by
        simpa [markerValid.2.2] using argumentsValid.1
      have markerShape := acceptToken_ok_state_shape (.keyword .returnKw)
        .yulStatement (· == .keyword .returnKw) markerResult
      have markerAdvanced : input.advance? = some (marker, afterMarker) := by
        unfold State.advance?
        rw [markerShape.1, markerShape.2]
        rfl
      rcases delimited_startsAtCurrentTokenOnSuccess .leftParen .rightParen
          true yulExpression .yulExpression .yul afterMarker arguments
          afterArguments argumentsResult with
        ⟨opening, openingFound, argumentsStart⟩
      have markerBeforeArguments :=
        inputValid.consumed_end_le_peek_start_after_advance markerAdvanced
          openingFound
      have ordered : marker.span.startByte ≤ arguments.span.endByte :=
        Nat.le_trans markerSpanValid.2.1
          (Nat.le_trans markerBeforeArguments (by
            rw [argumentsStart]
            exact argumentsValidInput.1.2.1))
      have outerValid := SourceSpan.cover_validFor markerSpanValid
        argumentsValidInput.1 ordered
      have expressionValid : YulExpr.ValidFor input.file {
          span := SourceSpan.cover marker.span arguments.span
          value := .call { span := marker.span, value := "return" } arguments
        } := YulExpr.ValidFor.call outerValid markerSpanValid
          argumentsValidInput.1 argumentsValidInput.2
      cases finished
      exact ⟨YulStmt.ValidFor.expression outerValid expressionValid,
        weakResult.2.1, weakResult.2.2⟩

/-- Yul `return(...)` preserves every ordinary token window. -/
theorem yulReturnBuiltin_preservesTokenWindow :
    Parser.PreservesTokenWindow yulReturnBuiltin := by
  unfold yulReturnBuiltin
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .returnKw .yulStatement)
  intro marker
  apply Parser.bind_preservesTokenWindow
    (delimited_preservesTokenWindow .leftParen .rightParen true yulExpression
      .yulExpression .yul yulExpression_preservesTokenWindow)
  intro arguments
  exact Parser.pure_preservesTokenWindow _

theorem yulReturnBuiltin_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess yulReturnBuiltin :=
  yulReturnBuiltin_preservesTokenWindow.preservesTokensOnSuccess

/-- Yul `return(...)` never rewinds the parser cursor. -/
theorem yulReturnBuiltin_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulReturnBuiltin := by
  unfold yulReturnBuiltin
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .returnKw .yulStatement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (delimited_cursorMonotoneOnSuccess .leftParen .rightParen true
      yulExpression .yulExpression .yul)
  intro arguments
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A successful Yul `return(...)` starts at its `return` token. -/
theorem yulReturnBuiltin_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess yulReturnBuiltin (·.span) := by
  unfold yulReturnBuiltin
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess (.keyword .returnKw)
      .yulStatement (· == .keyword .returnKw))
  intro marker input statement final parsed
  rcases yulStatementBind_ok_components parsed with
    ⟨arguments, afterArguments, _argumentsResult, finished⟩
  cases finished
  rfl

/-- A keyword-only Yul control statement retains its keyword range. -/
theorem yulControlToken_validFor (value : HardKeyword)
    (result : YulStmtValue)
    (resultValid : ∀ file span, span.ValidFor file →
      YulStmt.ValidFor file { span, value := result }) :
    (yulControlToken value result).ValidFor YulStmt.ValidFor := by
  unfold yulControlToken
  apply Parser.bind_validFor_of_value (keyword_validFor value .yulStatement)
  intro marker input inputValid markerValid
  exact ⟨resultValid input.file marker.span markerValid, inputValid, rfl⟩

theorem yulLeaveControl_validFor :
    (yulControlToken .leaveKw .leave).ValidFor YulStmt.ValidFor :=
  yulControlToken_validFor .leaveKw .leave
    (fun _ _ => YulStmt.ValidFor.leave)

theorem yulBreakControl_validFor :
    (yulControlToken .breakKw .break).ValidFor YulStmt.ValidFor :=
  yulControlToken_validFor .breakKw .break
    (fun _ _ => YulStmt.ValidFor.break)

theorem yulContinueControl_validFor :
    (yulControlToken .continueKw .continue).ValidFor YulStmt.ValidFor :=
  yulControlToken_validFor .continueKw .continue
    (fun _ _ => YulStmt.ValidFor.continue)

/-- Keyword-only Yul control statements preserve complete token windows. -/
theorem yulControlToken_preservesTokenWindow (value : HardKeyword)
    (result : YulStmtValue) :
    Parser.PreservesTokenWindow (yulControlToken value result) := by
  unfold yulControlToken
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow value .yulStatement)
  intro marker
  exact Parser.pure_preservesTokenWindow _

theorem yulControlToken_preservesTokensOnSuccess (value : HardKeyword)
    (result : YulStmtValue) :
    Parser.PreservesTokensOnSuccess (yulControlToken value result) :=
  (yulControlToken_preservesTokenWindow value result).preservesTokensOnSuccess

/-- Keyword-only Yul control statements never rewind the cursor. -/
theorem yulControlToken_cursorMonotoneOnSuccess (value : HardKeyword)
    (result : YulStmtValue) :
    Parser.CursorMonotoneOnSuccess (yulControlToken value result) := by
  unfold yulControlToken
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess value .yulStatement)
  intro marker
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A keyword-only Yul control statement starts at its keyword token. -/
theorem yulControlToken_startsAtCurrentTokenOnSuccess (value : HardKeyword)
    (result : YulStmtValue) :
    Parser.StartsAtCurrentTokenOnSuccess
      (yulControlToken value result) (·.span) := by
  unfold yulControlToken
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess (.keyword value)
      .yulStatement (· == .keyword value))
  intros
  cases ‹_ = Reply.ok _ _›
  rfl

/-- Recognized-statement fallback preserves either branch's provenance. -/
theorem recognizedYulStatementOrFallback_validFor {valueValid :
    SourceFile → YulStmt → Prop} (primary fallback : Parser YulStmt)
    (primaryValid : primary.ValidFor valueValid)
    (fallbackValid : fallback.ValidFor valueValid) :
    (recognizedYulStatementOrFallback primary fallback).ValidFor valueValid := by
  intro input inputValid
  have primaryContract := primaryValid input inputValid
  unfold recognizedYulStatementOrFallback
  cases primaryResult : primary input with
  | invariant error => trivial
  | ok value next =>
      rw [primaryResult] at primaryContract
      simpa only [primaryResult] using primaryContract
  | reject failure failedState =>
      rw [primaryResult] at primaryContract
      have fallbackContract := fallbackValid input inputValid
      cases fallbackResult : fallback input with
      | invariant error => trivial
      | reject fallbackFailure fallbackState =>
          simp only [Reply.ValidFor]
          exact ⟨primaryContract.1, inputValid, trivial⟩
      | ok value next =>
          rw [fallbackResult] at fallbackContract
          let reset : State := {
            next with diagnosticsRev := input.diagnosticsRev
          }
          have resetValid : reset.ValidFor := {
            tokens := fallbackContract.2.1.tokens
            cursor_le_endIndex := fallbackContract.2.1.cursor_le_endIndex
            endIndex_le_size := fallbackContract.2.1.endIndex_le_size
            endByte_le_source := fallbackContract.2.1.endByte_le_source
            endByte_boundary := fallbackContract.2.1.endByte_boundary
            diagnosticsRev := by
              intro diagnostic member
              simpa [reset, fallbackContract.2.2] using
                inputValid.diagnosticsRev diagnostic member
          }
          have emittedValid := resetValid.emit_validFor failure.toDiagnostic
            (by simpa [reset, fallbackContract.2.2] using
              failure.toDiagnostic_span_validFor primaryContract.1)
          simp only [Reply.ValidFor]
          exact ⟨fallbackContract.1, emittedValid,
            by simpa [reset, State.emit] using fallbackContract.2.2⟩

/-- Recognized-statement fallback preserves every ordinary token window. -/
theorem recognizedYulStatementOrFallback_preservesTokenWindow
    (primary fallback : Parser YulStmt)
    (primaryShape : Parser.PreservesTokenWindow primary)
    (fallbackShape : Parser.PreservesTokenWindow fallback) :
    Parser.PreservesTokenWindow
      (recognizedYulStatementOrFallback primary fallback) := by
  intro input
  have primaryContract := primaryShape input
  unfold recognizedYulStatementOrFallback
  cases primaryResult : primary input with
  | invariant error => trivial
  | ok value next =>
      rw [primaryResult] at primaryContract
      simpa only [primaryResult] using primaryContract
  | reject failure failedState =>
      have fallbackContract := fallbackShape input
      cases fallbackResult : fallback input with
      | invariant error => trivial
      | reject fallbackFailure fallbackState =>
          simp only [Reply.PreservesTokenWindow]
          exact ⟨trivial, trivial⟩
      | ok value next =>
          rw [fallbackResult] at fallbackContract
          simpa only [primaryResult, fallbackResult, State.emit,
            Reply.PreservesTokenWindow] using fallbackContract

theorem recognizedYulStatementOrFallback_preservesTokensOnSuccess
    (primary fallback : Parser YulStmt)
    (primaryShape : Parser.PreservesTokenWindow primary)
    (fallbackShape : Parser.PreservesTokenWindow fallback) :
    Parser.PreservesTokensOnSuccess
      (recognizedYulStatementOrFallback primary fallback) :=
  (recognizedYulStatementOrFallback_preservesTokenWindow primary fallback
    primaryShape fallbackShape).preservesTokensOnSuccess

/-- Success-only carrier contracts also compose through recognized fallback. -/
theorem recognizedYulStatementOrFallback_preservesTokensOnSuccess_of_success
    (primary fallback : Parser YulStmt)
    (primaryPreserves : Parser.PreservesTokensOnSuccess primary)
    (fallbackPreserves : Parser.PreservesTokensOnSuccess fallback) :
    Parser.PreservesTokensOnSuccess
      (recognizedYulStatementOrFallback primary fallback) := by
  intro input value next result
  unfold recognizedYulStatementOrFallback at result
  cases primaryResult : primary input with
  | invariant error => simp [primaryResult] at result
  | ok primaryValue afterPrimary =>
      simp only [primaryResult] at result
      have preserved := primaryPreserves input primaryValue afterPrimary
        primaryResult
      cases result
      exact preserved
  | reject failure failedState =>
      simp only [primaryResult] at result
      cases fallbackResult : fallback input with
      | invariant error => simp [fallbackResult] at result
      | reject fallbackFailure fallbackState => simp [fallbackResult] at result
      | ok fallbackValue afterFallback =>
          simp only [fallbackResult] at result
          have preserved := fallbackPreserves input fallbackValue afterFallback
            fallbackResult
          cases result
          exact preserved

/-- Recognized-statement fallback never rewinds either successful branch. -/
theorem recognizedYulStatementOrFallback_cursorMonotoneOnSuccess
    (primary fallback : Parser YulStmt)
    (primaryMonotone : Parser.CursorMonotoneOnSuccess primary)
    (fallbackMonotone : Parser.CursorMonotoneOnSuccess fallback) :
    Parser.CursorMonotoneOnSuccess
      (recognizedYulStatementOrFallback primary fallback) := by
  intro input value next result
  unfold recognizedYulStatementOrFallback at result
  cases primaryResult : primary input with
  | invariant error => simp [primaryResult] at result
  | ok primaryValue afterPrimary =>
      simp only [primaryResult] at result
      have monotone := primaryMonotone input primaryValue afterPrimary
        primaryResult
      cases result
      exact monotone
  | reject failure failedState =>
      simp only [primaryResult] at result
      cases fallbackResult : fallback input with
      | invariant error => simp [fallbackResult] at result
      | reject fallbackFailure fallbackState => simp [fallbackResult] at result
      | ok fallbackValue afterFallback =>
          simp only [fallbackResult] at result
          have monotone := fallbackMonotone input fallbackValue afterFallback
            fallbackResult
          cases result
          exact monotone

/-- Successful recognized fallback starts at the selected branch's token. -/
theorem recognizedYulStatementOrFallback_startsAtCurrentTokenOnSuccess
    (primary fallback : Parser YulStmt)
    (primaryStarts : Parser.StartsAtCurrentTokenOnSuccess primary (·.span))
    (fallbackStarts : Parser.StartsAtCurrentTokenOnSuccess fallback (·.span)) :
    Parser.StartsAtCurrentTokenOnSuccess
      (recognizedYulStatementOrFallback primary fallback) (·.span) := by
  intro input value next result
  unfold recognizedYulStatementOrFallback at result
  cases primaryResult : primary input with
  | invariant error => simp [primaryResult] at result
  | ok primaryValue afterPrimary =>
      simp only [primaryResult] at result
      have starts := primaryStarts input primaryValue afterPrimary primaryResult
      cases result
      exact starts
  | reject failure failedState =>
      simp only [primaryResult] at result
      cases fallbackResult : fallback input with
      | invariant error => simp [fallbackResult] at result
      | reject fallbackFailure fallbackState => simp [fallbackResult] at result
      | ok fallbackValue afterFallback =>
          simp only [fallbackResult] at result
          have starts := fallbackStarts input fallbackValue afterFallback
            fallbackResult
          cases result
          exact starts

/-- Contracts needed to compose one recursive Yul statement choice. -/
structure YulStatementParserContracts (parser : Parser YulStmt) : Prop where
  validFor : parser.ValidFor YulStmt.ValidFor
  preservesTokens : Parser.PreservesTokensOnSuccess parser
  cursorMonotone : Parser.CursorMonotoneOnSuccess parser
  startsAtToken : Parser.StartsAtCurrentTokenOnSuccess parser (·.span)

private theorem stateChoice_contracts (condition : State → Bool)
    (first second : Parser YulStmt)
    (firstContracts : YulStatementParserContracts first)
    (secondContracts : YulStatementParserContracts second) :
    YulStatementParserContracts (fun input =>
      if condition input then first input else second input) := {
  validFor := by
    intro input inputValid
    by_cases selected : condition input = true
    · simpa [selected] using firstContracts.validFor input inputValid
    · simpa [selected] using secondContracts.validFor input inputValid
  preservesTokens := by
    intro input value next result
    by_cases selected : condition input = true
    · exact firstContracts.preservesTokens input value next
        (by simpa [selected] using result)
    · exact secondContracts.preservesTokens input value next
        (by simpa [selected] using result)
  cursorMonotone := by
    intro input value next result
    by_cases selected : condition input = true
    · exact firstContracts.cursorMonotone input value next
        (by simpa [selected] using result)
    · exact secondContracts.cursorMonotone input value next
        (by simpa [selected] using result)
  startsAtToken := by
    intro input value next result
    by_cases selected : condition input = true
    · exact firstContracts.startsAtToken input value next
        (by simpa [selected] using result)
    · exact secondContracts.startsAtToken input value next
        (by simpa [selected] using result)
}

private theorem recognized_contracts (primary fallback : Parser YulStmt)
    (primaryContracts : YulStatementParserContracts primary)
    (fallbackContracts : YulStatementParserContracts fallback) :
    YulStatementParserContracts
      (recognizedYulStatementOrFallback primary fallback) := {
  validFor := recognizedYulStatementOrFallback_validFor primary fallback
    primaryContracts.validFor fallbackContracts.validFor
  preservesTokens :=
    recognizedYulStatementOrFallback_preservesTokensOnSuccess_of_success
      primary fallback primaryContracts.preservesTokens
        fallbackContracts.preservesTokens
  cursorMonotone :=
    recognizedYulStatementOrFallback_cursorMonotoneOnSuccess primary fallback
      primaryContracts.cursorMonotone fallbackContracts.cursorMonotone
  startsAtToken :=
    recognizedYulStatementOrFallback_startsAtCurrentTokenOnSuccess
      primary fallback primaryContracts.startsAtToken
        fallbackContracts.startsAtToken
}

private theorem orElse_contracts (first second : Parser YulStmt)
    (firstContracts : YulStatementParserContracts first)
    (secondContracts : YulStatementParserContracts second) :
    YulStatementParserContracts (orElse first second) := {
  validFor := Parser.orElse_validFor firstContracts.validFor
    secondContracts.validFor
  preservesTokens := Parser.orElse_preservesTokensOnSuccess
    firstContracts.preservesTokens secondContracts.preservesTokens
  cursorMonotone := Parser.orElse_cursorMonotoneOnSuccess
    firstContracts.cursorMonotone secondContracts.cursorMonotone
  startsAtToken := Parser.orElse_startsAtCurrentTokenOnSuccess
    firstContracts.startsAtToken secondContracts.startsAtToken
}

/-- All non-terminating Yul statement choices compose from recursive input. -/
theorem yulStatementCore_contracts (nested : Parser YulStmt)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    YulStatementParserContracts (yulStatementCore nested) := by
  let fallbackContracts :
      YulStatementParserContracts yulExpressionStatement :=
    ⟨yulExpressionStatement_validFor,
      yulExpressionStatement_preservesTokensOnSuccess,
      yulExpressionStatement_cursorMonotoneOnSuccess,
      yulExpressionStatement_startsAtCurrentTokenOnSuccess⟩
  have blockContracts :
      YulStatementParserContracts (yulBlockStatement nested) :=
    ⟨yulBlockStatement_validFor nested nestedValid nestedPreserves,
      yulBlockStatement_preservesTokensOnSuccess nested nestedPreserves,
      yulBlockStatement_cursorMonotoneOnSuccess nested nestedPreserves,
      yulBlockStatement_startsAtCurrentTokenOnSuccess nested nestedPreserves⟩
  have letContracts : YulStatementParserContracts yulLetStatement :=
    ⟨yulLetStatement_validFor, yulLetStatement_preservesTokensOnSuccess,
      yulLetStatement_cursorMonotoneOnSuccess,
      yulLetStatement_startsAtCurrentTokenOnSuccess⟩
  have ifContracts :
      YulStatementParserContracts (yulIfStatement nested) :=
    ⟨yulIfStatement_validFor nested yulExpression_validFor
        yulExpression_startsAtCurrentTokenOnSuccess
        yulExpression_preservesTokensOnSuccess
        yulExpression_cursorMonotoneOnSuccess nestedValid nestedPreserves,
      yulIfStatement_preservesTokensOnSuccess nested
        yulExpression_preservesTokensOnSuccess nestedPreserves,
      yulIfStatement_cursorMonotoneOnSuccess nested
        yulExpression_cursorMonotoneOnSuccess nestedPreserves,
      yulIfStatement_startsAtCurrentTokenOnSuccess nested⟩
  have forContracts :
      YulStatementParserContracts (yulForStatement nested) :=
    ⟨yulForStatement_validFor nested yulExpression_validFor
        yulExpression_preservesTokensOnSuccess
        yulExpression_cursorMonotoneOnSuccess nestedValid nestedPreserves,
      yulForStatement_preservesTokensOnSuccess nested
        yulExpression_preservesTokensOnSuccess nestedPreserves,
      yulForStatement_cursorMonotoneOnSuccess nested
        yulExpression_cursorMonotoneOnSuccess nestedPreserves,
      yulForStatement_startsAtCurrentTokenOnSuccess nested⟩
  have switchContracts :
      YulStatementParserContracts (yulSwitchStatement nested) :=
    ⟨yulSwitchStatement_validFor nested nestedValid nestedPreserves,
      yulSwitchStatement_preservesTokensOnSuccess nested nestedPreserves,
      yulSwitchStatement_cursorMonotoneOnSuccess nested nestedPreserves,
      yulSwitchStatement_startsAtCurrentTokenOnSuccess nested⟩
  have functionContracts :
      YulStatementParserContracts (yulFunctionStatement nested) :=
    ⟨yulFunctionStatement_validFor nested nestedValid nestedPreserves,
      yulFunctionStatement_preservesTokensOnSuccess nested nestedPreserves,
      yulFunctionStatement_cursorMonotoneOnSuccess nested nestedPreserves,
      yulFunctionStatement_startsAtCurrentTokenOnSuccess nested⟩
  have returnContracts : YulStatementParserContracts yulReturnBuiltin :=
    ⟨yulReturnBuiltin_validFor, yulReturnBuiltin_preservesTokensOnSuccess,
      yulReturnBuiltin_cursorMonotoneOnSuccess,
      yulReturnBuiltin_startsAtCurrentTokenOnSuccess⟩
  have leaveContracts : YulStatementParserContracts
      (yulControlToken .leaveKw .leave) :=
    ⟨yulLeaveControl_validFor,
      yulControlToken_preservesTokensOnSuccess .leaveKw .leave,
      yulControlToken_cursorMonotoneOnSuccess .leaveKw .leave,
      yulControlToken_startsAtCurrentTokenOnSuccess .leaveKw .leave⟩
  have breakContracts : YulStatementParserContracts
      (yulControlToken .breakKw .break) :=
    ⟨yulBreakControl_validFor,
      yulControlToken_preservesTokensOnSuccess .breakKw .break,
      yulControlToken_cursorMonotoneOnSuccess .breakKw .break,
      yulControlToken_startsAtCurrentTokenOnSuccess .breakKw .break⟩
  have continueContracts : YulStatementParserContracts
      (yulControlToken .continueKw .continue) :=
    ⟨yulContinueControl_validFor,
      yulControlToken_preservesTokensOnSuccess .continueKw .continue,
      yulControlToken_cursorMonotoneOnSuccess .continueKw .continue,
      yulControlToken_startsAtCurrentTokenOnSuccess .continueKw .continue⟩
  have assignmentContracts : YulStatementParserContracts yulAssignment :=
    ⟨yulAssignment_validFor, yulAssignment_preservesTokensOnSuccess,
      yulAssignment_cursorMonotoneOnSuccess,
      yulAssignment_startsAtCurrentTokenOnSuccess⟩
  unfold yulStatementCore
  apply stateChoice_contracts
  · exact recognized_contracts _ _ blockContracts fallbackContracts
  · apply stateChoice_contracts
    · exact recognized_contracts _ _ letContracts fallbackContracts
    · apply stateChoice_contracts
      · exact recognized_contracts _ _ ifContracts fallbackContracts
      · apply stateChoice_contracts
        · exact recognized_contracts _ _ forContracts fallbackContracts
        · apply stateChoice_contracts
          · exact recognized_contracts _ _ switchContracts fallbackContracts
          · apply stateChoice_contracts
            · exact recognized_contracts _ _ functionContracts fallbackContracts
            · apply stateChoice_contracts
              · exact recognized_contracts _ _ returnContracts fallbackContracts
              · apply stateChoice_contracts
                · exact recognized_contracts _ _ leaveContracts fallbackContracts
                · apply stateChoice_contracts
                  · exact recognized_contracts _ _ breakContracts fallbackContracts
                  · apply stateChoice_contracts
                    · exact recognized_contracts _ _ continueContracts
                        fallbackContracts
                    · apply stateChoice_contracts
                      · exact orElse_contracts _ _ assignmentContracts
                          fallbackContracts
                      · exact fallbackContracts

theorem yulStatementCore_validFor (nested : Parser YulStmt)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (yulStatementCore nested).ValidFor YulStmt.ValidFor :=
  (yulStatementCore_contracts nested nestedValid nestedPreserves).validFor

theorem yulStatementCore_preservesTokensOnSuccess (nested : Parser YulStmt)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (yulStatementCore nested) :=
  (yulStatementCore_contracts nested nestedValid nestedPreserves).preservesTokens

theorem yulStatementCore_cursorMonotoneOnSuccess (nested : Parser YulStmt)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.CursorMonotoneOnSuccess (yulStatementCore nested) :=
  (yulStatementCore_contracts nested nestedValid nestedPreserves).cursorMonotone

theorem yulStatementCore_startsAtCurrentTokenOnSuccess
    (nested : Parser YulStmt)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.StartsAtCurrentTokenOnSuccess (yulStatementCore nested) (·.span) :=
  (yulStatementCore_contracts nested nestedValid nestedPreserves).startsAtToken

/-- Every non-terminating statement choice preserves recursive token windows. -/
theorem yulStatementCore_preservesTokenWindow (nested : Parser YulStmt)
    (nestedShape : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (yulStatementCore nested) := by
  intro input
  unfold yulStatementCore
  split
  · exact recognizedYulStatementOrFallback_preservesTokenWindow _ _
      (yulBlockStatement_preservesTokenWindow nested nestedShape)
      yulExpressionStatement_preservesTokenWindow input
  · split
    · exact recognizedYulStatementOrFallback_preservesTokenWindow _ _
        yulLetStatement_preservesTokenWindow
        yulExpressionStatement_preservesTokenWindow input
    · split
      · exact recognizedYulStatementOrFallback_preservesTokenWindow _ _
          (yulIfStatement_preservesTokenWindow nested
            yulExpression_preservesTokenWindow nestedShape)
          yulExpressionStatement_preservesTokenWindow input
      · split
        · exact recognizedYulStatementOrFallback_preservesTokenWindow _ _
            (yulForStatement_preservesTokenWindow nested
              yulExpression_preservesTokenWindow nestedShape)
            yulExpressionStatement_preservesTokenWindow input
        · split
          · exact recognizedYulStatementOrFallback_preservesTokenWindow _ _
              (yulSwitchStatement_preservesTokenWindow nested nestedShape)
              yulExpressionStatement_preservesTokenWindow input
          · split
            · exact recognizedYulStatementOrFallback_preservesTokenWindow _ _
                (yulFunctionStatement_preservesTokenWindow nested nestedShape)
                yulExpressionStatement_preservesTokenWindow input
            · split
              · exact recognizedYulStatementOrFallback_preservesTokenWindow _ _
                  yulReturnBuiltin_preservesTokenWindow
                  yulExpressionStatement_preservesTokenWindow input
              · split
                · exact recognizedYulStatementOrFallback_preservesTokenWindow _ _
                    (yulControlToken_preservesTokenWindow .leaveKw .leave)
                    yulExpressionStatement_preservesTokenWindow input
                · split
                  · exact recognizedYulStatementOrFallback_preservesTokenWindow
                      _ _ (yulControlToken_preservesTokenWindow .breakKw .break)
                      yulExpressionStatement_preservesTokenWindow input
                  · split
                    · exact recognizedYulStatementOrFallback_preservesTokenWindow
                        _ _ (yulControlToken_preservesTokenWindow
                          .continueKw .continue)
                        yulExpressionStatement_preservesTokenWindow input
                    · split
                      · exact Parser.orElse_preservesTokenWindow
                          yulAssignment_preservesTokenWindow
                          yulExpressionStatement_preservesTokenWindow input
                      · exact yulExpressionStatement_preservesTokenWindow input

/-- Optional semicolon parsing preserves a supplied valid statement. -/
theorem optionalYulSemicolon_validForAt (value : YulStmt) (input : State)
    (inputValid : input.ValidFor) (valueValid : YulStmt.ValidFor input.file value) :
    (optionalYulSemicolon value input).ValidFor input YulStmt.ValidFor := by
  unfold optionalYulSemicolon getState
  simp only [bind]
  by_cases present : isSymbol input .semicolon = true
  · simp only [present, if_true]
    cases semicolonResult : symbol .semicolon .yulStatement input with
    | invariant error => trivial
    | reject failure rejected =>
        have valid := symbol_validFor .semicolon .yulStatement input inputValid
        rw [semicolonResult] at valid
        simpa only [bind, semicolonResult, Reply.ValidFor] using valid
    | ok marker next =>
        have valid := symbol_validFor .semicolon .yulStatement input inputValid
        rw [semicolonResult] at valid
        simp only [Reply.ValidFor]
        exact ⟨by simpa [valid.2.2] using valueValid,
          valid.2.1, valid.2.2⟩
  · simp only [present, Bool.false_eq_true, if_false, Reply.ValidFor]
    exact ⟨valueValid, inputValid, rfl⟩

/-- Optional semicolons preserve every ordinary token window. -/
theorem optionalYulSemicolon_preservesTokenWindow (value : YulStmt) :
    Parser.PreservesTokenWindow (optionalYulSemicolon value) := by
  unfold optionalYulSemicolon
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindow
  intro state
  split
  · apply Parser.bind_preservesTokenWindow
      (symbol_preservesTokenWindow .semicolon .yulStatement)
    intro marker
    exact Parser.pure_preservesTokenWindow value
  · exact Parser.pure_preservesTokenWindow value

/-- Optional semicolons never rewind the parser cursor. -/
theorem optionalYulSemicolon_cursorMonotoneOnSuccess (value : YulStmt) :
    Parser.CursorMonotoneOnSuccess (optionalYulSemicolon value) := by
  unfold optionalYulSemicolon
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro state
  split
  · apply Parser.bind_cursorMonotoneOnSuccess
      (symbol_cursorMonotoneOnSuccess .semicolon .yulStatement)
    intro marker
    exact Parser.pure_cursorMonotoneOnSuccess value
  · exact Parser.pure_cursorMonotoneOnSuccess value

/-- Optional semicolon parsing returns the supplied statement unchanged. -/
theorem optionalYulSemicolon_value_eq (value parsed : YulStmt)
    (input next : State)
    (result : optionalYulSemicolon value input = .ok parsed next) :
    parsed = value := by
  unfold optionalYulSemicolon getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .semicolon = true
  · simp only [present, if_true] at result
    cases semicolonResult : symbol .semicolon .yulStatement input with
    | invariant error => simp [semicolonResult] at result
    | reject failure rejected => simp [semicolonResult] at result
    | ok marker afterMarker =>
        simp only [semicolonResult] at result
        cases result
        rfl
  · simp only [present, Bool.false_eq_true, if_false] at result
    cases result
    rfl

/-- Optional termination preserves recursive statement provenance. -/
theorem yulStatementTerminated_validFor (nested : Parser YulStmt)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (yulStatementTerminated nested).ValidFor YulStmt.ValidFor := by
  intro input inputValid
  unfold yulStatementTerminated
  cases coreResult : yulStatementCore nested input with
  | invariant error => simp [bind, coreResult, Reply.ValidFor]
  | reject failure rejected =>
      have valid := yulStatementCore_validFor nested nestedValid
        nestedPreserves input inputValid
      rw [coreResult] at valid
      simpa only [bind, coreResult] using valid
  | ok value afterCore =>
      have valid := yulStatementCore_validFor nested nestedValid
        nestedPreserves input inputValid
      rw [coreResult] at valid
      simpa only [bind, coreResult] using
        (optionalYulSemicolon_validForAt value afterCore valid.2.1
          (by simpa [valid.2.2] using valid.1)).of_file_eq valid.2.2

theorem yulStatementTerminated_preservesTokensOnSuccess
    (nested : Parser YulStmt)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (yulStatementTerminated nested) := by
  unfold yulStatementTerminated
  apply Parser.bind_preservesTokensOnSuccess
    (yulStatementCore_preservesTokensOnSuccess nested nestedValid
      nestedPreserves)
  intro value
  exact (optionalYulSemicolon_preservesTokenWindow value).preservesTokensOnSuccess

theorem yulStatementTerminated_cursorMonotoneOnSuccess
    (nested : Parser YulStmt)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.CursorMonotoneOnSuccess (yulStatementTerminated nested) := by
  unfold yulStatementTerminated
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulStatementCore_cursorMonotoneOnSuccess nested nestedValid
      nestedPreserves)
  intro value
  exact optionalYulSemicolon_cursorMonotoneOnSuccess value

theorem yulStatementTerminated_startsAtCurrentTokenOnSuccess
    (nested : Parser YulStmt)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.StartsAtCurrentTokenOnSuccess
      (yulStatementTerminated nested) (·.span) := by
  unfold yulStatementTerminated
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (yulStatementCore_startsAtCurrentTokenOnSuccess nested nestedValid
      nestedPreserves)
  intro value input parsed final result
  rw [optionalYulSemicolon_value_eq value parsed input final result]

private theorem yulStatementAdvance_state_shape {input next : State}
    {token : Token} (advanced : input.advance? = some (token, next)) :
    input.peek? = some token ∧
      next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      exact ⟨rfl, rfl⟩

/-- Finishing statement recovery retains a source-valid error range. -/
theorem finishRecoveredYulStatement_validFor (first last : SourceSpan)
    (state : State) (stateValid : state.ValidFor)
    (firstValid : first.ValidFor state.file)
    (lastValid : last.ValidFor state.file)
    (ordered : first.startByte ≤ last.endByte) :
    (finishRecoveredYulStatement first last state).ValidFor state
      YulStmt.ValidFor := by
  have spanValid := SourceSpan.cover_validFor firstValid lastValid ordered
  unfold finishRecoveredYulStatement Reply.ValidFor
  exact ⟨YulStmt.ValidFor.error spanValid,
    stateValid.emit_validFor _ spanValid, rfl⟩

/-- Statement recovery preserves the provenance of its consumed range. -/
theorem recoverYulStatementAux_validFor (first : SourceSpan) :
    ∀ fuel last state lastIndex lastToken,
      state.ValidFor → first.ValidFor state.file →
      last.ValidFor state.file → first.startByte ≤ last.endByte →
      state.tokens[lastIndex]? = some lastToken → lastToken.span = last →
      lastIndex < state.cursor →
      (recoverYulStatementAux first last fuel state).ValidFor state
        YulStmt.ValidFor := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro last state lastIndex lastToken stateValid firstValid lastValid
        ordered lastFound lastSpan lastBefore
      unfold recoverYulStatementAux
      split
      · exact finishRecoveredYulStatement_validFor first last state
          stateValid firstValid lastValid ordered
      · cases advanced : state.advance? with
        | none =>
            exact finishRecoveredYulStatement_validFor first last state
              stateValid firstValid lastValid ordered
        | some pair =>
            rcases pair with ⟨token, next⟩
            have nextValid := stateValid.advance?_validFor advanced
            have shape := yulStatementAdvance_state_shape advanced
            have tokenValid := stateValid.peek?_span_validFor shape.1
            have currentFound :=
              State.getElem?_eq_some_of_peek?_eq_some shape.1
            have lastBeforeCurrent :=
              stateValid.token_end_le_token_start_of_getElem?_lt lastFound
                currentFound lastBefore
            apply (inductionHypothesis token.span next state.cursor token
              nextValid (by simpa [shape.2] using firstValid)
              (by simpa [shape.2] using tokenValid)
              (Nat.le_trans ordered (Nat.le_trans
                (by simpa [lastSpan] using lastBeforeCurrent)
                tokenValid.2.1))
              (by simpa [shape.2] using currentFound) rfl
              (by simp [shape.2])).of_file_eq
            simp [shape.2]

/-- Successful statement recovery preserves carrier, cursor, and first byte. -/
theorem recoverYulStatementAux_ok_state_shape (first : SourceSpan) :
    ∀ fuel last input statement next,
      recoverYulStatementAux first last fuel input = .ok statement next →
      next.tokens = input.tokens ∧ input.cursor ≤ next.cursor ∧
        statement.span.startByte = first.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro last input statement next result
      unfold recoverYulStatementAux at result
      split at result
      · unfold finishRecoveredYulStatement at result
        cases result
        exact ⟨rfl, Nat.le_refl _, rfl⟩
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            unfold finishRecoveredYulStatement at result
            cases result
            exact ⟨rfl, Nat.le_refl _, rfl⟩
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            have recursive := inductionHypothesis token.span afterToken
              statement next result
            have shape := yulStatementAdvance_state_shape advanced
            exact ⟨recursive.1.trans (by simp [shape.2]),
              Nat.le_trans (by simp [shape.2]) recursive.2.1,
              recursive.2.2⟩

/-- Statement recovery preserves every ordinary token window. -/
theorem recoverYulStatementAux_preservesTokenWindow (first last : SourceSpan) :
    ∀ fuel, Parser.PreservesTokenWindow
      (recoverYulStatementAux first last fuel) := by
  intro fuel input
  induction fuel generalizing last input with
  | zero => trivial
  | succ fuel inductionHypothesis =>
      unfold recoverYulStatementAux
      split
      · unfold finishRecoveredYulStatement Reply.PreservesTokenWindow
        exact ⟨rfl, rfl⟩
      · cases advanced : input.advance? with
        | none =>
            unfold finishRecoveredYulStatement Reply.PreservesTokenWindow
            exact ⟨rfl, rfl⟩
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            exact (inductionHypothesis token.span afterToken).trans (by
              simp [(yulStatementAdvance_state_shape advanced).2])

theorem recoverYulStatementAux_preservesTokensOnSuccess
    (first last : SourceSpan) (fuel : Nat) :
    Parser.PreservesTokensOnSuccess
      (recoverYulStatementAux first last fuel) :=
  (recoverYulStatementAux_preservesTokenWindow first last fuel).preservesTokensOnSuccess

theorem recoverYulStatementAux_cursorMonotoneOnSuccess
    (first last : SourceSpan) (fuel : Nat) :
    Parser.CursorMonotoneOnSuccess
      (recoverYulStatementAux first last fuel) := by
  intro input statement next result
  exact (recoverYulStatementAux_ok_state_shape first fuel last input statement
    next result).2.1

/-- Optional termination retains any token-window contract of the core parser. -/
theorem yulStatementTerminated_preservesTokenWindow (nested : Parser YulStmt)
    (coreShape : Parser.PreservesTokenWindow (yulStatementCore nested)) :
    Parser.PreservesTokenWindow (yulStatementTerminated nested) := by
  unfold yulStatementTerminated
  apply Parser.bind_preservesTokenWindow coreShape
  intro statement
  exact optionalYulSemicolon_preservesTokenWindow statement

/-- One recovering statement layer preserves recursive source provenance. -/
theorem yulStatementLayer_validFor (nested : Parser YulStmt)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested)
    (coreShape : Parser.PreservesTokenWindow (yulStatementCore nested)) :
    (yulStatementLayer nested).ValidFor YulStmt.ValidFor := by
  intro input inputValid
  unfold yulStatementLayer
  cases terminatedResult : yulStatementTerminated nested input with
  | ok statement next =>
      have valid := yulStatementTerminated_validFor nested nestedValid
        nestedPreserves input inputValid
      rw [terminatedResult] at valid
      exact valid
  | invariant error => trivial
  | reject failure failedState =>
      have terminatedValid := yulStatementTerminated_validFor nested nestedValid
        nestedPreserves input inputValid
      rw [terminatedResult] at terminatedValid
      have terminatedShape :=
        yulStatementTerminated_preservesTokenWindow nested coreShape input
      rw [terminatedResult] at terminatedShape
      let rewound : State := { failedState with cursor := input.cursor }
      have rewoundValid : rewound.ValidFor := {
        tokens := terminatedValid.2.1.tokens
        cursor_le_endIndex := by
          simpa [rewound, terminatedShape.2] using
            inputValid.cursor_le_endIndex
        endIndex_le_size := terminatedValid.2.1.endIndex_le_size
        endByte_le_source := terminatedValid.2.1.endByte_le_source
        endByte_boundary := terminatedValid.2.1.endByte_boundary
        diagnosticsRev := terminatedValid.2.1.diagnosticsRev
      }
      have rewoundFile : rewound.file = input.file := by
        simpa [rewound] using terminatedValid.2.2
      have failureValid : failure.span.ValidFor rewound.file := by
        simpa [rewound, terminatedValid.2.2] using terminatedValid.1
      change (if rewound.atEnd || isSymbol rewound .rightBrace then
        Reply.reject failure rewound else
        match rewound.advance? with
        | some (token, next) =>
            recoverYulStatementAux token.span token.span
              (next.remainingCount + 1) (next.emit failure.toDiagnostic)
        | none => Reply.reject failure rewound).ValidFor input YulStmt.ValidFor
      split
      · exact ⟨terminatedValid.1, rewoundValid, rewoundFile⟩
      · cases advanced : rewound.advance? with
        | none => exact ⟨terminatedValid.1, rewoundValid, rewoundFile⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            have advanceShape := yulStatementAdvance_state_shape advanced
            have nextValid := rewoundValid.advance?_validFor advanced
            have tokenValid : token.span.ValidFor next.file := by
              rw [advanceShape.2]
              exact rewoundValid.peek?_span_validFor advanceShape.1
            have emittedValid := nextValid.emit_validFor failure.toDiagnostic
              (by simpa [advanceShape.2] using
                failure.toDiagnostic_span_validFor failureValid)
            have currentFound :
                (next.emit failure.toDiagnostic).tokens[rewound.cursor]? =
                  some token := by
              simpa [advanceShape.2, State.emit] using
                State.getElem?_eq_some_of_peek?_eq_some advanceShape.1
            have recovered := recoverYulStatementAux_validFor token.span
              (next.remainingCount + 1) token.span
              (next.emit failure.toDiagnostic) rewound.cursor token emittedValid
              (by simpa [State.emit] using tokenValid)
              (by simpa [State.emit] using tokenValid)
              tokenValid.2.1 currentFound rfl (by
                simp [advanceShape.2, State.emit])
            exact recovered.of_file_eq (by
              simpa [advanceShape.2, State.emit] using rewoundFile)

/-- A recovering statement layer preserves every ordinary token window. -/
theorem yulStatementLayer_preservesTokenWindow (nested : Parser YulStmt)
    (coreShape : Parser.PreservesTokenWindow (yulStatementCore nested)) :
    Parser.PreservesTokenWindow (yulStatementLayer nested) := by
  intro input
  unfold yulStatementLayer
  cases terminatedResult : yulStatementTerminated nested input with
  | invariant error => trivial
  | ok statement next =>
      have terminatedShape :=
        yulStatementTerminated_preservesTokenWindow nested coreShape input
      rw [terminatedResult] at terminatedShape
      exact terminatedShape
  | reject failure failedState =>
      have terminatedShape :=
        yulStatementTerminated_preservesTokenWindow nested coreShape input
      rw [terminatedResult] at terminatedShape
      let rewound : State := { failedState with cursor := input.cursor }
      have failedShape : failedState.tokens = input.tokens ∧
          failedState.window = input.window := by
        simpa only [Reply.PreservesTokenWindow] using terminatedShape
      have rewoundShape : rewound.tokens = input.tokens ∧
          rewound.window = input.window := by
        simpa [rewound] using failedShape
      change (if rewound.atEnd || isSymbol rewound .rightBrace then
        Reply.reject failure rewound else
        match rewound.advance? with
        | some (token, next) =>
            recoverYulStatementAux token.span token.span
              (next.remainingCount + 1) (next.emit failure.toDiagnostic)
        | none => Reply.reject failure rewound).PreservesTokenWindow input
      split
      · exact rewoundShape
      · cases advanced : rewound.advance? with
        | none => exact rewoundShape
        | some pair =>
            rcases pair with ⟨token, next⟩
            have recovered := recoverYulStatementAux_preservesTokenWindow
              token.span token.span (next.remainingCount + 1)
              (next.emit failure.toDiagnostic)
            have advanceShape := yulStatementAdvance_state_shape advanced
            exact recovered.trans (by
              simpa [State.emit, advanceShape.2] using rewoundShape)

theorem yulStatementLayer_preservesTokensOnSuccess (nested : Parser YulStmt)
    (coreShape : Parser.PreservesTokenWindow (yulStatementCore nested)) :
    Parser.PreservesTokensOnSuccess (yulStatementLayer nested) :=
  (yulStatementLayer_preservesTokenWindow nested coreShape).preservesTokensOnSuccess

/-- A recovering statement layer never rewinds its caller's cursor. -/
theorem yulStatementLayer_cursorMonotoneOnSuccess (nested : Parser YulStmt)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.CursorMonotoneOnSuccess (yulStatementLayer nested) := by
  intro input statement next result
  unfold yulStatementLayer at result
  cases terminatedResult : yulStatementTerminated nested input with
  | invariant error => simp [terminatedResult] at result
  | ok value afterCore =>
      simp only [terminatedResult] at result
      have monotone := yulStatementTerminated_cursorMonotoneOnSuccess nested
        nestedValid nestedPreserves input value afterCore terminatedResult
      cases result
      exact monotone
  | reject failure failedState =>
      simp only [terminatedResult] at result
      let rewound : State := { failedState with cursor := input.cursor }
      change (if rewound.atEnd || isSymbol rewound .rightBrace then
        Reply.reject failure rewound else
        match rewound.advance? with
        | some (token, afterToken) =>
            recoverYulStatementAux token.span token.span
              (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic)
        | none => Reply.reject failure rewound) = .ok statement next at result
      split at result
      · contradiction
      · cases advanced : rewound.advance? with
        | none => simp [advanced] at result
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            have recovered := recoverYulStatementAux_cursorMonotoneOnSuccess
              token.span token.span (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic) statement next result
            have advanceShape := yulStatementAdvance_state_shape advanced
            exact Nat.le_trans (by simp [advanceShape.2, State.emit, rewound])
              recovered

/-- A successful recovering layer starts at its caller's current token. -/
theorem yulStatementLayer_startsAtCurrentTokenOnSuccess
    (nested : Parser YulStmt)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested)
    (coreShape : Parser.PreservesTokenWindow (yulStatementCore nested)) :
    Parser.StartsAtCurrentTokenOnSuccess (yulStatementLayer nested) (·.span) := by
  intro input statement next result
  unfold yulStatementLayer at result
  cases terminatedResult : yulStatementTerminated nested input with
  | invariant error => simp [terminatedResult] at result
  | ok value afterCore =>
      simp only [terminatedResult] at result
      have starts := yulStatementTerminated_startsAtCurrentTokenOnSuccess nested
        nestedValid nestedPreserves input value afterCore terminatedResult
      cases result
      simpa using starts
  | reject failure failedState =>
      simp only [terminatedResult] at result
      have terminatedShape :=
        yulStatementTerminated_preservesTokenWindow nested coreShape input
      rw [terminatedResult] at terminatedShape
      let rewound : State := { failedState with cursor := input.cursor }
      change (if rewound.atEnd || isSymbol rewound .rightBrace then
        Reply.reject failure rewound else
        match rewound.advance? with
        | some (token, afterToken) =>
            recoverYulStatementAux token.span token.span
              (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic)
        | none => Reply.reject failure rewound) = .ok statement next at result
      split at result
      · contradiction
      · cases advanced : rewound.advance? with
        | none => simp [advanced] at result
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            have advanceShape := yulStatementAdvance_state_shape advanced
            have found : input.peek? = some token := by
              have rewoundFound := advanceShape.1
              unfold State.peek? at rewoundFound ⊢
              simpa [rewound, terminatedShape.1, terminatedShape.2] using
                rewoundFound
            have recovered := recoverYulStatementAux_ok_state_shape token.span
              (afterToken.remainingCount + 1) token.span
              (afterToken.emit failure.toDiagnostic) statement next result
            exact ⟨token, found, recovered.2.2.symm⟩

/-- Every fuel-bounded statement parser preserves ordinary token windows. -/
theorem yulStatementWithFuel_preservesTokenWindow :
    ∀ fuel, Parser.PreservesTokenWindow (yulStatementWithFuel fuel) := by
  intro fuel
  induction fuel with
  | zero => intro input; trivial
  | succ fuel inductionHypothesis =>
      exact yulStatementLayer_preservesTokenWindow
        (yulStatementWithFuel fuel)
        (yulStatementCore_preservesTokenWindow
          (yulStatementWithFuel fuel) inductionHypothesis)

theorem yulStatementWithFuel_preservesTokensOnSuccess (fuel : Nat) :
    Parser.PreservesTokensOnSuccess (yulStatementWithFuel fuel) :=
  (yulStatementWithFuel_preservesTokenWindow fuel).preservesTokensOnSuccess

/-- Every fuel-bounded statement parser retains source provenance. -/
theorem yulStatementWithFuel_validFor :
    ∀ fuel, (yulStatementWithFuel fuel).ValidFor YulStmt.ValidFor := by
  intro fuel
  induction fuel with
  | zero => intro input inputValid; trivial
  | succ fuel inductionHypothesis =>
      have nestedShape := yulStatementWithFuel_preservesTokenWindow fuel
      exact yulStatementLayer_validFor (yulStatementWithFuel fuel)
        inductionHypothesis nestedShape.preservesTokensOnSuccess
        (yulStatementCore_preservesTokenWindow
          (yulStatementWithFuel fuel) nestedShape)

/-- Fuel-bounded statement successes never rewind their caller. -/
theorem yulStatementWithFuel_cursorMonotoneOnSuccess :
    ∀ fuel, Parser.CursorMonotoneOnSuccess (yulStatementWithFuel fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro input statement next result
      simp [yulStatementWithFuel] at result
  | succ fuel inductionHypothesis =>
      have nestedShape := yulStatementWithFuel_preservesTokenWindow fuel
      exact yulStatementLayer_cursorMonotoneOnSuccess
        (yulStatementWithFuel fuel)
        (yulStatementWithFuel_validFor fuel)
        nestedShape.preservesTokensOnSuccess

/-- Fuel-bounded statement successes begin at the current token. -/
theorem yulStatementWithFuel_startsAtCurrentTokenOnSuccess :
    ∀ fuel, Parser.StartsAtCurrentTokenOnSuccess
      (yulStatementWithFuel fuel) (·.span) := by
  intro fuel
  induction fuel with
  | zero =>
      intro input statement next result
      simp [yulStatementWithFuel] at result
  | succ fuel inductionHypothesis =>
      have nestedShape := yulStatementWithFuel_preservesTokenWindow fuel
      exact yulStatementLayer_startsAtCurrentTokenOnSuccess
        (yulStatementWithFuel fuel)
        (yulStatementWithFuel_validFor fuel)
        nestedShape.preservesTokensOnSuccess
        (yulStatementCore_preservesTokenWindow
          (yulStatementWithFuel fuel) nestedShape)

/-- Public Yul statement parsing preserves every ordinary token window. -/
theorem yulStatement_preservesTokenWindow :
    Parser.PreservesTokenWindow yulStatement := by
  intro input
  unfold yulStatement
  exact yulStatementWithFuel_preservesTokenWindow
    (input.remainingCount + 1) input

theorem yulStatement_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess yulStatement :=
  yulStatement_preservesTokenWindow.preservesTokensOnSuccess

/-- Public Yul statement parsing retains source provenance. -/
theorem yulStatement_validFor : yulStatement.ValidFor YulStmt.ValidFor := by
  intro input inputValid
  unfold yulStatement
  exact yulStatementWithFuel_validFor (input.remainingCount + 1)
    input inputValid

/-- Public Yul statement successes never rewind their caller. -/
theorem yulStatement_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulStatement := by
  intro input statement next result
  unfold yulStatement at result
  exact yulStatementWithFuel_cursorMonotoneOnSuccess
    (input.remainingCount + 1) input statement next result

/-- Public Yul statement successes begin at the current token. -/
theorem yulStatement_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess yulStatement (·.span) := by
  intro input statement next result
  unfold yulStatement at result
  exact yulStatementWithFuel_startsAtCurrentTokenOnSuccess
    (input.remainingCount + 1) input statement next result

/-- A complete Yul body retains every statement and its enclosing range. -/
theorem yulBody_validFor :
    yulBody.ValidFor (YulParsedBlock.ValidFor YulStmt.ValidFor) :=
  yulBlock_validFor YulStmt.ValidFor yulStatement yulStatement_validFor
    yulStatement_preservesTokensOnSuccess

/-- Complete Yul bodies preserve every ordinary token window. -/
theorem yulBody_preservesTokenWindow :
    Parser.PreservesTokenWindow yulBody :=
  yulBlock_preservesTokenWindow yulStatement
    yulStatement_preservesTokenWindow

theorem yulBody_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess yulBody :=
  yulBody_preservesTokenWindow.preservesTokensOnSuccess

/-- Successful Yul-body parsing never rewinds its caller. -/
theorem yulBody_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulBody :=
  yulBlock_cursorMonotoneOnSuccess yulStatement
    yulStatement_preservesTokensOnSuccess

/-- A successful Yul body starts at its opening brace token. -/
theorem yulBody_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess yulBody (·.span) :=
  yulBlock_startsAtCurrentTokenOnSuccess yulStatement
    yulStatement_preservesTokensOnSuccess

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulBlockStatementOrdinarySoundnessProperties
/-! Executable ordinary outcome bridges for Yul blocks in statement form. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful executable block statement lifts the exact ordinary
underlying block outcome. -/
theorem yulBlockStatement_success_ordinary_sound
    (nested : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {statement : YulStmt},
      nested input = .ok statement output →
        statementOrdinary input.declarativeRemainder statement
          output.declarativeRemainder)
    {input output : State} {statement : YulStmt}
    (result : yulBlockStatement nested input = .ok statement output) :
    DeclarativeGrammar.YulBlockStatementOrdinaryParses statementOrdinary
      input.declarativeRemainder statement output.declarativeRemainder := by
  unfold yulBlockStatement at result
  cases blockResult : yulBlock nested input with
  | invariant error => simp [bind, blockResult] at result
  | reject failure rejected => simp [bind, blockResult] at result
  | ok block afterBlock =>
      simp only [bind, blockResult, pure] at result
      cases result
      exact .parsed (yulBlock_success_ordinary_sound nested statementOrdinary
        nestedSuccessSound blockResult)

/-- Every executable block-statement rejection is exactly the underlying
block rejection. -/
theorem yulBlockStatement_reject_ordinary_sound
    (nested : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {statement : YulStmt},
      nested input = .ok statement output →
        statementOrdinary input.declarativeRemainder statement
          output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : yulBlockStatement nested input = .reject failure rejected) :
    DeclarativeGrammar.YulBlockStatementRejects statementOrdinary
      statementRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold yulBlockStatement at result
  cases blockResult : yulBlock nested input with
  | invariant error => simp [bind, blockResult] at result
  | ok block afterBlock => simp [bind, blockResult, pure] at result
  | reject blockFailure blockRejected =>
      simp only [bind, blockResult] at result
      cases result
      exact yulBlock_reject_ordinary_sound nested statementOrdinary
        statementRejects nestedSuccessSound nestedRejectSound blockResult

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulStatementBasicDiagnosticReflectionProperties
/-!
Diagnostic reflection for the public inline-Yul expression parser and the
basic statement forms built from it.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace YulExpressionInternals

/-- Every fuel-bounded public expression parser reflects diagnostic freedom. -/
theorem withFuel_reflectsDiagnosticFreeOnSuccess : ∀ fuel,
    Parser.ReflectsDiagnosticFreeOnSuccess (withFuel fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro input expression next result diagnosticFree
      simp [withFuel] at result
  | succ fuel inductionHypothesis =>
      exact yulExpressionLayer_reflectsDiagnosticFreeOnSuccess
        (withFuel fuel) inductionHypothesis

end YulExpressionInternals

/-- The fixed public inline-Yul expression parser cannot erase diagnostics. -/
theorem yulExpression_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess yulExpression := by
  intro input expression next result diagnosticFree
  unfold yulExpression at result
  exact YulExpressionInternals.withFuel_reflectsDiagnosticFreeOnSuccess
    (input.remainingCount + 1) input expression next result diagnosticFree

/-- Optional Yul `let` initialization reflects through its committed branch. -/
theorem yulLetInitializer_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess yulLetInitializer := by
  unfold yulLetInitializer
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (symbol_reflectsDiagnosticFreeOnSuccess .colonEqual .yulStatement)
    intro operator
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      yulExpression_reflectsDiagnosticFreeOnSuccess
    intro value
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Inline-Yul `let` parsing reflects through names and initialization. -/
theorem yulLetStatement_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess yulLetStatement := by
  unfold yulLetStatement
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .letKw .yulStatement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    yulNames_reflectsDiagnosticFreeOnSuccess
  intro names
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    yulLetInitializer_reflectsDiagnosticFreeOnSuccess
  intro initializer
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Inline-Yul assignment parsing reflects through targets and value. -/
theorem yulAssignment_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess yulAssignment := by
  unfold yulAssignment
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    yulNames_reflectsDiagnosticFreeOnSuccess
  intro names
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .colonEqual .yulStatement)
  intro operator
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    yulExpression_reflectsDiagnosticFreeOnSuccess
  intro value
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Inline-Yul expression statements reflect through their expression. -/
theorem yulExpressionStatement_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess yulExpressionStatement := by
  unfold yulExpressionStatement
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    yulExpression_reflectsDiagnosticFreeOnSuccess
  intro expression
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Source-level Yul `return(...)` reflects through its argument list. -/
theorem yulReturnBuiltin_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess yulReturnBuiltin := by
  unfold yulReturnBuiltin
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .returnKw .yulStatement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimited_reflectsDiagnosticFreeOnSuccess .leftParen .rightParen true
      yulExpression .yulExpression .yul
        yulExpression_reflectsDiagnosticFreeOnSuccess)
  intro arguments
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulStatementBasicSoundnessProperties
/-!
Exact diagnostic-free soundness for the basic inline-Yul statement forms.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {alpha beta : Type} {first : Parser alpha}
    {next : alpha → Parser beta} {input final : State} {value : beta}
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

/-- Every optional Yul `let` initializer success follows the exact `:=`
priority and the supplied public-expression relation. -/
theorem yulLetInitializer_success_sound
    (expressionParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → yulExpression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {initializer : Option YulExpr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulLetInitializer input = .ok initializer next) :
    DeclarativeGrammar.YulLetInitializerParses expressionParses
      input.declarativeRemainder initializer next.declarativeRemainder := by
  unfold yulLetInitializer getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .colonEqual
  · simp only [present, if_true] at result
    rcases bind_ok_components result with
      ⟨operator, afterOperator, operatorResult, valueStage⟩
    rcases bind_ok_components valueStage with
      ⟨value, afterValue, valueResult, finished⟩
    cases finished
    exact .present operator.span
      (symbol_success_exactTokenParses .colonEqual .yulStatement
        operatorResult)
      (expressionSound diagnosticFree valueResult)
  · have absent : isSymbol input .colonEqual = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (symbolAbsentAt_of_isSymbol_eq_false .colonEqual absent)

/-- Every diagnostic-free inline-Yul `let` success retains its exact names,
initializer priority, span, AST, and remainder. -/
theorem yulLetStatement_success_sound
    (expressionParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → yulExpression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {statement : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulLetStatement input = .ok statement next) :
    DeclarativeGrammar.YulLetStatementParses expressionParses
      input.declarativeRemainder statement next.declarativeRemainder := by
  unfold yulLetStatement at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, namesStage⟩
  rcases bind_ok_components namesStage with
    ⟨names, afterNames, namesResult, initializerStage⟩
  rcases bind_ok_components initializerStage with
    ⟨initializer, afterInitializer, initializerResult, finished⟩
  cases finished
  have afterNamesFree := yulLetInitializer_reflectsDiagnosticFreeOnSuccess
    afterNames initializer next initializerResult diagnosticFree
  exact .parsed marker.span names.span
    (keyword_success_exactTokenParses .letKw .yulStatement markerResult)
    (yulNames_success_sound afterNamesFree namesResult)
    (yulLetInitializer_success_sound expressionParses expressionSound
      diagnosticFree initializerResult)

/-- Every diagnostic-free inline-Yul assignment success retains the forward
target order, exact `:=`, value, covering span, and remainder. -/
theorem yulAssignment_success_sound
    (expressionParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → yulExpression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {statement : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulAssignment input = .ok statement next) :
    DeclarativeGrammar.YulAssignmentParses expressionParses
      input.declarativeRemainder statement next.declarativeRemainder := by
  unfold yulAssignment at result
  rcases bind_ok_components result with
    ⟨names, afterNames, namesResult, operatorStage⟩
  rcases bind_ok_components operatorStage with
    ⟨operator, afterOperator, operatorResult, valueStage⟩
  rcases bind_ok_components valueStage with
    ⟨value, afterValue, valueResult, finished⟩
  cases finished
  have afterOperatorFree := yulExpression_reflectsDiagnosticFreeOnSuccess
    afterOperator value next valueResult diagnosticFree
  have afterNamesFree := symbol_reflectsDiagnosticFreeOnSuccess .colonEqual
    .yulStatement afterNames operator afterOperator operatorResult
      afterOperatorFree
  exact .parsed names.span operator.span
    (yulNames_success_sound afterNamesFree namesResult)
    (symbol_success_exactTokenParses .colonEqual .yulStatement operatorResult)
    (expressionSound diagnosticFree valueResult)

/-- Every diagnostic-free expression-statement success is the exact lift of
the supplied public-expression relation. -/
theorem yulExpressionStatement_success_sound
    (expressionParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → yulExpression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {statement : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulExpressionStatement input = .ok statement next) :
    DeclarativeGrammar.YulExpressionStatementParses expressionParses
      input.declarativeRemainder statement next.declarativeRemainder := by
  unfold yulExpressionStatement at result
  rcases bind_ok_components result with
    ⟨expression, afterExpression, expressionResult, finished⟩
  cases finished
  exact .parsed (expressionSound diagnosticFree expressionResult)

/-- Every diagnostic-free source-level `return(...)` success is the exact
synthesized call, including allow-empty/trailing arguments and delimiters. -/
theorem yulReturnBuiltin_success_sound
    (expressionParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → yulExpression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {statement : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulReturnBuiltin input = .ok statement next) :
    DeclarativeGrammar.YulReturnBuiltinParses expressionParses
      input.declarativeRemainder statement next.declarativeRemainder := by
  unfold yulReturnBuiltin at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, argumentsStage⟩
  rcases bind_ok_components argumentsStage with
    ⟨arguments, afterArguments, argumentsResult, finished⟩
  cases finished
  exact .parsed marker.span
    (keyword_success_exactTokenParses .returnKw .yulStatement markerResult)
    (delimited_allowEmpty_trailing_success_sound_of_diagnosticFree
      .leftParen .rightParen yulExpression expressionParses .yulExpression
      .yul expressionSound yulExpression_reflectsDiagnosticFreeOnSuccess
      yulExpression_preservesTokenWindow diagnosticFree argumentsResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulStatementControlDiagnosticReflectionProperties
/-!
Diagnostic reflection for Yul block, `if`, and `for` statements.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem yulBlockStatement_reflectsDiagnosticFreeOnSuccess
    (statement : Parser YulStmt)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (yulBlockStatement statement) := by
  unfold yulBlockStatement
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (yulBlock_reflectsDiagnosticFreeOnSuccess statement statementReflects)
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

theorem yulIfStatement_reflectsDiagnosticFreeOnSuccess
    (statement : Parser YulStmt)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    Parser.ReflectsDiagnosticFreeOnSuccess (yulIfStatement statement) := by
  unfold yulIfStatement
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .ifKw .yulStatement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    yulExpression_reflectsDiagnosticFreeOnSuccess
  intro condition
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (yulBlock_reflectsDiagnosticFreeOnSuccess statement statementReflects)
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

theorem yulForStatement_reflectsDiagnosticFreeOnSuccess
    (statement : Parser YulStmt)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    Parser.ReflectsDiagnosticFreeOnSuccess (yulForStatement statement) := by
  unfold yulForStatement
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .forKw .yulStatement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (yulBlock_reflectsDiagnosticFreeOnSuccess statement statementReflects)
  intro initializer
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    yulExpression_reflectsDiagnosticFreeOnSuccess
  intro condition
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (yulBlock_reflectsDiagnosticFreeOnSuccess statement statementReflects)
  intro post
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (yulBlock_reflectsDiagnosticFreeOnSuccess statement statementReflects)
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulStatementControlSoundnessProperties
/-!
Exact diagnostic-free soundness for Yul block, `if`, and `for` statements.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem yulBlockStatement_success_sound
    (statement : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulBlockStatement statement input = .ok value next) :
    DeclarativeGrammar.YulBlockStatementParses statementParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold yulBlockStatement at result
  rcases bind_ok_components result with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed (yulBlock_success_sound statement statementParses
    statementReflects statementSound diagnosticFree bodyResult)

theorem yulIfStatement_success_sound
    (statement : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (expressionParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → yulExpression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulIfStatement statement input = .ok value next) :
    DeclarativeGrammar.YulIfStatementParses statementParses expressionParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold yulIfStatement at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, conditionStage⟩
  rcases bind_ok_components conditionStage with
    ⟨condition, afterCondition, conditionResult, bodyStage⟩
  rcases bind_ok_components bodyStage with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  have afterConditionFree := yulBlock_reflectsDiagnosticFreeOnSuccess
    statement statementReflects afterCondition body next bodyResult
      diagnosticFree
  exact .parsed marker.span
    (keyword_success_exactTokenParses .ifKw .yulStatement markerResult)
    (expressionSound afterConditionFree conditionResult)
    (yulBlock_success_sound statement statementParses statementReflects
      statementSound diagnosticFree bodyResult)

theorem yulForStatement_success_sound
    (statement : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (expressionParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → yulExpression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulForStatement statement input = .ok value next) :
    DeclarativeGrammar.YulForStatementParses statementParses expressionParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold yulForStatement at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, initializerStage⟩
  rcases bind_ok_components initializerStage with
    ⟨initializer, afterInitializer, initializerResult, conditionStage⟩
  rcases bind_ok_components conditionStage with
    ⟨condition, afterCondition, conditionResult, postStage⟩
  rcases bind_ok_components postStage with
    ⟨post, afterPost, postResult, bodyStage⟩
  rcases bind_ok_components bodyStage with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  have afterPostFree := yulBlock_reflectsDiagnosticFreeOnSuccess statement
    statementReflects afterPost body next bodyResult diagnosticFree
  have afterConditionFree := yulBlock_reflectsDiagnosticFreeOnSuccess
    statement statementReflects afterCondition post afterPost postResult
      afterPostFree
  have afterInitializerFree :=
    yulExpression_reflectsDiagnosticFreeOnSuccess afterInitializer condition
      afterCondition conditionResult afterConditionFree
  exact .parsed marker.span
    (keyword_success_exactTokenParses .forKw .yulStatement markerResult)
    (yulBlock_success_sound statement statementParses statementReflects
      statementSound afterInitializerFree initializerResult)
    (expressionSound afterConditionFree conditionResult)
    (yulBlock_success_sound statement statementParses statementReflects
      statementSound afterPostFree postResult)
    (yulBlock_success_sound statement statementParses statementReflects
      statementSound diagnosticFree bodyResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreYulStatementRecoveryDiagnosticProperties
/-!
Diagnostic commitments at inline-Yul statement choice and recovery boundaries.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A diagnostic-free recognized-Yul choice success is the unchanged primary
success; fallback success after primary rejection commits that failure. -/
theorem recognizedYulStatementOrFallback_primary_of_diagnosticFree_success
    (primary fallback : Parser YulStmt)
    {input next : State} {value : YulStmt}
    (result : recognizedYulStatementOrFallback primary fallback input =
      .ok value next)
    (diagnosticFree : next.diagnosticsRev = []) :
    primary input = .ok value next := by
  unfold recognizedYulStatementOrFallback at result
  cases primaryResult : primary input with
  | ok primaryValue afterPrimary =>
      simp only [primaryResult] at result
      cases result
      rfl
  | reject failure failedState =>
      simp only [primaryResult] at result
      cases fallbackResult : fallback input with
      | invariant error => simp [fallbackResult] at result
      | reject fallbackFailure fallbackState =>
          simp [fallbackResult] at result
      | ok fallbackValue afterFallback =>
          simp only [fallbackResult] at result
          cases result
          simp [State.emit] at diagnosticFree
  | invariant error => simp [primaryResult] at result

theorem recognizedYulStatementOrFallback_reflectsDiagnosticFreeOnSuccess
    (primary fallback : Parser YulStmt)
    (primaryReflects : Parser.ReflectsDiagnosticFreeOnSuccess primary) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (recognizedYulStatementOrFallback primary fallback) := by
  intro input value next result diagnosticFree
  exact primaryReflects input value next
    (recognizedYulStatementOrFallback_primary_of_diagnosticFree_success
      primary fallback result diagnosticFree)
    diagnosticFree

/-- Finishing Yul-statement recovery always commits its diagnostic. -/
theorem finishRecoveredYulStatement_diagnostics_ne_nil_onSuccess
    (first last : SourceSpan) {input next : State} {value : YulStmt}
    (result : finishRecoveredYulStatement first last input = .ok value next) :
    next.diagnosticsRev ≠ [] := by
  unfold finishRecoveredYulStatement at result
  cases result
  simp [State.emit]

/-- Every successful Yul-statement recovery scan retains a diagnostic. -/
theorem recoverYulStatementAux_diagnostics_ne_nil_onSuccess
    (first last : SourceSpan) :
    ∀ fuel, ∀ {input next : State} {value : YulStmt},
      recoverYulStatementAux first last fuel input = .ok value next →
      next.diagnosticsRev ≠ [] := by
  intro fuel
  induction fuel generalizing last with
  | zero => simp [recoverYulStatementAux]
  | succ fuel inductionHypothesis =>
      intro input next value recovered
      unfold recoverYulStatementAux at recovered
      split at recovered
      · exact finishRecoveredYulStatement_diagnostics_ne_nil_onSuccess
          first last recovered
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at recovered
            exact finishRecoveredYulStatement_diagnostics_ne_nil_onSuccess
              first last recovered
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at recovered
            exact inductionHypothesis token.span recovered

/-- A diagnostic-free recovering Yul-statement layer success is exactly its
unchanged non-recovering terminated-statement success. -/
theorem yulStatementTerminated_of_diagnosticFree_layer_success
    (nested : Parser YulStmt) {input next : State} {value : YulStmt}
    (result : yulStatementLayer nested input = .ok value next)
    (diagnosticFree : next.diagnosticsRev = []) :
    yulStatementTerminated nested input = .ok value next := by
  unfold yulStatementLayer at result
  cases coreResult : yulStatementTerminated nested input with
  | ok coreValue afterCore =>
      simp only [coreResult] at result
      cases result
      rfl
  | reject failure failedState =>
      simp only [coreResult] at result
      let rewound : State := { failedState with cursor := input.cursor }
      change (if rewound.atEnd || isSymbol rewound .rightBrace then
          .reject failure rewound
        else
          match rewound.advance? with
          | some (token, afterToken) =>
              recoverYulStatementAux token.span token.span
                (afterToken.remainingCount + 1)
                (afterToken.emit failure.toDiagnostic)
          | none => .reject failure rewound) = .ok value next at result
      split at result
      · contradiction
      · cases advanced : rewound.advance? with
        | none => simp [advanced] at result
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            exact False.elim
              (recoverYulStatementAux_diagnostics_ne_nil_onSuccess
                token.span token.span (afterToken.remainingCount + 1) result
                  diagnosticFree)
  | invariant error => simp [coreResult] at result

theorem yulStatementLayer_reflectsDiagnosticFreeOnSuccess
    (nested : Parser YulStmt)
    (terminatedReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (yulStatementTerminated nested)) :
    Parser.ReflectsDiagnosticFreeOnSuccess (yulStatementLayer nested) := by
  intro input value next result diagnosticFree
  exact terminatedReflects input value next
    (yulStatementTerminated_of_diagnosticFree_layer_success nested result
      diagnosticFree)
    diagnosticFree

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreYulStatementBasicSoundnessProperties
/-!
Diagnostic reflection and exact soundness for keyword-only Yul statements and
optional semicolon termination.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem yulControlToken_reflectsDiagnosticFreeOnSuccess
    (keywordValue : HardKeyword) (statementValue : YulStmtValue) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (yulControlToken keywordValue statementValue) := by
  unfold yulControlToken
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess keywordValue .yulStatement)
  intro marker
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

theorem optionalYulSemicolon_reflectsDiagnosticFreeOnSuccess
    (value : YulStmt) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (optionalYulSemicolon value) := by
  unfold optionalYulSemicolon
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (symbol_reflectsDiagnosticFreeOnSuccess .semicolon .yulStatement)
    intro semicolon
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

theorem yulStatementTerminated_reflectsDiagnosticFreeOnSuccess
    (core : Parser YulStmt)
    (coreReflects : Parser.ReflectsDiagnosticFreeOnSuccess core) :
    Parser.ReflectsDiagnosticFreeOnSuccess (do
      optionalYulSemicolon (← core)) := by
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess coreReflects
  intro value
  exact optionalYulSemicolon_reflectsDiagnosticFreeOnSuccess value

theorem yulControlToken_success_sound
    (keywordValue : HardKeyword) (statementValue : YulStmtValue)
    {input next : State} {value : YulStmt}
    (result : yulControlToken keywordValue statementValue input =
      .ok value next) :
    DeclarativeGrammar.YulControlTokenParses keywordValue statementValue
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold yulControlToken at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, finished⟩
  cases finished
  exact .parsed marker.span
    (keyword_success_exactTokenParses keywordValue .yulStatement markerResult)

theorem optionalYulSemicolon_success_sound (value : YulStmt)
    {input next : State}
    (result : optionalYulSemicolon value input = .ok value next) :
    DeclarativeGrammar.OptionalYulSemicolonParses input.declarativeRemainder
      value next.declarativeRemainder := by
  unfold optionalYulSemicolon getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .semicolon
  · simp only [present, if_true] at result
    cases semicolonResult : symbol .semicolon .yulStatement input with
    | invariant error => simp [semicolonResult] at result
    | reject failure rejected => simp [semicolonResult] at result
    | ok semicolon afterSemicolon =>
        simp only [semicolonResult, pure] at result
        cases result
        exact .present semicolon.span
          (symbol_success_exactTokenParses .semicolon .yulStatement
            semicolonResult)
  · have absent : isSymbol input .semicolon = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (symbolAbsentAt_of_isSymbol_eq_false .semicolon absent)

theorem yulStatementTerminated_success_sound
    (core : Parser YulStmt)
    (coreParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (coreSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → core input = .ok value next →
      coreParses input.declarativeRemainder value next.declarativeRemainder)
    {input next : State} {value : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : (do optionalYulSemicolon (← core)) input = .ok value next) :
    DeclarativeGrammar.YulStatementTerminatedParses coreParses
      input.declarativeRemainder value next.declarativeRemainder := by
  rcases bind_ok_components result with
    ⟨coreValue, afterCore, coreResult, semicolonResult⟩
  have afterCoreFree := optionalYulSemicolon_reflectsDiagnosticFreeOnSuccess
    coreValue afterCore value next semicolonResult diagnosticFree
  have valueEq : coreValue = value := by
    unfold optionalYulSemicolon getState at semicolonResult
    simp only [bind] at semicolonResult
    split at semicolonResult
    · cases symbolResult : symbol .semicolon .yulStatement afterCore with
      | invariant error => simp [symbolResult] at semicolonResult
      | reject failure rejected => simp [symbolResult] at semicolonResult
      | ok semicolon afterSemicolon =>
          simp only [symbolResult, pure] at semicolonResult
          cases semicolonResult
          rfl
    · simp only [pure] at semicolonResult
      cases semicolonResult
      rfl
  subst coreValue
  exact ⟨afterCore.declarativeRemainder,
    coreSound afterCoreFree coreResult,
    optionalYulSemicolon_success_sound value semicolonResult⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulStatementTerminatedOrdinarySoundnessProperties
/-!
Unconditional ordinary-success and exact-rejection reflection for a Yul
statement core followed by its optional semicolon.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem reject_state_eq {α : Type}
    {leftFailure rightFailure : Failure} {leftState rightState : State}
    (result : (Reply.reject leftFailure leftState : Reply α) =
      .reject rightFailure rightState) :
    leftState = rightState := by
  injection result

/-- Optional-semicolon parsing has no rejection outcome. -/
private theorem optionalYulSemicolon_not_reject (value : YulStmt)
    {input rejected : State} {failure : Failure}
    (result : optionalYulSemicolon value input =
      .reject failure rejected) : False := by
  unfold optionalYulSemicolon getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .semicolon = true
  · simp only [present, if_true] at result
    rcases symbol_eq_ok_of_isSymbol_eq_true .semicolon .yulStatement present
      with ⟨semicolon, semicolonResult⟩
    simp only [semicolonResult, pure] at result
    contradiction
  · simp only [present, Bool.false_eq_true, if_false, pure] at result
    contradiction

/-- Every successful executable optional termination reflects an ordinary
terminated success whenever its core success does. -/
theorem yulStatementTerminated_success_ordinary_sound
    (nested : Parser YulStmt)
    (coreOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (coreSuccessSound : ∀ {input output : State} {statement : YulStmt},
      yulStatementCore nested input = .ok statement output →
        coreOrdinary input.declarativeRemainder statement
          output.declarativeRemainder)
    {input output : State} {statement : YulStmt}
    (result : yulStatementTerminated nested input = .ok statement output) :
    DeclarativeGrammar.YulStatementTerminatedOrdinaryParses coreOrdinary
      input.declarativeRemainder statement output.declarativeRemainder := by
  unfold yulStatementTerminated at result
  cases coreResult : yulStatementCore nested input with
  | invariant error => simp [bind, coreResult] at result
  | reject failure rejected => simp [bind, coreResult] at result
  | ok coreValue afterCore =>
      simp only [bind, coreResult] at result
      have valueEq := optionalYulSemicolon_value_eq coreValue statement
        afterCore output result
      subst statement
      exact ⟨afterCore.declarativeRemainder,
        coreSuccessSound coreResult,
        optionalYulSemicolon_success_sound coreValue result⟩

/-- Every executable rejection of optional termination is exactly the core
rejection, since optional-semicolon parsing itself cannot reject. -/
theorem yulStatementTerminated_reject_ordinary_sound
    (nested : Parser YulStmt)
    (coreRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (coreRejectSound : ∀ {input rejected : State} {failure : Failure},
      yulStatementCore nested input = .reject failure rejected →
        coreRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : yulStatementTerminated nested input =
      .reject failure rejected) :
    DeclarativeGrammar.YulStatementTerminatedRejects coreRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold yulStatementTerminated at result
  cases coreResult : yulStatementCore nested input with
  | invariant error => simp [bind, coreResult] at result
  | reject coreFailure afterCore =>
      simp only [bind, coreResult] at result
      have stateEq := reject_state_eq result
      cases stateEq
      exact coreRejectSound coreResult
  | ok coreValue afterCore =>
      simp only [bind, coreResult] at result
      exact False.elim (optionalYulSemicolon_not_reject coreValue result)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulStatementRecoveryOrdinarySoundnessProperties
/-! Exact ordinary-success reflection for outer Yul-statement recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem isSymbol_eq_true_of_tokenAt (value : Symbol)
    {input : State} {span : SourceSpan}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol value }) :
    isSymbol input value = true := by
  unfold isSymbol State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]
  cases value <;> rfl

private theorem yulStatementRejects_of_rightBrace {input : State}
    (present : isSymbol input .rightBrace = true) :
    DeclarativeGrammar.YulStatementRejects input.declarativeRemainder
      input.declarativeRemainder := by
  rcases symbol_eq_ok_of_isSymbol_eq_true .rightBrace .yulStatement present
      with ⟨token, parsed⟩
  exact .rightBrace
    (symbol_ok_tokenAt .rightBrace .yulStatement parsed).1

/-- An executable statement boundary gives exact declarative rejection. -/
theorem yulStatementRejects_of_boundary (input : State)
    (boundary : (input.atEnd || isSymbol input .rightBrace) = true) :
    DeclarativeGrammar.YulStatementRejects input.declarativeRemainder
      input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have notAtEnd : input.atEnd = false := by
      unfold State.atEnd
      exact decide_eq_false atEnd
    have rightBrace : isSymbol input .rightBrace = true := by
      simpa [notAtEnd] using boundary
    exact yulStatementRejects_of_rightBrace rightBrace

/-- Failure to advance is an end or missing-token statement boundary. -/
theorem yulStatementRejects_of_advance?_eq_none
    (input : State) (advanced : input.advance? = none) :
    DeclarativeGrammar.YulStatementRejects input.declarativeRemainder
      input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have inside : input.cursor < input.window.endIndex := by omega
    apply DeclarativeGrammar.YulStatementRejects.missingToken inside
    unfold State.advance? State.peek? at advanced
    simpa [State.declarativeRemainder, inside] using advanced

/-- A present non-boundary token continues statement recovery. -/
theorem no_yulStatementRejects_of_nonBoundary_token
    {input : State} {token : Token}
    (boundary : (input.atEnd || isSymbol input .rightBrace) = false)
    (found : input.peek? = some token) :
    ¬ DeclarativeGrammar.YulStatementRejects input.declarativeRemainder
      input.declarativeRemainder := by
  intro rejected
  have current := tokenAt_of_peek?_eq_some found
  cases rejected with
  | windowEnd atEnd =>
      change input.window.endIndex ≤ input.cursor at atEnd
      have inside := State.cursor_lt_endIndex_of_peek?_eq_some found
      omega
  | rightBrace rightBraceToken =>
      have present := isSymbol_eq_true_of_tokenAt .rightBrace rightBraceToken
      simp [present] at boundary
  | missingToken inside missing =>
      change input.tokens[input.cursor]? = none at missing
      rw [current.2] at missing
      contradiction

private theorem advance?_state_shape {input next : State} {token : Token}
    (advanced : input.advance? = some (token, next)) :
    input.peek? = some token ∧
      next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      exact ⟨rfl, rfl⟩

/-- Every successful executable statement-recovery scan follows the exact
boundary-prioritized declarative scan. -/
theorem recoverYulStatementAux_success_ordinary_sound (first : SourceSpan) :
    ∀ fuel last input statement output,
      recoverYulStatementAux first last fuel input = .ok statement output →
      DeclarativeGrammar.YulStatementRecoveryScanParses first last
        input.declarativeRemainder statement output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last input statement output result
      simp [recoverYulStatementAux] at result
  | succ fuel inductionHypothesis =>
      intro last input statement output result
      unfold recoverYulStatementAux at result
      by_cases boundary :
          (input.atEnd || isSymbol input .rightBrace) = true
      · simp only [boundary, if_true] at result
        unfold finishRecoveredYulStatement at result
        cases result
        exact .stop (yulStatementRejects_of_boundary input boundary)
      · have boundaryFalse :
            (input.atEnd || isSymbol input .rightBrace) = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            unfold finishRecoveredYulStatement at result
            cases result
            exact .stop
              (yulStatementRejects_of_advance?_eq_none input advanced)
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at result
            rcases advance?_state_shape advanced with ⟨found, nextEq⟩
            have tail := inductionHypothesis token.span next statement output
              result
            have current := tokenAt_of_peek?_eq_some found
            have continues := no_yulStatementRejects_of_nonBoundary_token
              boundaryFalse found
            rw [nextEq] at tail
            exact .next continues current tail

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.RecognizedYulStatementFallbackOutcomeProperties
/-!
Executable outcome bridges for recognized inline-Yul statement fallback.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every wrapper success follows the preferred ordinary relation or exact
preferred rejection followed by fallback ordinary success at the original
input. -/
theorem recognizedYulStatementOrFallback_success_ordinary_sound
    (primary fallback : Parser YulStmt)
    (primaryParses fallbackParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (primaryRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (primarySuccessSound : ∀ {input output : State} {value : YulStmt},
      primary input = .ok value output → primaryParses
        input.declarativeRemainder value output.declarativeRemainder)
    (primaryRejectSound : ∀ {input rejected : State} {failure : Failure},
      primary input = .reject failure rejected → primaryRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (fallbackSuccessSound : ∀ {input output : State} {value : YulStmt},
      fallback input = .ok value output → fallbackParses
        input.declarativeRemainder value output.declarativeRemainder)
    {input output : State} {value : YulStmt}
    (result : recognizedYulStatementOrFallback primary fallback input =
      .ok value output) :
    DeclarativeGrammar.TransactionalFallbackOrdinaryParses primaryParses
      primaryRejects fallbackParses input.declarativeRemainder value
        output.declarativeRemainder := by
  unfold recognizedYulStatementOrFallback at result
  cases primaryResult : primary input with
  | ok primaryValue afterPrimary =>
      simp only [primaryResult] at result
      cases result
      exact .primary (primarySuccessSound primaryResult)
  | invariant error => simp [primaryResult] at result
  | reject primaryFailure primaryRejected =>
      simp only [primaryResult] at result
      cases fallbackResult : fallback input with
      | invariant error => simp [fallbackResult] at result
      | reject fallbackFailure fallbackRejected =>
          simp [fallbackResult] at result
      | ok fallbackValue afterFallback =>
          simp only [fallbackResult] at result
          let reset : State := {
            afterFallback with diagnosticsRev := input.diagnosticsRev
          }
          have parsed :
              DeclarativeGrammar.TransactionalFallbackOrdinaryParses
                primaryParses primaryRejects fallbackParses
                input.declarativeRemainder fallbackValue
                  afterFallback.declarativeRemainder :=
            .fallback (primaryRejectSound primaryResult)
              (fallbackSuccessSound fallbackResult)
          change Reply.ok fallbackValue
            (reset.emit primaryFailure.toDiagnostic) = .ok value output
              at result
          cases result
          simpa [reset, State.emit, State.declarativeRemainder] using parsed

/-- A wrapper rejection decomposes into both branch rejections.  The returned
failure is exactly the preferred failure, and the returned state is the
original input state. -/
theorem recognizedYulStatementOrFallback_reject_decomposition
    (primary fallback : Parser YulStmt)
    {input rejected : State} {failure : Failure}
    (result : recognizedYulStatementOrFallback primary fallback input =
      .reject failure rejected) :
    ∃ primaryRejected fallbackFailure fallbackRejected,
      primary input = .reject failure primaryRejected ∧
        fallback input = .reject fallbackFailure fallbackRejected ∧
        rejected = input := by
  unfold recognizedYulStatementOrFallback at result
  cases primaryResult : primary input with
  | ok primaryValue afterPrimary => simp [primaryResult] at result
  | invariant error => simp [primaryResult] at result
  | reject primaryFailure primaryRejected =>
      simp only [primaryResult] at result
      cases fallbackResult : fallback input with
      | ok fallbackValue afterFallback => simp [fallbackResult] at result
      | invariant error => simp [fallbackResult] at result
      | reject fallbackFailure fallbackRejected =>
          simp only [fallbackResult] at result
          cases result
          exact ⟨primaryRejected, fallbackFailure, fallbackRejected,
            rfl, rfl, rfl⟩

/-- Every wrapper rejection follows the exact both-rejected relation and is
non-consuming even when either branch reported a different rejected state. -/
theorem recognizedYulStatementOrFallback_reject_sound
    (primary fallback : Parser YulStmt)
    (primaryRejects fallbackRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (primaryRejectSound : ∀ {input rejected : State} {failure : Failure},
      primary input = .reject failure rejected → primaryRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (fallbackRejectSound : ∀ {input rejected : State} {failure : Failure},
      fallback input = .reject failure rejected → fallbackRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : recognizedYulStatementOrFallback primary fallback input =
      .reject failure rejected) :
    DeclarativeGrammar.TransactionalFallbackRejects primaryRejects
      fallbackRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  rcases recognizedYulStatementOrFallback_reject_decomposition primary
      fallback result with
    ⟨primaryRejected, fallbackFailure, fallbackRejected, primaryResult,
      fallbackResult, rejectedEq⟩
  subst rejected
  exact .both (primaryRejectSound primaryResult)
    (fallbackRejectSound fallbackResult)

end Solcore.Syntax.Parser
end
