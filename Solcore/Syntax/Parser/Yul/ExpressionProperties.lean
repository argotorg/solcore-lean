import Solcore.Syntax.Parser.Yul.LeafProperties
import Solcore.Syntax.YulValidity

/-! Compositional carrier and cursor contracts for one inline-Yul expression layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem presentYulCallArguments_validFor
    (nested : Parser YulExpr) (valueValid : SourceFile → YulExpr → Prop)
    (nestedValid : nested.ValidFor valueValid)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (do
      pure (some (← delimited .leftParen .rightParen true nested
        .yulExpression .yul))).ValidFor
          (Option.ValidFor (DelimitedList.ValidFor valueValid)) := by
  apply Parser.bind_validFor_of_value
    (delimited_validFor valueValid .leftParen .rightParen true nested
      .yulExpression .yul nestedValid nestedPreserves)
  intro arguments input inputValid argumentsValid
  exact ⟨argumentsValid, inputValid, rfl⟩

private theorem presentYulCallArguments_preservesTokensOnSuccess
    (nested : Parser YulExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (do
      pure (some (← delimited .leftParen .rightParen true nested
        .yulExpression .yul))) := by
  apply Parser.bind_preservesTokensOnSuccess
  · exact delimited_preservesTokensOnSuccess .leftParen .rightParen true
      nested .yulExpression .yul nestedPreserves
  · intro arguments
    exact Parser.pure_preservesTokensOnSuccess (some arguments)

private theorem presentYulCallArguments_preservesTokenWindow
    (nested : Parser YulExpr)
    (nestedShape : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (do
      pure (some (← delimited .leftParen .rightParen true nested
        .yulExpression .yul))) := by
  apply Parser.bind_preservesTokenWindow
  · exact delimited_preservesTokenWindow .leftParen .rightParen true nested
      .yulExpression .yul nestedShape
  · intro arguments
    exact Parser.pure_preservesTokenWindow (some arguments)

private theorem presentYulCallArguments_cursorMonotoneOnSuccess
    (nested : Parser YulExpr) :
    Parser.CursorMonotoneOnSuccess (do
      pure (some (← delimited .leftParen .rightParen true nested
        .yulExpression .yul))) := by
  apply Parser.bind_cursorMonotoneOnSuccess
  · exact delimited_cursorMonotoneOnSuccess .leftParen .rightParen true
      nested .yulExpression .yul
  · intro arguments
    exact Parser.pure_cursorMonotoneOnSuccess (some arguments)

/-- Optional Yul-call arguments preserve delimiter and element provenance. -/
theorem optionalYulCallArguments_validFor
    (nested : Parser YulExpr) (valueValid : SourceFile → YulExpr → Prop)
    (nestedValid : nested.ValidFor valueValid)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (optionalYulCallArguments nested).ValidFor
      (Option.ValidFor (DelimitedList.ValidFor valueValid)) := by
  intro input inputValid
  unfold optionalYulCallArguments
  split
  · exact Parser.orElse_validFor
      (presentYulCallArguments_validFor nested valueValid nestedValid
        nestedPreserves)
      (Parser.pure_validFor none _ (fun _ => trivial)) input inputValid
  · exact ⟨trivial, inputValid, rfl⟩

/-- Optional call arguments preserve every ordinary token window. -/
theorem optionalYulCallArguments_preservesTokenWindow
    (nested : Parser YulExpr)
    (nestedShape : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (optionalYulCallArguments nested) := by
  intro input
  unfold optionalYulCallArguments
  split
  · exact Parser.orElse_preservesTokenWindow
      (presentYulCallArguments_preservesTokenWindow nested nestedShape)
      (Parser.pure_preservesTokenWindow none) input
  · exact ⟨rfl, rfl⟩

/-- Optional Yul-call arguments preserve the immutable lexer token carrier. -/
theorem optionalYulCallArguments_preservesTokensOnSuccess
    (nested : Parser YulExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (optionalYulCallArguments nested) := by
  intro input arguments next result
  unfold optionalYulCallArguments at result
  split at result
  · exact (Parser.orElse_preservesTokensOnSuccess
      (presentYulCallArguments_preservesTokensOnSuccess nested
        nestedPreserves)
      (Parser.pure_preservesTokensOnSuccess none)) input arguments next result
  · cases result
    rfl

/-- Optional Yul-call arguments never rewind the parser cursor. -/
theorem optionalYulCallArguments_cursorMonotoneOnSuccess
    (nested : Parser YulExpr) :
    Parser.CursorMonotoneOnSuccess (optionalYulCallArguments nested) := by
  intro input arguments next result
  unfold optionalYulCallArguments at result
  split at result
  · exact (Parser.orElse_cursorMonotoneOnSuccess
      (presentYulCallArguments_cursorMonotoneOnSuccess nested)
      (Parser.pure_cursorMonotoneOnSuccess none)) input arguments next result
  · cases result
    exact Nat.le_refl _

/-- Present call arguments start at their opening parenthesis token. -/
theorem optionalYulCallArguments_some_startsAtCurrentTokenOnSuccess
    (nested : Parser YulExpr) {input next : State}
    {arguments : DelimitedList YulExpr}
    (result : optionalYulCallArguments nested input = .ok (some arguments) next) :
    ∃ token, input.peek? = some token ∧
      token.span.startByte = arguments.span.startByte := by
  unfold optionalYulCallArguments at result
  split at result
  · unfold orElse at result
    cases presentResult : (do
        pure (some (← delimited .leftParen .rightParen true nested
          .yulExpression .yul))) input with
    | invariant error => simp [presentResult] at result
    | reject failure rejected =>
        simp only [presentResult] at result
        change Reply.ok none input = Reply.ok (some arguments) next at result
        cases result
    | ok value afterPresent =>
        simp only [presentResult] at result
        cases result
        change (do
          pure (some (← delimited .leftParen .rightParen true nested
            .yulExpression .yul))) input = .ok (some arguments) next at presentResult
        cases argumentsResult : delimited .leftParen .rightParen true nested
            .yulExpression .yul input with
        | invariant error =>
            simp only [bind, argumentsResult] at presentResult
            contradiction
        | reject failure rejected =>
            simp only [bind, argumentsResult] at presentResult
            contradiction
        | ok parsed afterArguments =>
            simp only [bind, argumentsResult] at presentResult
            cases presentResult
            exact delimited_startsAtCurrentTokenOnSuccess .leftParen
              .rightParen true nested .yulExpression .yul input arguments
              next argumentsResult
  · cases result

/-- Rejected source-level Yul meta syntax produces a valid error expression. -/
theorem rejectedMeta_yulExpr_validFor :
    rejectedMeta.ValidFor YulExpr.ValidFor := by
  apply Parser.validFor_of_ok_reject
  · intro input inputValid expression next result
    unfold rejectedMeta at result
    cases found : input.peek? with
    | none =>
        simp only [found] at result
        unfold rejectAt at result
        contradiction
    | some token =>
        rcases token with ⟨span, kind⟩
        have spanValid := inputValid.peek?_span_validFor found
        have advancedValid :
            ({ input with cursor := input.cursor + 1 } : State).ValidFor := by
          apply inputValid.advance?_validFor
          unfold State.advance?
          rw [found]
          rfl
        cases kind <;> simp only [found] at result
        all_goals try { unfold rejectAt at result; contradiction }
        all_goals cases result
        all_goals exact ⟨YulExpr.ValidFor.error spanValid,
          advancedValid.emit_validFor _ spanValid, rfl⟩
  · intro input inputValid failure next result
    unfold rejectedMeta at result
    cases found : input.peek? with
    | none =>
        simp only [found] at result
        exact rejectAt_reject_validFor inputValid _ _ result
    | some token =>
        rcases token with ⟨span, kind⟩
        cases kind <;> simp only [found] at result
        all_goals try { exact rejectAt_reject_validFor inputValid _ _ result }
        all_goals contradiction

/-- Meta-syntax rejection preserves every ordinary token window. -/
theorem rejectedMeta_preservesTokenWindow :
    Parser.PreservesTokenWindow rejectedMeta := by
  intro input
  unfold rejectedMeta
  cases found : input.peek? with
  | none => exact rejectAt_preservesTokenWindow input _ _
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind
      all_goals try { exact rejectAt_preservesTokenWindow input _ _ }
      all_goals exact ⟨rfl, rfl⟩

/-- The outer range of rejected meta syntax remains source-valid. -/
theorem rejectedMeta_validFor :
    rejectedMeta.ValidFor Located.ValidFor :=
  rejectedMeta_yulExpr_validFor.mono (by
    intro file expression valid
    cases valid <;> assumption)

/-- Rejected source-level Yul meta syntax preserves the token carrier. -/
theorem rejectedMeta_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess rejectedMeta := by
  intro input expression next result
  unfold rejectedMeta at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      all_goals cases result
      all_goals rfl

/-- Rejected meta syntax starts at the diagnosed input token. -/
theorem rejectedMeta_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess rejectedMeta (·.span) := by
  intro input expression next result
  unfold rejectedMeta at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      all_goals cases result
      all_goals exact ⟨_, rfl, rfl⟩

/-- Rejected source-level Yul meta syntax advances by one token. -/
theorem rejectedMeta_cursor_lt_onSuccess {input next : State}
    {expression : YulExpr} (result : rejectedMeta input = .ok expression next) :
    input.cursor < next.cursor := by
  unfold rejectedMeta at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      all_goals cases result
      all_goals simp [State.emit]

/-- Rejected source-level Yul meta syntax never rewinds the parser cursor. -/
theorem rejectedMeta_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess rejectedMeta := by
  intro input expression next result
  exact Nat.le_of_lt (rejectedMeta_cursor_lt_onSuccess result)

/-- One recursive Yul-expression layer preserves all retained source ranges. -/
theorem yulExpressionCore_validFor
    (nested : Parser YulExpr)
    (nestedValid : nested.ValidFor YulExpr.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (yulExpressionCore nested).ValidFor YulExpr.ValidFor := by
  intro input inputValid
  unfold yulExpressionCore
  split
  · cases literalResult : yulLiteral input with
    | invariant error => simp only [Reply.ValidFor]
    | reject failure rejected =>
        have valid := yulLiteral_validFor input inputValid
        rw [literalResult] at valid
        simpa only [Reply.ValidFor] using valid
    | ok literal afterLiteral =>
        have valid := yulLiteral_validFor input inputValid
        rw [literalResult] at valid
        exact ⟨YulExpr.ValidFor.literal valid.1 valid.1,
          valid.2.1, valid.2.2⟩
  · split
    · cases nameResult : yulName input with
      | invariant error => simp only [Reply.ValidFor]
      | reject failure rejected =>
          have valid := yulName_validFor input inputValid
          rw [nameResult] at valid
          simpa only [Reply.ValidFor] using valid
      | ok name afterName =>
          have nameValid := yulName_validFor input inputValid
          rw [nameResult] at nameValid
          simp only
          cases argumentsResult : optionalYulCallArguments nested afterName with
          | invariant error => simp only [Reply.ValidFor]
          | reject failure rejected =>
              have valid := optionalYulCallArguments_validFor nested
                YulExpr.ValidFor nestedValid nestedPreserves afterName
                nameValid.2.1
              rw [argumentsResult] at valid
              exact valid.of_file_eq nameValid.2.2
          | ok arguments afterArguments =>
              have argumentsValid := optionalYulCallArguments_validFor nested
                YulExpr.ValidFor nestedValid nestedPreserves afterName
                nameValid.2.1
              rw [argumentsResult] at argumentsValid
              cases arguments with
              | none =>
                  exact ⟨YulExpr.ValidFor.identifier nameValid.1 nameValid.1,
                    argumentsValid.2.1,
                    argumentsValid.2.2.trans nameValid.2.2⟩
              | some arguments =>
                  have nameSpanValid : name.span.ValidFor input.file := by
                    simpa only [Located.ValidFor] using nameValid.1
                  have argumentsSpanValid :
                      arguments.span.ValidFor input.file := by
                    simpa only [Option.ValidFor, DelimitedList.ValidFor,
                      nameValid.2.2] using argumentsValid.1.1
                  have retainedValid : ∀ argument ∈ arguments.elements,
                      YulExpr.ValidFor input.file argument := by
                    intro argument member
                    simpa only [Option.ValidFor, DelimitedList.ValidFor,
                      nameValid.2.2] using argumentsValid.1.2 argument member
                  rcases yulName_ok_state_shape nameResult with
                    ⟨nameToken, nameFound, nameSpan, nameTokens, nameCursor⟩
                  rcases optionalYulCallArguments_some_startsAtCurrentTokenOnSuccess
                      nested argumentsResult with
                    ⟨openingToken, openingFound, openingStart⟩
                  have nameAt :=
                    State.getElem?_eq_some_of_peek?_eq_some nameFound
                  have openingAt :
                      input.tokens[afterName.cursor]? = some openingToken := by
                    have found :=
                      State.getElem?_eq_some_of_peek?_eq_some openingFound
                    simpa [nameTokens] using found
                  have nameEndBeforeArgumentsStart :
                      name.span.endByte ≤ arguments.span.startByte := by
                    have ordered :=
                      inputValid.token_end_le_token_start_of_getElem?_lt
                        nameAt openingAt (by rw [nameCursor]; simp)
                    simpa [nameSpan, openingStart] using ordered
                  have coverValid := SourceSpan.cover_validFor nameSpanValid
                    argumentsSpanValid (Nat.le_trans nameSpanValid.2.1
                      (Nat.le_trans nameEndBeforeArgumentsStart
                        argumentsSpanValid.2.1))
                  exact ⟨YulExpr.ValidFor.call coverValid nameSpanValid
                      argumentsSpanValid retainedValid,
                    argumentsValid.2.1,
                    argumentsValid.2.2.trans nameValid.2.2⟩
    · split <;> try { exact
          rejectedMeta_yulExpr_validFor input inputValid }
      unfold rejectAt Reply.ValidFor
      exact ⟨inputValid.currentSpan_validFor, inputValid, rfl⟩

/-- A successful Yul-expression layer starts at its leading token. -/
theorem yulExpressionCore_startsAtCurrentTokenOnSuccess
    (nested : Parser YulExpr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (yulExpressionCore nested) (·.span) := by
  intro input expression next result
  unfold yulExpressionCore at result
  split at result
  · cases literalResult : yulLiteral input with
    | invariant error => simp [literalResult] at result
    | reject failure rejected => simp [literalResult] at result
    | ok literal afterLiteral =>
        simp only [literalResult] at result
        have starts := yulLiteral_startsAtCurrentTokenOnSuccess input literal
          afterLiteral literalResult
        cases result
        exact starts
  · split at result
    · cases nameResult : yulName input with
      | invariant error => simp [nameResult] at result
      | reject failure rejected => simp [nameResult] at result
      | ok name afterName =>
          simp only [nameResult] at result
          cases argumentsResult : optionalYulCallArguments nested afterName with
          | invariant error => simp [argumentsResult] at result
          | reject failure rejected => simp [argumentsResult] at result
          | ok arguments afterArguments =>
              simp only [argumentsResult] at result
              rcases yulName_startsAtCurrentTokenOnSuccess input name afterName
                  nameResult with ⟨token, found, start⟩
              cases arguments <;> cases result
              · exact ⟨token, found, start⟩
              · exact ⟨token, found, start⟩
    · split at result <;> try { exact
          rejectedMeta_startsAtCurrentTokenOnSuccess input expression next result }
      unfold rejectAt at result
      contradiction

/-- One Yul-expression layer preserves tokens when its recursive parser does. -/
theorem yulExpressionCore_preservesTokensOnSuccess
    (nested : Parser YulExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (yulExpressionCore nested) := by
  intro input expression next result
  unfold yulExpressionCore at result
  split at result
  · cases literalResult : yulLiteral input with
    | ok literal afterLiteral =>
        simp only [literalResult] at result
        have preserved := yulLiteral_preservesTokensOnSuccess input literal
          afterLiteral literalResult
        cases result
        exact preserved
    | reject failure rejected => simp [literalResult] at result
    | invariant error => simp [literalResult] at result
  · split at result
    · cases nameResult : yulName input with
      | ok name afterName =>
          simp only [nameResult] at result
          cases argumentsResult : optionalYulCallArguments nested afterName with
          | ok arguments afterArguments =>
              simp only [argumentsResult] at result
              have argumentsPreserved :=
                optionalYulCallArguments_preservesTokensOnSuccess nested
                  nestedPreserves afterName arguments afterArguments
                    argumentsResult
              have namePreserved := yulName_preservesTokensOnSuccess input name
                afterName nameResult
              cases arguments <;> cases result
              all_goals exact argumentsPreserved.trans namePreserved
          | reject failure rejected => simp [argumentsResult] at result
          | invariant error => simp [argumentsResult] at result
      | reject failure rejected => simp [nameResult] at result
      | invariant error => simp [nameResult] at result
    · split at result <;> try { exact
          rejectedMeta_preservesTokensOnSuccess input expression next result }
      unfold rejectAt at result
      contradiction

/-- One Yul-expression layer preserves every ordinary token window. -/
theorem yulExpressionCore_preservesTokenWindow
    (nested : Parser YulExpr)
    (nestedShape : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (yulExpressionCore nested) := by
  intro input
  unfold yulExpressionCore
  split
  · have literalShape := yulLiteral_preservesTokenWindow input
    cases literalResult : yulLiteral input with
    | ok literal next => rw [literalResult] at literalShape; exact literalShape
    | reject failure next =>
        rw [literalResult] at literalShape
        exact literalShape
    | invariant error => trivial
  · split
    · have nameShape := yulName_preservesTokenWindow input
      cases nameResult : yulName input with
      | ok name afterName =>
          rw [nameResult] at nameShape
          have argumentsShape :=
            optionalYulCallArguments_preservesTokenWindow nested nestedShape
              afterName
          cases argumentsResult : optionalYulCallArguments nested afterName with
          | ok arguments next =>
              rw [argumentsResult] at argumentsShape
              cases arguments <;>
                simp only [argumentsResult, Reply.PreservesTokenWindow] <;>
                exact argumentsShape.trans nameShape
          | reject failure next =>
              rw [argumentsResult] at argumentsShape
              simp only [argumentsResult, Reply.PreservesTokenWindow]
              exact argumentsShape.trans nameShape
          | invariant error =>
              simp only [argumentsResult, Reply.PreservesTokenWindow]
      | reject failure next =>
          rw [nameResult] at nameShape
          exact nameShape
      | invariant error => trivial
    · split
      all_goals try { exact rejectedMeta_preservesTokenWindow input }
      exact rejectAt_preservesTokenWindow input _ _

/-- Core Yul rejection retains the caller's immutable token window. -/
theorem yulExpressionCore_reject_preservesTokenWindow
    (nested : Parser YulExpr)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input failedState : State} {failure : Failure}
    (result : yulExpressionCore nested input =
      .reject failure failedState) :
    failedState.tokens = input.tokens ∧
      failedState.window = input.window := by
  have preserved := yulExpressionCore_preservesTokenWindow nested nestedShape input
  rw [result] at preserved
  exact preserved

/-- Every successful Yul-expression layer consumes at least its leading token. -/
theorem yulExpressionCore_cursor_lt_onSuccess
    (nested : Parser YulExpr) {input next : State} {expression : YulExpr}
    (result : yulExpressionCore nested input = .ok expression next) :
    input.cursor < next.cursor := by
  unfold yulExpressionCore at result
  split at result
  · cases literalResult : yulLiteral input with
    | ok literal afterLiteral =>
        simp only [literalResult] at result
        have shape := yulLiteral_ok_state_shape literalResult
        cases result
        rw [shape]
        simp
    | reject failure rejected => simp [literalResult] at result
    | invariant error => simp [literalResult] at result
  · split at result
    · cases nameResult : yulName input with
      | ok name afterName =>
          simp only [nameResult] at result
          cases argumentsResult : optionalYulCallArguments nested afterName with
          | ok arguments afterArguments =>
              simp only [argumentsResult] at result
              have nameProgress : input.cursor < afterName.cursor := by
                rw [(yulName_ok_state_shape nameResult).choose_spec.2.2.2]
                simp
              have argumentsMonotone :=
                optionalYulCallArguments_cursorMonotoneOnSuccess nested
                  afterName arguments afterArguments argumentsResult
              cases arguments <;> cases result
              all_goals exact Nat.lt_of_lt_of_le nameProgress argumentsMonotone
          | reject failure rejected => simp [argumentsResult] at result
          | invariant error => simp [argumentsResult] at result
      | reject failure rejected => simp [nameResult] at result
      | invariant error => simp [nameResult] at result
    · split at result <;> try { exact
          rejectedMeta_cursor_lt_onSuccess result }
      unfold rejectAt at result
      contradiction

/-- One Yul-expression layer never rewinds the parser cursor. -/
theorem yulExpressionCore_cursorMonotoneOnSuccess
    (nested : Parser YulExpr) :
    Parser.CursorMonotoneOnSuccess (yulExpressionCore nested) := by
  intro input expression next result
  exact Nat.le_of_lt (yulExpressionCore_cursor_lt_onSuccess nested result)

namespace YulExpressionInternals

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

/-- Finishing Yul-expression recovery retains a source-valid error range. -/
theorem finishRecovered_validFor (first last : SourceSpan) (state : State)
    (stateValid : state.ValidFor) (firstValid : first.ValidFor state.file)
    (lastValid : last.ValidFor state.file)
    (ordered : first.startByte ≤ last.endByte) :
    (finishRecovered first last state).ValidFor state YulExpr.ValidFor := by
  have spanValid := SourceSpan.cover_validFor firstValid lastValid ordered
  unfold finishRecovered Reply.ValidFor
  exact ⟨YulExpr.ValidFor.error spanValid,
    stateValid.emit_validFor _ spanValid, rfl⟩

/--
Recovery preserves recursive expression provenance.  The final hypotheses
record the already-consumed token whose span is `last`; they make the source
ordering needed by the next recovery step explicit.
-/
theorem recoverAux_validFor (first : SourceSpan) :
    ∀ fuel last state lastIndex lastToken,
      state.ValidFor → first.ValidFor state.file →
      last.ValidFor state.file → first.startByte ≤ last.endByte →
      state.tokens[lastIndex]? = some lastToken → lastToken.span = last →
      lastIndex < state.cursor →
      (recoverAux first last fuel state).ValidFor state YulExpr.ValidFor := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro last state lastIndex lastToken stateValid firstValid lastValid
        ordered lastFound lastSpan lastBefore
      unfold recoverAux
      split
      · exact finishRecovered_validFor first last state stateValid firstValid
          lastValid ordered
      · cases advanced : state.advance? with
        | some pair =>
            rcases pair with ⟨token, next⟩
            have nextValid := stateValid.advance?_validFor advanced
            unfold State.advance? at advanced
            cases found : state.peek? with
            | none => simp [found] at advanced
            | some current =>
                simp only [found, Option.map_some] at advanced
                cases advanced
                have tokenValid := stateValid.peek?_span_validFor found
                have currentFound :=
                  State.getElem?_eq_some_of_peek?_eq_some found
                have lastBeforeCurrent :=
                  stateValid.token_end_le_token_start_of_getElem?_lt
                    lastFound currentFound lastBefore
                have recursive := inductionHypothesis token.span
                  { state with cursor := state.cursor + 1 } state.cursor token
                  nextValid (by simpa using firstValid)
                  (by simpa using tokenValid)
                  (Nat.le_trans ordered (Nat.le_trans
                    (by simpa [lastSpan] using lastBeforeCurrent)
                    tokenValid.2.1))
                  currentFound rfl (by simp)
                exact recursive.of_file_eq rfl
        | none =>
            exact finishRecovered_validFor first last state stateValid
              firstValid lastValid ordered

/-- Successful recovery preserves tokens, cursor order, and its first byte. -/
theorem recoverAux_ok_state_shape (first : SourceSpan) :
    ∀ fuel last input expression next,
      recoverAux first last fuel input = .ok expression next →
      next.tokens = input.tokens ∧ input.cursor ≤ next.cursor ∧
        expression.span.startByte = first.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro last input expression next result
      unfold recoverAux at result
      split at result
      · unfold finishRecovered at result
        cases result
        exact ⟨rfl, Nat.le_refl _, rfl⟩
      · cases advanced : input.advance? with
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            have recursive := inductionHypothesis token.span afterToken
              expression next result
            unfold State.advance? at advanced
            cases found : input.peek? with
            | none => simp [found] at advanced
            | some current =>
                simp only [found, Option.map_some] at advanced
                cases advanced
                exact ⟨recursive.1,
                  Nat.le_trans (Nat.le_add_right input.cursor 1)
                    recursive.2.1,
                  recursive.2.2⟩
        | none =>
            simp only [advanced] at result
            unfold finishRecovered at result
            cases result
            exact ⟨rfl, Nat.le_refl _, rfl⟩

/-- Yul recovery preserves the immutable lexer token carrier on success. -/
theorem recoverAux_preservesTokensOnSuccess (first last : SourceSpan)
    (fuel : Nat) :
    Parser.PreservesTokensOnSuccess (recoverAux first last fuel) := by
  intro input expression next result
  exact (recoverAux_ok_state_shape first fuel last input expression next
    result).1

/-- Yul recovery never rewinds the cursor on success. -/
theorem recoverAux_cursorMonotoneOnSuccess (first last : SourceSpan)
    (fuel : Nat) :
    Parser.CursorMonotoneOnSuccess (recoverAux first last fuel) := by
  intro input expression next result
  exact (recoverAux_ok_state_shape first fuel last input expression next
    result).2.1

/-- Yul recovery preserves the complete immutable token window. -/
theorem recoverAux_preservesTokenWindow (first last : SourceSpan)
    (fuel : Nat) :
    Parser.PreservesTokenWindow (recoverAux first last fuel) := by
  intro input
  induction fuel generalizing last input with
  | zero => trivial
  | succ fuel inductionHypothesis =>
      unfold recoverAux
      split
      · unfold finishRecovered Reply.PreservesTokenWindow
        exact ⟨rfl, rfl⟩
      · cases advanced : input.advance? with
        | none =>
            unfold finishRecovered Reply.PreservesTokenWindow
            exact ⟨rfl, rfl⟩
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            have recursive := inductionHypothesis token.span afterToken
            have advanceShape := advance?_state_shape advanced
            exact recursive.trans (by
              simp [advanceShape.2])

/-- One recovering Yul-expression layer preserves recursive provenance. -/
theorem layer_validFor (nested : Parser YulExpr)
    (nestedValid : nested.ValidFor YulExpr.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested)
    (coreRejectShape : ∀ input failure failedState,
      yulExpressionCore nested input = .reject failure failedState →
      failedState.tokens = input.tokens ∧ failedState.window = input.window) :
    (layer nested).ValidFor YulExpr.ValidFor := by
  intro input inputValid
  unfold layer
  cases coreResult : yulExpressionCore nested input with
  | ok expression next =>
      have valid := yulExpressionCore_validFor nested nestedValid
        nestedPreserves input inputValid
      rw [coreResult] at valid
      exact valid
  | invariant error => trivial
  | reject failure failedState =>
      have coreValid := yulExpressionCore_validFor nested nestedValid
        nestedPreserves input inputValid
      rw [coreResult] at coreValid
      have rejectedShape := coreRejectShape input failure failedState coreResult
      let rewound : State := { failedState with cursor := input.cursor }
      have rewoundValid : rewound.ValidFor := {
        tokens := coreValid.2.1.tokens
        cursor_le_endIndex := by
          simpa [rewound, rejectedShape.2] using inputValid.cursor_le_endIndex
        endIndex_le_size := coreValid.2.1.endIndex_le_size
        endByte_le_source := coreValid.2.1.endByte_le_source
        endByte_boundary := coreValid.2.1.endByte_boundary
        diagnosticsRev := coreValid.2.1.diagnosticsRev
      }
      have rewoundFile : rewound.file = input.file := by
        simpa [rewound] using coreValid.2.2
      have failureValid : failure.span.ValidFor rewound.file := by
        simpa [rewound, coreValid.2.2] using coreValid.1
      change (if isBoundary rewound then Reply.reject failure rewound else
        match rewound.advance? with
        | some (token, next) =>
            recoverAux token.span token.span (next.remainingCount + 1)
              (next.emit failure.toDiagnostic)
        | none => Reply.reject failure rewound).ValidFor input YulExpr.ValidFor
      split
      · exact ⟨coreValid.1, rewoundValid, rewoundFile⟩
      · cases advanced : rewound.advance? with
        | none => exact ⟨coreValid.1, rewoundValid, rewoundFile⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            have advanceShape := advance?_state_shape advanced
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
            have recovered := recoverAux_validFor token.span
              (next.remainingCount + 1) token.span
              (next.emit failure.toDiagnostic) rewound.cursor token emittedValid
              (by simpa [State.emit] using tokenValid)
              (by simpa [State.emit] using tokenValid)
              tokenValid.2.1 currentFound rfl (by
                simp [advanceShape.2, State.emit])
            exact recovered.of_file_eq (by
              simpa [advanceShape.2, State.emit] using rewoundFile)

/-- A recovering Yul layer preserves tokens when rejection does as well. -/
theorem layer_preservesTokensOnSuccess (nested : Parser YulExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested)
    (coreRejectPreserves : ∀ input failure failedState,
      yulExpressionCore nested input = .reject failure failedState →
      failedState.tokens = input.tokens) :
    Parser.PreservesTokensOnSuccess (layer nested) := by
  intro input expression next result
  unfold layer at result
  cases coreResult : yulExpressionCore nested input with
  | ok value afterCore =>
      simp only [coreResult] at result
      have preserved := yulExpressionCore_preservesTokensOnSuccess nested
        nestedPreserves input value afterCore coreResult
      cases result
      exact preserved
  | invariant error => simp [coreResult] at result
  | reject failure failedState =>
      simp only [coreResult] at result
      let rewound : State := { failedState with cursor := input.cursor }
      change (if isBoundary rewound then Reply.reject failure rewound else
        match rewound.advance? with
        | some (token, afterToken) =>
            recoverAux token.span token.span (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic)
        | none => Reply.reject failure rewound) = .ok expression next at result
      split at result
      · contradiction
      · cases advanced : rewound.advance? with
        | none => simp [advanced] at result
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            have recovered := recoverAux_ok_state_shape token.span
              (afterToken.remainingCount + 1) token.span
              (afterToken.emit failure.toDiagnostic) expression next result
            have advanceShape := advance?_state_shape advanced
            exact recovered.1.trans (by
              simpa [advanceShape.2, State.emit, rewound] using
                coreRejectPreserves input failure failedState coreResult)

/-- A recovering Yul layer preserves every ordinary token window. -/
theorem layer_preservesTokenWindow (nested : Parser YulExpr)
    (nestedShape : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (layer nested) := by
  intro input
  unfold layer
  cases coreResult : yulExpressionCore nested input with
  | invariant error => trivial
  | ok expression next =>
      have coreShape := yulExpressionCore_preservesTokenWindow nested
        nestedShape input
      rw [coreResult] at coreShape
      exact coreShape
  | reject failure failedState =>
      have coreShape := yulExpressionCore_preservesTokenWindow nested
        nestedShape input
      rw [coreResult] at coreShape
      let rewound : State := { failedState with cursor := input.cursor }
      have failedShape : failedState.tokens = input.tokens ∧
          failedState.window = input.window := by
        simpa only [Reply.PreservesTokenWindow] using coreShape
      have rewoundShape : rewound.tokens = input.tokens ∧
          rewound.window = input.window := by
        simpa [rewound] using failedShape
      change (if isBoundary rewound then Reply.reject failure rewound else
        match rewound.advance? with
        | some (token, afterToken) =>
            recoverAux token.span token.span (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic)
        | none => Reply.reject failure rewound).PreservesTokenWindow input
      split
      · exact rewoundShape
      · cases advanced : rewound.advance? with
        | none => exact rewoundShape
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            have recovered := recoverAux_preservesTokenWindow token.span
              token.span (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic)
            have advanceShape := advance?_state_shape advanced
            exact recovered.trans (by
              simpa [State.emit, advanceShape.2] using rewoundShape)

/-- A recovering Yul layer never rewinds its caller's cursor. -/
theorem layer_cursorMonotoneOnSuccess (nested : Parser YulExpr) :
    Parser.CursorMonotoneOnSuccess (layer nested) := by
  intro input expression next result
  unfold layer at result
  cases coreResult : yulExpressionCore nested input with
  | invariant error => simp [coreResult] at result
  | ok value afterCore =>
      simp only [coreResult] at result
      have monotone := yulExpressionCore_cursorMonotoneOnSuccess nested
        input value afterCore coreResult
      cases result
      exact monotone
  | reject failure failedState =>
      simp only [coreResult] at result
      let rewound : State := { failedState with cursor := input.cursor }
      change (if isBoundary rewound then Reply.reject failure rewound else
        match rewound.advance? with
        | some (token, afterToken) =>
            recoverAux token.span token.span (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic)
        | none => Reply.reject failure rewound) = .ok expression next at result
      split at result
      · contradiction
      · cases advanced : rewound.advance? with
        | none => simp [advanced] at result
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            have recovered := recoverAux_cursorMonotoneOnSuccess token.span
              token.span (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic) expression next result
            have advanceShape := advance?_state_shape advanced
            exact Nat.le_trans (by simp [advanceShape.2, State.emit, rewound])
              recovered

/-- A successful recovering layer starts at its caller's current token. -/
theorem layer_startsAtCurrentTokenOnSuccess (nested : Parser YulExpr)
    (nestedShape : Parser.PreservesTokenWindow nested) :
    Parser.StartsAtCurrentTokenOnSuccess (layer nested) (·.span) := by
  intro input expression next result
  unfold layer at result
  cases coreResult : yulExpressionCore nested input with
  | invariant error => simp [coreResult] at result
  | ok value afterCore =>
      simp only [coreResult] at result
      have starts := yulExpressionCore_startsAtCurrentTokenOnSuccess nested
        input value afterCore coreResult
      cases result
      simpa using starts
  | reject failure failedState =>
      simp only [coreResult] at result
      have coreShape := yulExpressionCore_reject_preservesTokenWindow nested
        nestedShape coreResult
      let rewound : State := { failedState with cursor := input.cursor }
      change (if isBoundary rewound then Reply.reject failure rewound else
        match rewound.advance? with
        | some (token, afterToken) =>
            recoverAux token.span token.span (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic)
        | none => Reply.reject failure rewound) = .ok expression next at result
      split at result
      · contradiction
      · cases advanced : rewound.advance? with
        | none => simp [advanced] at result
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            have advanceShape := advance?_state_shape advanced
            have found : input.peek? = some token := by
              have rewoundFound := advanceShape.1
              unfold State.peek? at rewoundFound ⊢
              simpa [rewound, coreShape.1, coreShape.2] using rewoundFound
            have recovered := recoverAux_ok_state_shape token.span
              (afterToken.remainingCount + 1) token.span
              (afterToken.emit failure.toDiagnostic) expression next result
            exact ⟨token, found, recovered.2.2.symm⟩

/-- Every fuel-bounded recursive Yul parser preserves token windows. -/
theorem withFuel_preservesTokenWindow : ∀ fuel,
    Parser.PreservesTokenWindow (withFuel fuel) := by
  intro fuel
  induction fuel with
  | zero => intro input; trivial
  | succ fuel inductionHypothesis =>
      exact layer_preservesTokenWindow (withFuel fuel) inductionHypothesis

/-- Every fuel-bounded recursive Yul parser preserves source provenance. -/
theorem withFuel_validFor : ∀ fuel,
    (withFuel fuel).ValidFor YulExpr.ValidFor := by
  intro fuel
  induction fuel with
  | zero =>
      intro input inputValid
      change True
      trivial
  | succ fuel inductionHypothesis =>
      have nestedShape := withFuel_preservesTokenWindow fuel
      exact layer_validFor (withFuel fuel) inductionHypothesis
        nestedShape.preservesTokensOnSuccess (by
          intro input failure failedState result
          exact yulExpressionCore_reject_preservesTokenWindow
            (withFuel fuel) nestedShape result)

/-- Every fuel-bounded recursive Yul parser preserves its token carrier. -/
theorem withFuel_preservesTokensOnSuccess (fuel : Nat) :
    Parser.PreservesTokensOnSuccess (withFuel fuel) :=
  (withFuel_preservesTokenWindow fuel).preservesTokensOnSuccess

/-- Every fuel-bounded recursive Yul parser keeps cursor order. -/
theorem withFuel_cursorMonotoneOnSuccess : ∀ fuel,
    Parser.CursorMonotoneOnSuccess (withFuel fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro input expression next result
      unfold withFuel at result
      contradiction
  | succ fuel inductionHypothesis =>
      exact layer_cursorMonotoneOnSuccess (withFuel fuel)

/-- Every successful fuel-bounded Yul parser starts at its input token. -/
theorem withFuel_startsAtCurrentTokenOnSuccess : ∀ fuel,
    Parser.StartsAtCurrentTokenOnSuccess (withFuel fuel) (·.span) := by
  intro fuel
  induction fuel with
  | zero =>
      intro input expression next result
      unfold withFuel at result
      contradiction
  | succ fuel inductionHypothesis =>
      exact layer_startsAtCurrentTokenOnSuccess (withFuel fuel)
        (withFuel_preservesTokenWindow fuel)

end YulExpressionInternals

/-- The public recursive Yul parser preserves all retained source ranges. -/
theorem yulExpression_validFor :
    yulExpression.ValidFor YulExpr.ValidFor := by
  intro input inputValid
  unfold yulExpression
  exact YulExpressionInternals.withFuel_validFor
    (input.remainingCount + 1) input inputValid

/-- The public recursive Yul parser preserves every ordinary token window. -/
theorem yulExpression_preservesTokenWindow :
    Parser.PreservesTokenWindow yulExpression := by
  intro input
  unfold yulExpression
  exact YulExpressionInternals.withFuel_preservesTokenWindow
    (input.remainingCount + 1) input

/-- The public recursive Yul parser preserves its immutable token carrier. -/
theorem yulExpression_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess yulExpression :=
  yulExpression_preservesTokenWindow.preservesTokensOnSuccess

/-- The public recursive Yul parser never rewinds its cursor. -/
theorem yulExpression_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulExpression := by
  intro input expression next result
  unfold yulExpression at result
  exact YulExpressionInternals.withFuel_cursorMonotoneOnSuccess
    (input.remainingCount + 1) input expression next result

/-- A successful public Yul expression starts at its current input token. -/
theorem yulExpression_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess yulExpression (·.span) := by
  intro input expression next result
  unfold yulExpression at result
  exact YulExpressionInternals.withFuel_startsAtCurrentTokenOnSuccess
    (input.remainingCount + 1) input expression next result

end Solcore.Syntax.Parser
