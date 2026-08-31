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

end Solcore.Syntax.Parser
