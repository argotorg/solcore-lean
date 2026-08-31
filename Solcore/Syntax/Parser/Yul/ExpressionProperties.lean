import Solcore.Syntax.Parser.Yul.LeafProperties

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

/-- Rejected source-level Yul meta syntax retains source provenance. -/
theorem rejectedMeta_validFor :
    rejectedMeta.ValidFor Located.ValidFor := by
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
        all_goals exact ⟨spanValid,
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
