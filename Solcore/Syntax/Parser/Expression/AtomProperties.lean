import Solcore.Syntax.Parser.Expression.Atom
import Solcore.Syntax.Parser.LiteralProperties
import Solcore.Syntax.ExpressionValidity

/-! Provenance and state contracts for canonical Core expression atoms. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ExpressionAtomInternals

private theorem atomBind_ok_components {alpha beta : Type}
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

/-- Expression names retain the ordinary or Boolean builtin token range. -/
theorem expressionName_validFor :
    expressionName.ValidFor Located.ValidFor := by
  intro input inputValid
  unfold expressionName
  split
  · exact booleanIdentifier_validFor input inputValid
  · exact identifier_validFor .expression input inputValid

/-- Expression-name parsing preserves every ordinary token window. -/
theorem expressionName_preservesTokenWindow :
    Parser.PreservesTokenWindow expressionName := by
  intro input
  unfold expressionName
  split
  · exact booleanIdentifier_preservesTokenWindow input
  · exact identifier_preservesTokenWindow .expression input

theorem expressionName_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess expressionName :=
  expressionName_preservesTokenWindow.preservesTokensOnSuccess

/-- A successful expression name consumes exactly its current token. -/
theorem expressionName_ok_state_shape {input next : State}
    {name : Identifier} (parsed : expressionName input = .ok name next) :
    ∃ token, input.peek? = some token ∧ token.span = name.span ∧
      next.tokens = input.tokens ∧ next.cursor = input.cursor + 1 := by
  unfold expressionName at parsed
  split at parsed
  · unfold booleanIdentifier at parsed
    cases found : input.peek? with
    | none => simp [found, rejectAt] at parsed
    | some token =>
        rcases token with ⟨span, kind⟩
        cases kind <;> simp only [found] at parsed
        all_goals try { unfold rejectAt at parsed; contradiction }
        case keyword keyword =>
          cases keyword <;> simp only at parsed
          all_goals try { unfold rejectAt at parsed; contradiction }
          all_goals cases parsed
          all_goals exact ⟨_, rfl, rfl, rfl, rfl⟩
  · exact identifier_ok_state_shape .expression parsed

/-- Successful expression-name parsing never rewinds the cursor. -/
theorem expressionName_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess expressionName := by
  intro input name next parsed
  unfold expressionName at parsed
  split at parsed
  · exact booleanIdentifier_cursorMonotoneOnSuccess
      input name next parsed
  · exact identifier_cursorMonotoneOnSuccess .expression
      input name next parsed

theorem expressionName_cursor_lt_onSuccess {input next : State}
    {name : Identifier} (parsed : expressionName input = .ok name next) :
    input.cursor < next.cursor := by
  rw [(expressionName_ok_state_shape parsed).choose_spec.2.2.2]
  simp

/-- An expression name starts at its ordinary or Boolean name token. -/
theorem expressionName_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess expressionName (·.span) := by
  intro input name next parsed
  unfold expressionName at parsed
  split at parsed
  · exact booleanIdentifier_startsAtCurrentTokenOnSuccess
      input name next parsed
  · rcases identifier_ok_state_shape .expression parsed with
      ⟨token, found, span, _tokens, _cursor⟩
    exact ⟨token, found, congrArg SourceSpan.startByte span⟩

/-- Literal-expression parsing retains both equal literal ranges. -/
theorem literalExpression_validFor
    (statementValid : SourceFile → Statement → Prop) :
    literalExpression.ValidFor (Expr.ValidFor statementValid) := by
  unfold literalExpression
  apply Parser.bind_validFor_of_value coreLiteral_validFor
  intro literal input inputValid literalValid
  exact ⟨Expr.ValidFor.literal literalValid literalValid, inputValid, rfl⟩

/-- Literal expressions preserve every ordinary token window. -/
theorem literalExpression_preservesTokenWindow :
    Parser.PreservesTokenWindow literalExpression := by
  unfold literalExpression
  apply Parser.bind_preservesTokenWindow coreLiteral_preservesTokenWindow
  intro literal
  exact Parser.pure_preservesTokenWindow _

theorem literalExpression_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess literalExpression :=
  literalExpression_preservesTokenWindow.preservesTokensOnSuccess

/-- Literal-expression parsing never rewinds the cursor. -/
theorem literalExpression_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess literalExpression := by
  unfold literalExpression
  apply Parser.bind_cursorMonotoneOnSuccess
    coreLiteral_cursorMonotoneOnSuccess
  intro literal
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A literal expression starts at its literal token. -/
theorem literalExpression_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess literalExpression (·.span) := by
  unfold literalExpression
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    coreLiteral_startsAtCurrentTokenOnSuccess
  intro literal input value final parsed
  cases parsed
  rfl

/-- Identifier-expression parsing retains both equal name ranges. -/
theorem identifierExpression_validFor
    (statementValid : SourceFile → Statement → Prop) :
    identifierExpression.ValidFor (Expr.ValidFor statementValid) := by
  unfold identifierExpression
  apply Parser.bind_validFor_of_value expressionName_validFor
  intro name input inputValid nameValid
  exact ⟨Expr.ValidFor.identifier nameValid nameValid, inputValid, rfl⟩

/-- Identifier expressions preserve every ordinary token window. -/
theorem identifierExpression_preservesTokenWindow :
    Parser.PreservesTokenWindow identifierExpression := by
  unfold identifierExpression
  apply Parser.bind_preservesTokenWindow expressionName_preservesTokenWindow
  intro name
  exact Parser.pure_preservesTokenWindow _

theorem identifierExpression_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess identifierExpression :=
  identifierExpression_preservesTokenWindow.preservesTokensOnSuccess

/-- Identifier-expression parsing never rewinds the cursor. -/
theorem identifierExpression_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess identifierExpression := by
  unfold identifierExpression
  apply Parser.bind_cursorMonotoneOnSuccess
    expressionName_cursorMonotoneOnSuccess
  intro name
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- An identifier expression starts at its name token. -/
theorem identifierExpression_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess identifierExpression (·.span) := by
  unfold identifierExpression
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    expressionName_startsAtCurrentTokenOnSuccess
  intro name input value final parsed
  cases parsed
  rfl

/-- Proxy expressions retain their marker, inner type, and outer cover. -/
theorem proxyExpression_validFor
    (statementValid : SourceFile → Statement → Prop) :
    proxyExpression.ValidFor (Expr.ValidFor statementValid) := by
  have weak : proxyExpression.ValidFor (fun _ _ => True) := by
    unfold proxyExpression
    apply Parser.bind_validFor (symbol_validFor .at .expression)
    intro marker
    apply Parser.bind_validFor typeExpr_validFor
    intro type
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : proxyExpression input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok expression final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold proxyExpression at stages
      rcases atomBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases atomBind_ok_components rest with
        ⟨type, afterType, typeResult, finished⟩
      have markerContract := symbol_validFor .at .expression input inputValid
      rw [markerResult] at markerContract
      have typeContract := typeExpr_validFor afterMarker markerContract.2.1
      rw [typeResult] at typeContract
      have markerSpanValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerContract.1
      have typeValidInput : TypeExpr.ValidFor input.file type := by
        simpa [markerContract.2.2] using typeContract.1
      rcases typeExpr_startsAtCurrentTokenOnSuccess
          afterMarker type afterType typeResult with
        ⟨typeToken, typeFound, typeStart⟩
      have markerShape :=
        symbol_ok_state_shape .at .expression markerResult
      have advanced : input.advance? = some (marker, afterMarker) := by
        unfold State.advance?
        rw [markerShape.1, markerShape.2]
        rfl
      have markerBeforeType :
          marker.span.endByte ≤ type.span.startByte := by
        rw [← typeStart]
        exact inputValid.consumed_end_le_peek_start_after_advance
          advanced typeFound
      have outerValid :
          (SourceSpan.cover marker.span type.span).ValidFor input.file := by
        apply SourceSpan.cover_validFor markerSpanValid
          typeValidInput.span_valid
        exact Nat.le_trans markerSpanValid.2.1
          (Nat.le_trans markerBeforeType typeValidInput.span_valid.2.1)
      cases finished
      exact ⟨Expr.ValidFor.proxy outerValid markerSpanValid typeValidInput,
        weakResult.2.1, weakResult.2.2⟩

/-- Proxy-expression parsing preserves every ordinary token window. -/
theorem proxyExpression_preservesTokenWindow :
    Parser.PreservesTokenWindow proxyExpression := by
  unfold proxyExpression
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .at .expression)
  intro marker
  apply Parser.bind_preservesTokenWindow typeExpr_preservesTokenWindow
  intro type
  exact Parser.pure_preservesTokenWindow _

theorem proxyExpression_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess proxyExpression :=
  proxyExpression_preservesTokenWindow.preservesTokensOnSuccess

/-- Successful proxy-expression parsing never rewinds the cursor. -/
theorem proxyExpression_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess proxyExpression := by
  unfold proxyExpression
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .at .expression)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    typeExpr_cursorMonotoneOnSuccess
  intro type
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A proxy expression starts at its current `@` token. -/
theorem proxyExpression_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess proxyExpression (·.span) := by
  unfold proxyExpression
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (symbol_startsAtCurrentTokenOnSuccess .at .expression)
  intro marker input expression final parsed
  rcases atomBind_ok_components parsed with
    ⟨type, afterType, typeResult, finished⟩
  cases finished
  rfl

end ExpressionAtomInternals
end Solcore.Syntax.Parser
