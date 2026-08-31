import Solcore.Syntax.Parser.Expression.Atom
import Solcore.Syntax.Parser.LiteralProperties
import Solcore.Syntax.ExpressionValidity

/-! Provenance and state contracts for canonical Core expression atoms. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ExpressionAtomInternals

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

end ExpressionAtomInternals
end Solcore.Syntax.Parser
