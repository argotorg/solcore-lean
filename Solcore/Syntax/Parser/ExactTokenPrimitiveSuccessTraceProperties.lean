import Solcore.Syntax.Parser.DeclarativePrimitiveProperties

/-! Exact token grammar determines primitive success without validity premises.
These consumers advance only the cursor and emit no raw diagnostic event. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- An accepted exact token changes only the cursor, not the diagnostic trace. -/
theorem acceptToken_eq_ok_of_exactTokenParses
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) {kind : TokenKind}
    (accepted : accepts kind = true) {input : State} {span : SourceSpan}
    {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ExactTokenParses kind
      input.declarativeRemainder span after) :
    acceptToken expected context accepts input =
      .ok { span, value := kind } { input with cursor := input.cursor + 1 } := by
  have current := parsed.1
  change input.cursor < input.window.endIndex ∧
    input.tokens[input.cursor]? = some { span, value := kind } at current
  have found : input.peek? = some { span, value := kind } := by
    simp only [State.peek?, current.1, if_true, current.2]
  simp only [acceptToken, found, accepted, if_true]

/-- Every successful token consumer preserves the complete raw diagnostic list. -/
theorem acceptToken_success_diagnostics_eq
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) {input output : State} {token : Token}
    (result : acceptToken expected context accepts input = .ok token output) :
    output.diagnostics = input.diagnostics := by
  rw [(acceptToken_ok_state_shape expected context accepts result).2]
  rfl

/-- Fixed token, exact remainder, and silent diagnostics are complete in both
directions; the recognizer may accept other kinds without weakening this claim. -/
theorem acceptToken_exactToken_success_iff
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) {kind : TokenKind}
    (accepted : accepts kind = true) {input : State} {span : SourceSpan}
    {after : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ExactTokenParses kind input.declarativeRemainder span after ↔
      ∃ output, acceptToken expected context accepts input =
        .ok { span, value := kind } output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics := by
  constructor
  · intro parsed
    exact ⟨_, acceptToken_eq_ok_of_exactTokenParses expected context accepts accepted parsed,
      parsed.2.symm, rfl⟩
  · rintro ⟨output, result, remainderEq, _⟩
    rcases acceptToken_ok_state_shape expected context accepts result with ⟨found, shape⟩
    refine ⟨tokenAt_of_peek?_eq_some found, ?_⟩
    rw [← remainderEq, shape]
    rfl

private theorem keyword_accepts_self (value : HardKeyword) :
    ((.keyword value : TokenKind) == .keyword value) = true := by
  change instBEqHardKeyword.beq value value = true
  cases value <;> rfl

private theorem symbol_accepts_self (value : Symbol) :
    ((.symbol value : TokenKind) == .symbol value) = true := by
  change instBEqSymbol.beq value value = true
  cases value <;> rfl

private theorem contextual_accepts_self (value : ContextualKeyword) :
    (TokenKind.identifier value.spelling).isContextual value = true := by
  simp [TokenKind.isContextual]

/-- A hard-keyword grammar step returns the exact keyword token and state. -/
theorem keyword_eq_ok_of_exactTokenParses
    (value : HardKeyword) (context : ParseContext)
    {input : State} {span : SourceSpan} {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ExactTokenParses (.keyword value)
      input.declarativeRemainder span after) :
    keyword value context input = .ok { span, value := .keyword value }
      { input with cursor := input.cursor + 1 } :=
  acceptToken_eq_ok_of_exactTokenParses (.keyword value) context
    (· == .keyword value) (keyword_accepts_self value) parsed

/-- A symbol grammar step returns the exact symbol token and state. -/
theorem symbol_eq_ok_of_exactTokenParses
    (value : Symbol) (context : ParseContext)
    {input : State} {span : SourceSpan} {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ExactTokenParses (.symbol value)
      input.declarativeRemainder span after) :
    symbol value context input = .ok { span, value := .symbol value }
      { input with cursor := input.cursor + 1 } :=
  acceptToken_eq_ok_of_exactTokenParses (.symbol value) context
    (· == .symbol value) (symbol_accepts_self value) parsed

/-- A contextual word returns an identifier token, not a hard keyword. -/
theorem contextual_eq_ok_of_exactTokenParses
    (value : ContextualKeyword) (context : ParseContext)
    {input : State} {span : SourceSpan} {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ExactTokenParses (.identifier value.spelling)
      input.declarativeRemainder span after) :
    contextual value context input = .ok { span, value := .identifier value.spelling }
      { input with cursor := input.cursor + 1 } :=
  acceptToken_eq_ok_of_exactTokenParses (.contextual value) context
    (·.isContextual value) (contextual_accepts_self value) parsed

/-- Hard-keyword exact grammar and executable success have identical silent traces. -/
theorem keyword_exactToken_success_iff
    (value : HardKeyword) (context : ParseContext)
    {input : State} {span : SourceSpan} {after : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ExactTokenParses (.keyword value)
      input.declarativeRemainder span after ↔
      ∃ output, keyword value context input = .ok { span, value := .keyword value } output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics :=
  acceptToken_exactToken_success_iff (.keyword value) context
    (· == .keyword value) (keyword_accepts_self value)

/-- Symbol exact grammar and executable success have identical silent traces. -/
theorem symbol_exactToken_success_iff
    (value : Symbol) (context : ParseContext)
    {input : State} {span : SourceSpan} {after : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ExactTokenParses (.symbol value)
      input.declarativeRemainder span after ↔
      ∃ output, symbol value context input = .ok { span, value := .symbol value } output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics :=
  acceptToken_exactToken_success_iff (.symbol value) context
    (· == .symbol value) (symbol_accepts_self value)

/-- Contextual-word exact grammar preserves its identifier spelling and silent trace. -/
theorem contextual_exactToken_success_iff
    (value : ContextualKeyword) (context : ParseContext)
    {input : State} {span : SourceSpan} {after : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ExactTokenParses (.identifier value.spelling)
      input.declarativeRemainder span after ↔
      ∃ output, contextual value context input =
        .ok { span, value := .identifier value.spelling } output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics :=
  acceptToken_exactToken_success_iff (.contextual value) context
    (·.isContextual value) (contextual_accepts_self value)

end Solcore.Syntax.Parser
