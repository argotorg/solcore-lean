import Solcore.Syntax.DeclarativeLiteralDiagnosticTraceProperties
import Solcore.Syntax.Parser.CoreLiteralOutcomeSoundnessProperties

/-! Exact ASTs, silent traces, and one-token state updates for literal leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem peek_of_token {input : State} {token : Token}
    (present : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex input.cursor token) :
    input.peek? = some token := by
  simp only [State.peek?, present.1, if_true, present.2]

theorem coreLiteral_eq_ok_of_ordinary
    {input : State} {literal : CoreLiteral} {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.CoreLiteralParses input.declarativeRemainder literal after) :
    coreLiteral input = .ok literal { input with cursor := input.cursor + 1 } := by
  cases parsed with
  | decimal token => simp only [coreLiteral, peek_of_token token]
  | hexadecimal token => simp only [coreLiteral, peek_of_token token]
  | string token => simp only [coreLiteral, peek_of_token token]

theorem booleanIdentifier_eq_ok_of_ordinary
    {input : State} {name : Identifier} {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.BooleanIdentifierParses input.declarativeRemainder name after) :
    booleanIdentifier input = .ok name { input with cursor := input.cursor + 1 } := by
  cases parsed with
  | trueKeyword token => simp only [booleanIdentifier, peek_of_token token]
  | falseKeyword token => simp only [booleanIdentifier, peek_of_token token]

theorem coreLiteral_success_diagnostics_eq
    {input output : State} {literal : CoreLiteral}
    (result : coreLiteral input = .ok literal output) : output.diagnostics = input.diagnostics := by
  rw [coreLiteral_ok_state_shape result]
  rfl

theorem booleanIdentifier_success_diagnostics_eq
    {input output : State} {name : Identifier}
    (result : booleanIdentifier input = .ok name output) : output.diagnostics = input.diagnostics := by
  rw [booleanIdentifier_ok_state_shape result]
  rfl

theorem coreLiteral_trace_success_iff
    {input : State} {literal : CoreLiteral} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.CoreLiteralTraceParses input.file.id input.window.endByte
      input.declarativeRemainder literal after trace ↔
    ∃ output, coreLiteral input = .ok literal output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · rintro ⟨parsed, rfl⟩
    exact ⟨_, coreLiteral_eq_ok_of_ordinary parsed,
      (DeclarativeGrammar.CoreLiteralOrdinaryParses.output_eq parsed).symm,
      by simp only [List.append_nil, State.diagnostics]⟩
  · rintro ⟨output, result, afterEq, diagnostics⟩
    refine ⟨afterEq ▸ coreLiteral_success_sound result, ?_⟩
    apply List.append_cancel_left (as := input.diagnostics)
    simpa only [List.append_nil] using diagnostics.symm.trans (coreLiteral_success_diagnostics_eq result)

theorem booleanIdentifier_trace_success_iff
    {input : State} {name : Identifier} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.BooleanIdentifierTraceParses input.file.id input.window.endByte
      input.declarativeRemainder name after trace ↔
    ∃ output, booleanIdentifier input = .ok name output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · rintro ⟨parsed, rfl⟩
    refine ⟨_, booleanIdentifier_eq_ok_of_ordinary parsed, ?_,
      by simp only [List.append_nil, State.diagnostics]⟩
    cases parsed <;> rfl
  · rintro ⟨output, result, afterEq, diagnostics⟩
    refine ⟨afterEq ▸ booleanIdentifier_success_sound result, ?_⟩
    apply List.append_cancel_left (as := input.diagnostics)
    simpa only [List.append_nil] using
      diagnostics.symm.trans (booleanIdentifier_success_diagnostics_eq result)

end Solcore.Syntax.Parser
