import Solcore.Syntax.DeclarativeExpressionNameTraceProperties
import Solcore.Syntax.Parser.BooleanIdentifierRejectionTraceProperties
import Solcore.Syntax.Parser.IdentifierTraceProperties
import Solcore.Syntax.Parser.PragmaItemsContextProperties

/-! Exact Boolean-first expression-name success with checked spelling events. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem isBooleanValue_true_of_booleanParses
    {input : State} {name : Identifier} {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.BooleanIdentifierParses input.declarativeRemainder name after) :
    isBooleanValue input = true := by
  cases parsed with
  | trueKeyword token =>
      rename_i span
      change input.cursor < input.window.endIndex ∧
        input.tokens[input.cursor]? = some { span, value := .keyword .trueKw } at token
      have found : input.peek? = some { span, value := .keyword .trueKw } := by
        simp only [State.peek?, token.1, if_true, token.2]
      simp only [isBooleanValue, isKeyword, State.peekKind?, found, Option.map_some]
      rfl
  | falseKeyword token =>
      rename_i span
      change input.cursor < input.window.endIndex ∧
        input.tokens[input.cursor]? = some { span, value := .keyword .falseKw } at token
      have found : input.peek? = some { span, value := .keyword .falseKw } := by
        simp only [State.peek?, token.1, if_true, token.2]
      simp only [isBooleanValue, isKeyword, State.peekKind?, found, Option.map_some]
      rfl

theorem isBooleanValue_false_of_absent {input : State}
    (absent : DeclarativeGrammar.BooleanPatternAbsentAt input.declarativeRemainder) :
    isBooleanValue input = false := by
  unfold isBooleanValue isKeyword State.peekKind?
  cases found : input.peek? with
  | none => rfl
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> try rfl
      case keyword keyword =>
        cases keyword <;> try rfl
        case trueKw => exact False.elim (absent.1 ⟨span, tokenAt_of_peek?_eq_some found⟩)
        case falseKw => exact False.elim (absent.2 ⟨span, tokenAt_of_peek?_eq_some found⟩)

theorem booleanAbsent_of_isBooleanValue_false {input : State}
    (absent : isBooleanValue input = false) :
    DeclarativeGrammar.BooleanPatternAbsentAt input.declarativeRemainder := by
  have both := Bool.or_eq_false_iff.mp absent
  exact ⟨keywordAbsentAt_of_isKeyword_eq_false .trueKw both.1,
    keywordAbsentAt_of_isKeyword_eq_false .falseKw both.2⟩

theorem expressionName_eq_identifier_of_booleanAbsent {input : State}
    (absent : DeclarativeGrammar.BooleanPatternAbsentAt input.declarativeRemainder) :
    expressionName input = identifier .expression input := by
  simp only [expressionName, isBooleanValue_false_of_absent absent, Bool.false_eq_true, if_false]

theorem expressionName_success_trace_sound
    {input output : State} {name : Identifier}
    (result : expressionName input = .ok name output) :
    ∃ trace, DeclarativeGrammar.ExpressionNameTraceParses input.file.id input.window.endByte
      input.declarativeRemainder name output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace := by
  unfold expressionName at result
  cases present : isBooleanValue input with
  | true =>
      simp only [present, if_true] at result
      exact ⟨[], .boolean ⟨booleanIdentifier_success_sound result, rfl⟩,
        by simpa only [List.append_nil] using booleanIdentifier_success_diagnostics_eq result⟩
  | false =>
      simp only [present, Bool.false_eq_true, if_false] at result
      rcases identifier_success_trace_sound .expression result with ⟨trace, parsed, events⟩
      exact ⟨trace, .identifier (booleanAbsent_of_isBooleanValue_false present) parsed, events⟩

theorem expressionName_trace_success_complete
    {input : State} {name : Identifier} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.ExpressionNameTraceParses input.file.id input.window.endByte
      input.declarativeRemainder name after trace) :
    ∃ output, expressionName input = .ok name output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  cases parsed with
  | boolean parsed =>
      rcases booleanIdentifier_trace_success_iff.mp parsed with ⟨output, result, afterEq, events⟩
      exact ⟨output, by simp only [expressionName, isBooleanValue_true_of_booleanParses parsed.1,
        if_true, result], afterEq, events⟩
  | identifier absent parsed =>
      rcases (identifier_trace_success_iff .expression).mp parsed with ⟨output, result, afterEq, events⟩
      exact ⟨output, (expressionName_eq_identifier_of_booleanAbsent absent).trans result, afterEq, events⟩

theorem expressionName_success_context_eq
    {input output : State} {name : Identifier}
    (result : expressionName input = .ok name output) :
    output.file = input.file ∧ output.window = input.window := by
  unfold expressionName at result
  split at result
  · rw [booleanIdentifier_ok_state_shape result]; exact ⟨rfl, rfl⟩
  · exact identifier_success_context_eq .expression result

theorem expressionName_trace_success_iff
    {input : State} {name : Identifier} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ExpressionNameTraceParses input.file.id input.window.endByte
      input.declarativeRemainder name after trace ↔
    ∃ output, expressionName input = .ok name output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact expressionName_trace_success_complete
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases expressionName_success_trace_sound result with ⟨actualTrace, parsed, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

/-- An independent name trace fixes the entire output state: exactly one
token advance and the reversed fresh trace prepended to prior reverse events. -/
theorem expressionName_success_state_eq_of_trace
    {input output : State} {name : Identifier} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic}
    (result : expressionName input = .ok name output)
    (parsed : DeclarativeGrammar.ExpressionNameTraceParses input.file.id input.window.endByte
      input.declarativeRemainder name after trace) :
    output = { input with
      cursor := input.cursor + 1
      diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  rcases expressionName_success_trace_sound result with ⟨actualTrace, actual, actualEq⟩
  have same := actual.result_unique parsed
  have remaining := actual.output_eq
  have tokensEq : output.tokens = input.tokens :=
    congrArg DeclarativeGrammar.Remainder.tokens remaining
  have cursorEq : output.cursor = input.cursor + 1 :=
    congrArg DeclarativeGrammar.Remainder.cursor remaining
  have frame := expressionName_success_context_eq result
  have events := congrArg List.reverse actualEq
  have diagnosticsEq : output.diagnosticsRev = trace.reverse ++ input.diagnosticsRev := by
    simpa only [same.2.2, State.diagnostics, List.reverse_append, List.reverse_reverse] using events
  cases input
  cases output
  simp_all only [State.declarativeRemainder]

theorem expressionName_eq_ok_of_trace
    {input : State} {name : Identifier} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.ExpressionNameTraceParses input.file.id input.window.endByte
      input.declarativeRemainder name after trace) :
    expressionName input = .ok name { input with
      cursor := input.cursor + 1
      diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  rcases expressionName_trace_success_complete parsed with ⟨output, result, _, _⟩
  exact expressionName_success_state_eq_of_trace result parsed ▸ result

end Solcore.Syntax.Parser.ExpressionAtomInternals
