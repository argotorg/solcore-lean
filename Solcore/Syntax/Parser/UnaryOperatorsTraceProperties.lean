import Solcore.Syntax.Parser.CoreExpressionUnarySoundnessProperties
import Solcore.Syntax.Parser.ExpressionUnaryTotalityProperties
import Solcore.Syntax.Parser.DiagnosticTraceStateProperties
import Solcore.Syntax.DeclarativeCoreExpressionOperatorExactnessProperties

/-! Prefix unary scanning is silent on every successful fuel/accumulator
combination and can never reject. Production fuel is adequate on arbitrary
States. Exact initial-scan correspondence fixes the complete operator list,
visible remainder, and every State field without a validity premise. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

open DeclarativeGrammar

theorem unaryOperators_success_state_shape :
    ∀ fuel operatorsRev {input output : State} {operators : List (Located UnaryOp)},
      unaryOperators fuel operatorsRev input = .ok operators output →
      output = { input with cursor := output.cursor } := by
  intro fuel
  induction fuel with
  | zero => intro operatorsRev input output operators result; simp [unaryOperators] at result
  | succ fuel ih =>
      intro operatorsRev input output operators result
      unfold unaryOperators at result
      cases found : input.peek? with
      | none => simp only [found] at result; cases result; rfl
      | some token =>
          simp only [found] at result
          cases decoded : unaryOp? token.value with
          | none => simp only [decoded] at result; cases result; rfl
          | some operator =>
              simp only [decoded] at result
              exact ih ({ span := token.span, value := operator } :: operatorsRev)
                (input := { input with cursor := input.cursor + 1 }) result

theorem unaryOperators_success_context (fuel : Nat) (operatorsRev : List (Located UnaryOp)) :
    ParserSuccessContext (unaryOperators fuel operatorsRev) := by
  intro input output operators result
  have shape := unaryOperators_success_state_shape fuel operatorsRev result
  rw [shape]
  exact ⟨rfl, rfl⟩

theorem unaryOperators_diagnostics_eq_onSuccess (fuel : Nat) (operatorsRev : List (Located UnaryOp))
    {input output : State} {operators : List (Located UnaryOp)}
    (result : unaryOperators fuel operatorsRev input = .ok operators output) :
    output.diagnostics = input.diagnostics := by
  rw [unaryOperators_success_state_shape fuel operatorsRev result]
  rfl

theorem unaryOperators_ne_reject :
    ∀ fuel operatorsRev input failure rejected,
      unaryOperators fuel operatorsRev input ≠ .reject failure rejected := by
  intro fuel
  induction fuel with
  | zero => intro operatorsRev input failure rejected result; simp [unaryOperators] at result
  | succ fuel ih =>
      intro operatorsRev input failure rejected result
      unfold unaryOperators at result
      cases found : input.peek? with
      | none => simp [found] at result
      | some token =>
          simp only [found] at result
          cases decoded : unaryOp? token.value with
          | none => simp [decoded] at result
          | some operator =>
              simp only [decoded] at result
              exact ih ({ span := token.span, value := operator } :: operatorsRev)
                { input with cursor := input.cursor + 1 } failure rejected result

theorem unaryOperators_trace_success_sound {fuel : Nat} {input output : State}
    {operators : List (Located UnaryOp)} (result : unaryOperators fuel [] input = .ok operators output) :
    UnaryOperatorsParses input.declarativeRemainder operators output.declarativeRemainder ∧
      output = input.traceResult output.declarativeRemainder [] := by
  have frame := unaryOperators_success_context fuel [] result
  exact ⟨unaryOperators_success_sound result, State.eq_traceResult_of_fields frame.1
    (congrArg TokenWindow.endByte frame.2) rfl (by
      simpa only [List.append_nil] using unaryOperators_diagnostics_eq_onSuccess fuel [] result)⟩

theorem unaryOperators_trace_success_complete {input : State} {operators : List (Located UnaryOp)}
    {after : Remainder} (parsed : UnaryOperatorsParses input.declarativeRemainder operators after) :
    unaryOperators (input.remainingCount + 1) [] input = .ok operators (input.traceResult after []) := by
  rcases unaryOperators_production_exists_ok [] input with ⟨actual, output, result⟩
  have sound := unaryOperators_trace_success_sound result
  rcases sound.1.result_unique parsed with ⟨rfl, afterEq⟩
  have same := sound.2.trans (congrArg (fun remainder => input.traceResult remainder []) afterEq)
  exact same ▸ result

theorem unaryOperators_trace_success_state_iff {input : State} {operators : List (Located UnaryOp)}
    {after : Remainder} :
    UnaryOperatorsParses input.declarativeRemainder operators after ↔
      unaryOperators (input.remainingCount + 1) [] input = .ok operators (input.traceResult after []) := by
  constructor
  · exact unaryOperators_trace_success_complete
  · intro result
    simpa only [State.traceResult_declarativeRemainder] using unaryOperators_success_sound result

theorem unaryOperators_exists_exact_trace_outcome (input : State) :
    ∃ operators after, UnaryOperatorsParses input.declarativeRemainder operators after ∧
      unaryOperators (input.remainingCount + 1) [] input = .ok operators (input.traceResult after []) := by
  rcases unaryOperators_production_exists_ok [] input with ⟨operators, output, result⟩
  have sound := unaryOperators_trace_success_sound result
  exact ⟨operators, output.declarativeRemainder, sound.1, sound.2 ▸ result⟩

/-- Independent maximal prefixes actually exist; their uniqueness alone was
not used as a substitute for the scanner's successful production execution. -/
theorem unaryOperatorsTrace_outcome_exists (input : Remainder) :
    ∃ operators after, UnaryOperatorsParses input operators after := by
  let state : State := {
    file := { id := { origin := .main, path := "" }, content := "" }, tokens := input.tokens
    cursor := input.cursor, window := { endIndex := input.endIndex, endByte := 0 }, diagnosticsRev := []
  }
  rcases unaryOperators_exists_exact_trace_outcome state with ⟨operators, after, parsed, _⟩
  exact ⟨operators, after, parsed⟩

end Solcore.Syntax.Parser.ExpressionInternals
