import Solcore.Syntax.DeclarativeParameterRecoveryTraceProperties
import Solcore.Syntax.Parser.CoreLambdaParameterRecoveryOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.SourceFrameProperties
import Solcore.Syntax.Parser.DiagnosticTraceStateProperties

/-! Standalone recovery appends exactly one event on success, retains the
complete source/window, and rejects without committing its terminal report.
The scan never replays diagnostics from the tokens that it skips. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FunctionParameterInternals

open DeclarativeGrammar

private theorem advance_state {input next : State} {token : Token}
    (advanced : input.advance? = some (token, next)) :
    next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      rfl

theorem recoverParameterAux_success_frame (first : SourceSpan) :
    ∀ fuel last {input output : State} {value : FunctionParameter},
      recoverParameterAux first last fuel input = .ok value output →
      output.file = input.file ∧
        output.diagnostics = input.diagnostics ++ [parameterRecoveryTraceEvent value.span] := by
  intro fuel
  induction fuel with
  | zero => intro last input output value result; simp [recoverParameterAux] at result
  | succ fuel ih =>
      intro last input output value result
      unfold recoverParameterAux at result
      split at result
      · unfold finishRecoveredParameter at result
        cases result
        exact ⟨rfl, by simp [State.emit, State.diagnostics, parameterRecoveryTraceEvent]⟩
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            unfold finishRecoveredParameter at result
            cases result
            exact ⟨rfl, by simp [State.emit, State.diagnostics, parameterRecoveryTraceEvent]⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at result
            have shape := advance_state advanced
            subst next
            exact ih token.span (input := { input with cursor := input.cursor + 1 }) result

theorem recoverParameter_success_frame {input output : State} {value : FunctionParameter}
    (result : recoverParameter input = .ok value output) :
    output.file = input.file ∧ output.diagnostics = input.diagnostics ++ [parameterRecoveryTraceEvent value.span] := by
  unfold recoverParameter at result
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at result
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at result
      have frame := recoverParameterAux_success_frame token.span (next.remainingCount + 1) token.span result
      rw [advance_state advanced] at frame
      exact frame

theorem recoverParameter_reject_shape {input rejected : State} {failure : Failure}
    (result : recoverParameter input = .reject failure rejected) :
    rejected = input ∧ (rejectAt input { head := .identifier, tail := [] } .parameter : Reply FunctionParameter) =
      .reject failure input := by
  unfold recoverParameter at result
  cases advanced : input.advance? with
  | none =>
      simp only [advanced] at result
      unfold rejectAt at result
      cases result
      exact ⟨rfl, rfl⟩
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at result
      rcases recoverParameterAux_production_exists_ok token.span token.span next with ⟨value, output, success⟩
      rw [success] at result
      contradiction

theorem recoverParameter_preservesFile : Parser.PreservesFile recoverParameter := by
  intro input
  cases result : recoverParameter input with
  | invariant error => trivial
  | ok value output => exact (recoverParameter_success_frame result).1
  | reject failure rejected => rw [(recoverParameter_reject_shape result).1]; rfl

theorem recoverParameter_success_context : ParserSuccessContext recoverParameter := by
  intro input output value result
  have window := recoverParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨(recoverParameter_success_frame result).1, window.2⟩

theorem recoverParameter_reject_context {input rejected : State} {failure : Failure}
    (result : recoverParameter input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  rw [(recoverParameter_reject_shape result).1]
  exact ⟨rfl, rfl⟩

end Solcore.Syntax.Parser.FunctionParameterInternals
