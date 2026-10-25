import Solcore.Syntax.DeclarativeLeftAssociativeTraceGrammar
import Solcore.Syntax.Parser.CoreExpressionBinaryOperatorSoundnessProperties
import Solcore.Syntax.Parser.DiagnosticTraceContracts

/-! Exact ordinary-outcome soundness at every left-associative loop fuel.
Only successful operand file/endByte framing is needed to compose traces.
No progress, endIndex/token preservation, rejected frame, or totality premise
is silently imposed on the operand. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

open DeclarativeGrammar

variable {operand : Parser Expr}
  {operandTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {operandRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem leftAssociativeTail_trace_success_sound
    (successSound : ParserTraceSuccessSound operand operandTrace)
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    (precedence : Nat) : ∀ fuel left input value output,
      leftAssociativeTail operand precedence fuel left input = .ok value output →
      ∃ trace, LeftAssociativeTailTraceParses operandTrace precedence input.file.id input.window.endByte
        input.declarativeRemainder left value output.declarativeRemainder trace ∧
        output.diagnostics = input.diagnostics ++ trace := by
  intro fuel
  induction fuel with
  | zero => intro left input value output result; simp [leftAssociativeTail] at result
  | succ fuel ih =>
      intro left input value output result
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none =>
          simp only [leftAssociativeTail, operatorResult] at result
          cases result
          exact ⟨[], .done (binaryAtPrecedence?_none_absentAt operatorResult), (List.append_nil _).symm⟩
      | some operator =>
          have operatorParsed := consumeBinary_success_sound_of_binaryAtPrecedence?_some
            operatorResult (consumeBinary_ok_state_shape operator input)
          simp only [leftAssociativeTail, operatorResult, consumeBinary_ok_state_shape] at result
          cases childResult : operand { input with cursor := input.cursor + 1 } with
          | invariant error => simp [childResult] at result
          | reject failure rejected => simp [childResult] at result
          | ok right next =>
              simp only [childResult] at result
              rcases successSound childResult with ⟨rightEvents, rightParsed, rightEq⟩
              have frame := successFrame childResult
              rcases ih (binaryNode left operator right) next value output result with
                ⟨tailEvents, tailParsed, tailEq⟩
              refine ⟨rightEvents ++ tailEvents, .next operatorParsed rightParsed ?_, ?_⟩
              · simpa only [frame.1, frame.2, binaryNode, DeclarativeGrammar.binaryNode] using tailParsed
              · rw [tailEq, rightEq]; exact List.append_assoc _ _ _

theorem leftAssociativeTail_reject_trace_sound
    (successSound : ParserTraceSuccessSound operand operandTrace)
    (rejectSound : ParserTraceRejectSound operand operandRejects)
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    (precedence : Nat) : ∀ fuel left input failure rejected,
      leftAssociativeTail operand precedence fuel left input = .reject failure rejected →
      ∃ trace, LeftAssociativeTailTraceRejects operandTrace operandRejects precedence input.file.id input.window.endByte
        input.declarativeRemainder left rejected.declarativeRemainder failure.toDiagnostic trace ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  intro fuel
  induction fuel with
  | zero => intro left input failure rejected result; simp [leftAssociativeTail] at result
  | succ fuel ih =>
      intro left input failure rejected result
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none => simp [leftAssociativeTail, operatorResult] at result
      | some operator =>
          have operatorParsed := consumeBinary_success_sound_of_binaryAtPrecedence?_some
            operatorResult (consumeBinary_ok_state_shape operator input)
          simp only [leftAssociativeTail, operatorResult, consumeBinary_ok_state_shape] at result
          cases childResult : operand { input with cursor := input.cursor + 1 } with
          | invariant error => simp [childResult] at result
          | reject actual next =>
              simp only [childResult] at result; cases result
              rcases rejectSound childResult with ⟨trace, rejection, events⟩
              exact ⟨trace, .rightRejected operatorParsed rejection, events⟩
          | ok right next =>
              simp only [childResult] at result
              rcases successSound childResult with ⟨rightEvents, rightParsed, rightEq⟩
              have frame := successFrame childResult
              rcases ih (binaryNode left operator right) next failure rejected result with
                ⟨tailEvents, tailRejected, tailEq⟩
              refine ⟨rightEvents ++ tailEvents, .laterRejected operatorParsed rightParsed ?_, ?_⟩
              · simpa only [frame.1, frame.2, binaryNode, DeclarativeGrammar.binaryNode] using tailRejected
              · rw [tailEq, rightEq]; exact List.append_assoc _ _ _

theorem leftAssociative_trace_success_sound
    (successSound : ParserTraceSuccessSound operand operandTrace)
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    (precedence : Nat) :
    ParserTraceSuccessSound (leftAssociative operand precedence) (LeftAssociativeTraceParses operandTrace precedence) := by
  intro input output value result
  unfold leftAssociative at result
  cases firstResult : operand input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok left next =>
      simp only [firstResult] at result
      rcases successSound firstResult with ⟨leftEvents, leftParsed, leftEq⟩
      have frame := successFrame firstResult
      rcases leftAssociativeTail_trace_success_sound successSound successFrame precedence
          (next.remainingCount + 1) left next value output result with ⟨tailEvents, tailParsed, tailEq⟩
      refine ⟨leftEvents ++ tailEvents, .parsed leftParsed ?_, ?_⟩
      · simpa only [frame.1, frame.2] using tailParsed
      · rw [tailEq, leftEq]; exact List.append_assoc _ _ _

theorem leftAssociative_reject_trace_sound
    (successSound : ParserTraceSuccessSound operand operandTrace)
    (rejectSound : ParserTraceRejectSound operand operandRejects)
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    (precedence : Nat) : ParserTraceRejectSound (leftAssociative operand precedence)
      (LeftAssociativeTraceRejects operandTrace operandRejects precedence) := by
  intro input rejected failure result
  unfold leftAssociative at result
  cases firstResult : operand input with
  | invariant error => simp [firstResult] at result
  | reject actual next =>
      simp only [firstResult] at result; cases result
      rcases rejectSound firstResult with ⟨trace, rejection, events⟩
      exact ⟨trace, .firstRejected rejection, events⟩
  | ok left next =>
      simp only [firstResult] at result
      rcases successSound firstResult with ⟨leftEvents, leftParsed, leftEq⟩
      have frame := successFrame firstResult
      rcases leftAssociativeTail_reject_trace_sound successSound rejectSound successFrame precedence
          (next.remainingCount + 1) left next failure rejected result with ⟨tailEvents, tailRejected, tailEq⟩
      refine ⟨leftEvents ++ tailEvents, .tailRejected leftParsed ?_, ?_⟩
      · simpa only [frame.1, frame.2] using tailRejected
      · rw [tailEq, leftEq]; exact List.append_assoc _ _ _

end Solcore.Syntax.Parser.ExpressionInternals
