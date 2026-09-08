import Solcore.Syntax.Parser.ExpressionAtomDispatchRejectionContextProperties
import Solcore.Syntax.Parser.ExpressionAtomDispatchTraceCorrespondenceProperties
import Solcore.Syntax.Parser.ExpressionAtomTraceStateProperties

/-! Concrete atom-test support: the recursive expression slot uses the actual
literal leaf, while the supplied block is exactly one pure empty AST. These
contracts describe only that supplied parser, not general recursive blocks. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxExpressionAtomTraceSupport

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open ExpressionAtomInternals

def emptyBlock : Block := {
  span := { source := { origin := .main, path := "unused-atom-block.sol" }, startByte := 0, endByte := 0 }, value := []
}
def blockParser : Parser Block := pure emptyBlock
def blockTrace (_ : SourceId) (_ : Nat) (input : Remainder) (value : Block)
    (output : Remainder) (trace : List ParseDiagnostic) : Prop :=
  value = emptyBlock ∧ output = input ∧ trace = []
def blockRejects (_ : SourceId) (_ : Nat) (_ _ : Remainder) (_ : ParseDiagnostic)
    (_ : List ParseDiagnostic) : Prop := False

private theorem block_success_sound : ParserTraceSuccessSound blockParser blockTrace := by
  intro input output value result
  change Reply.ok emptyBlock input = Reply.ok value output at result
  cases result
  exact ⟨[], ⟨rfl, rfl, rfl⟩, by simp⟩
private theorem block_success_complete : ParserTraceSuccessComplete blockParser blockTrace := by
  rintro input value after trace ⟨rfl, rfl, rfl⟩
  exact ⟨input, rfl, rfl, by simp⟩
private theorem block_success_context : ParserSuccessContext blockParser := by
  intro input output value result
  change Reply.ok emptyBlock input = Reply.ok value output at result
  cases result
  exact ⟨rfl, rfl⟩
private theorem block_reject_sound : ParserTraceRejectSound blockParser blockRejects := by
  intro input output failure result
  simp [blockParser, pure] at result
private theorem block_reject_complete : ParserTraceRejectComplete blockParser blockRejects := by
  intro input after report trace impossible
  exact False.elim impossible
private theorem block_reject_frame {input output : State} {failure : Failure}
    (result : blockParser input = .reject failure output) :
    output.file = input.file ∧ output.window.endByte = input.window.endByte := by
  simp [blockParser, pure] at result

abbrev coreParses := ExpressionAtomDispatchTraceParses LiteralExpressionTraceParses blockTrace
abbrev coreRejects := ExpressionAtomDispatchTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects blockRejects

private theorem core_success_sound : ParserTraceSuccessSound (expressionAtomCore literalExpression blockParser) coreParses :=
  expressionAtomCore_trace_success_sound literalExpression_trace_success_sound literalExpression_success_context block_success_sound
private theorem core_success_complete : ParserTraceSuccessComplete (expressionAtomCore literalExpression blockParser) coreParses :=
  expressionAtomCore_trace_success_complete literalExpression_trace_success_complete literalExpression_success_context block_success_complete
private theorem core_reject_sound : ParserTraceRejectSound (expressionAtomCore literalExpression blockParser) coreRejects :=
  expressionAtomCore_reject_trace_sound literalExpression_trace_success_sound literalExpression_trace_reject_sound
    literalExpression_success_context block_reject_sound
private theorem core_reject_complete : ParserTraceRejectComplete (expressionAtomCore literalExpression blockParser) coreRejects :=
  expressionAtomCore_trace_reject_complete literalExpression_trace_success_complete literalExpression_trace_reject_complete
    literalExpression_success_context block_reject_complete
private theorem core_success_frame {input output : State} {value : Expr}
    (result : expressionAtomCore literalExpression blockParser input = .ok value output) :
    output.file = input.file ∧ output.window.endByte = input.window.endByte := by
  have frame := expressionAtomCore_trace_success_context literalExpression_success_context block_success_context result
  exact ⟨frame.1, congrArg TokenWindow.endByte frame.2⟩
private theorem core_reject_frame {input output : State} {failure : Failure}
    (result : expressionAtomCore literalExpression blockParser input = .reject failure output) :
    output.file = input.file ∧ output.window.endByte = input.window.endByte :=
  expressionAtomCore_reject_source_endByte literalExpression_success_context
    (fun result => ⟨(literalExpression_reject_context result).1,
      congrArg TokenWindow.endByte (literalExpression_reject_context result).2⟩) block_reject_frame result

theorem core_reject_of_trace {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic}
    (rejection : coreRejects input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace) :
    expressionAtomCore literalExpression blockParser input = .reject failure (input.traceResult after trace) :=
  (expressionAtomCore_trace_reject_failure_state_iff literalExpression_trace_success_sound literalExpression_trace_reject_sound
    literalExpression_trace_success_complete literalExpression_trace_reject_complete literalExpression_success_context
    block_reject_sound block_reject_complete core_reject_frame).mp rejection

theorem public_success_of_trace {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic}
    (parsed : ExpressionAtomTraceParses coreParses coreRejects input.file.id input.window.endByte
      input.declarativeRemainder value after trace) :
    expressionAtom literalExpression blockParser input = .ok value (input.traceResult after trace) :=
  (expressionAtom_trace_success_state_iff core_success_sound core_reject_sound core_success_complete core_reject_complete
    core_success_frame core_reject_frame).mp parsed

theorem public_reject_of_trace {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic}
    (rejection : ExpressionAtomTraceRejects coreRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace) :
    expressionAtom literalExpression blockParser input = .reject failure (input.traceResult after trace) :=
  (expressionAtom_trace_reject_failure_state_iff core_reject_sound core_reject_complete core_reject_frame).mp rejection

end Solcore.Test.SyntaxExpressionAtomTraceSupport
