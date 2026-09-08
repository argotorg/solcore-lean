import Solcore.Test.SyntaxExpressionAtomTotalityProperties
import Solcore.Syntax.Parser.ExpressionPostfixLayerTraceProperties
import Solcore.Syntax.Parser.ExpressionPostfixUnrestrictedChildContractProperties
import Solcore.Syntax.Parser.ExpressionPostfixTraceContextProperties
import Solcore.Syntax.Parser.ExpressionPostfixTraceCorrespondenceProperties
import Solcore.Syntax.Parser.ExpressionUnaryTraceStateProperties

/-! Concrete unary consumers use the real literal child and one supplied
always-rejecting block. All-input postfix completeness is discharged from
exact independent outcomes, soundness, and bounded child execution; no general
recursive expression or block completeness is assumed. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxExpressionUnaryTraceSupport

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open ExpressionAtomInternals ExpressionInternals SyntaxExpressionAtomTotalityProperties

def blockFailure : Failure := {
  span := { source := { origin := .main, path := "unused-unary-block.sol" }, startByte := 0, endByte := 0 }
  found := none, expected := { head := .symbol .leftBrace, tail := [] }, context := .expression
}
def blockParser : Parser Block := fun input => .reject blockFailure input
def blockTrace (_ : SourceId) (_ : Nat) (_ : Remainder) (_ : Block) (_ : Remainder)
    (_ : List ParseDiagnostic) : Prop := False
def blockRejects (_ : SourceId) (_ : Nat) (input rejected : Remainder) (report : ParseDiagnostic)
    (trace : List ParseDiagnostic) : Prop := rejected = input ∧ report = blockFailure.toDiagnostic ∧ trace = []

private theorem block_contract (fuel : Nat) : UnrestrictedFuelElementContract blockParser fuel where
  endIndexOnSuccess result := by contradiction
  cursorLtOnSuccess result := by contradiction
  ordinary input _ := .inr ⟨blockFailure, input, rfl⟩

private theorem block_success_sound : ParserTraceSuccessSound blockParser blockTrace := by
  intro input output value result
  contradiction
private theorem block_reject_sound : ParserTraceRejectSound blockParser blockRejects := by
  intro input rejected failure result
  change Reply.reject blockFailure input = Reply.reject failure rejected at result
  cases result
  exact ⟨[], ⟨rfl, rfl, rfl⟩, by simp⟩
private theorem block_context : ParserSuccessContext blockParser := by
  intro input output value result
  contradiction
private theorem block_reject_frame {input rejected : State} {failure : Failure}
    (result : blockParser input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  change Reply.reject blockFailure input = Reply.reject failure rejected at result
  cases result
  exact ⟨rfl, rfl⟩
private theorem block_outcomes (source : SourceId) (endByte : Nat) :
    TraceExactOutcomeSpec blockTrace blockRejects source endByte where
  successResultUnique impossible := False.elim impossible
  rejectResultUnique left right := ⟨left.1.trans right.1.symm, left.2.1.trans right.2.1.symm, left.2.2.trans right.2.2.symm⟩
  successRejectDisjoint _ parsed := by rcases parsed with ⟨_, _, _, impossible⟩; exact impossible

abbrev postfixTrace := ExpressionPostfixLayerTraceParses
  LiteralExpressionTraceParses LiteralExpressionTraceRejects blockTrace blockRejects
abbrev postfixRejects := ExpressionPostfixLayerTraceRejects
  LiteralExpressionTraceParses LiteralExpressionTraceRejects blockTrace blockRejects

private theorem postfix_sound : ParserTraceSuccessSound (expressionPostfix literalExpression blockParser) postfixTrace :=
  expressionPostfix_layer_trace_success_sound literalExpression_trace_success_sound literalExpression_trace_reject_sound
    literalExpression_success_context block_success_sound block_reject_sound block_context
    literalExpression_reject_context block_reject_frame
private theorem postfix_reject_sound : ParserTraceRejectSound (expressionPostfix literalExpression blockParser) postfixRejects :=
  expressionPostfix_layer_reject_trace_sound literalExpression_trace_success_sound literalExpression_trace_reject_sound
    literalExpression_success_context block_success_sound block_reject_sound block_context
    literalExpression_reject_context block_reject_frame
private theorem postfix_ne_invariant (input : State) (error : ParserInvariantError) :
    expressionPostfix literalExpression blockParser input ≠ .invariant error :=
  expressionPostfix_ne_invariant_of_unrestrictedChildFuels literalExpression blockParser
    input.remainingCount input.remainingCount (literal_child_contract _) (block_contract _)
    (fun result => congrArg TokenWindow.endIndex (literalExpression_reject_context result).2)
    (fun result => congrArg TokenWindow.endIndex (block_reject_frame result).2)
    input (Nat.lt_succ_self _) (Nat.lt_succ_self _) error
private theorem postfix_outcomes (source : SourceId) (endByte : Nat) :
    TraceExactOutcomeSpec postfixTrace postfixRejects source endByte :=
  expressionPostfixLayerTraceExactOutcomeSpec
    (literalExpressionTraceExactOutcomeSpec source endByte).toTraceExactOutcomeSpec (block_outcomes source endByte)
private theorem postfix_complete : ParserTraceSuccessComplete (expressionPostfix literalExpression blockParser) postfixTrace := by
  intro input value after trace parsed
  exact trace_success_exists_ok_of_sound postfix_sound postfix_reject_sound (postfix_outcomes _ _)
    (postfix_ne_invariant input) parsed
private theorem postfix_reject_complete : ParserTraceRejectComplete (expressionPostfix literalExpression blockParser) postfixRejects := by
  intro input after report trace rejection
  exact trace_reject_exists_reject_of_sound postfix_sound postfix_reject_sound (postfix_outcomes _ _)
    (postfix_ne_invariant input) rejection

private theorem atom_context : ParserSuccessContext (expressionAtom literalExpression blockParser) :=
  expressionAtom_layer_success_context literalExpression_success_context block_context
    literalExpression_reject_context block_reject_frame
private theorem atom_reject_frame {input rejected : State} {failure : Failure}
    (result : expressionAtom literalExpression blockParser input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte :=
  expressionAtom_reject_source_end
    (expressionAtomCore_reject_source_endByte literalExpression_success_context
      (fun result => ⟨(literalExpression_reject_context result).1,
        congrArg TokenWindow.endByte (literalExpression_reject_context result).2⟩)
      (fun result => ⟨(block_reject_frame result).1, congrArg TokenWindow.endByte (block_reject_frame result).2⟩)) result

theorem success_of_trace {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic}
    (parsed : ExpressionUnaryTraceParses postfixTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace) :
    expressionUnary literalExpression blockParser input = .ok value (input.traceResult after trace) :=
  (expressionUnary_trace_success_state_iff postfix_sound postfix_complete
    (fun result => ⟨(expressionPostfix_trace_success_context atom_context literalExpression_success_context result).1,
      congrArg TokenWindow.endByte (expressionPostfix_trace_success_context atom_context literalExpression_success_context result).2⟩)).mp parsed

theorem reject_of_trace {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic}
    (rejection : ExpressionUnaryTraceRejects postfixRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace) :
    expressionUnary literalExpression blockParser input = .reject failure (input.traceResult after trace) :=
  (expressionUnary_trace_reject_failure_state_iff postfix_reject_sound postfix_reject_complete
    (expressionPostfix_reject_context_of_windowProjection atom_context literalExpression_success_context atom_reject_frame
      (fun result => ⟨(literalExpression_reject_context result).1,
        congrArg TokenWindow.endByte (literalExpression_reject_context result).2⟩))).mp rejection

end Solcore.Test.SyntaxExpressionUnaryTraceSupport
