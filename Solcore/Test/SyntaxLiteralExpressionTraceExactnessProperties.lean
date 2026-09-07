import Solcore.Syntax.DeclarativeLiteralExpressionTraceExactnessProperties
import Solcore.Syntax.Parser.LiteralExpressionTraceProperties
import Solcore.Test.SyntaxReturnStatementTraceExactnessProperties

/-! Concrete literal expressions close the expression assumptions in return
existence and isolated-block correspondence. These are restricted parsers. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxLiteralExpressionTraceExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals
open Solcore.Syntax.DeclarativeGrammar

/-- The concrete literal-return parser cannot produce an invariant outcome,
even on invalid carriers or with arbitrary prior diagnostics. -/
theorem literal_return_ne_invariant (input : State) (error : ParserInvariantError) :
    returnStatement literalExpression input ≠ .invariant error := by
  intro result
  rcases SyntaxReturnStatementTraceExactnessProperties.return_execution_has_ordinary_outcome
      literalExpression_trace_success_complete literalExpression_trace_reject_complete
      literalExpression_success_context input
      (literalExpressionTraceOutcomeExists input.file.id input.window.endByte) with successful | rejected
  · rcases successful with ⟨statement, output, trace, ordinary, _⟩
    rw [result] at ordinary
    contradiction
  · rcases rejected with ⟨failure, output, trace, ordinary, _⟩
    rw [result] at ordinary
    contradiction

theorem literal_return_rejection_excludes_success
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ReturnStatementTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects
      source endByte input rejected report trace) :
    ¬ ∃ statement output events, ReturnStatementTraceParses LiteralExpressionTraceParses
      source endByte input statement output events :=
  (literalReturnStatementTraceExactOutcomeSpec source endByte).successRejectDisjoint rejection

/-- Every expression and statement execution premise is discharged by the
real literal leaf; only the independent restricted-block judgment remains. -/
theorem isolated_literal_return_block_trace_iff
    (policy : TailExpressionPolicy) {input : State} {body : Block} {after : Remainder}
    {trace : List ParseDiagnostic} :
    IsolatedBlockTraceParses
      (CoreBlockTraceParses (ReturnStatementTraceParses LiteralExpressionTraceParses) policy.declarative)
      (CoreBlockTraceRejects (ReturnStatementTraceParses LiteralExpressionTraceParses)
        (ReturnStatementTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects)
        policy.declarative)
      input.file.id input.window.endByte input.declarativeRemainder body after trace ↔
    ∃ output, isolateBlock (coreBlock (returnStatement literalExpression) policy) input = .ok body output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  SyntaxReturnStatementTraceExactnessProperties.isolated_return_block_trace_iff
    literalExpression_trace_success_sound literalExpression_trace_reject_sound
    literalExpression_trace_success_complete literalExpression_trace_reject_complete
    literalExpression_success_context policy

end Solcore.Test.SyntaxLiteralExpressionTraceExactnessProperties
