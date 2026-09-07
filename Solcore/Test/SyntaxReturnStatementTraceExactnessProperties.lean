import Solcore.Syntax.DeclarativeReturnStatementTraceExactnessProperties
import Solcore.Syntax.Parser.ReturnStatementSuccessTraceProperties
import Solcore.Syntax.Parser.ReturnStatementRejectionTraceCompletenessProperties
import Solcore.Syntax.Parser.CoreBlockIsolationTraceProperties

/-! Conditional return exactness, outcome existence, and isolated block
composition, with every abstract expression assumption visible to the caller. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxReturnStatementTraceExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

variable {expression : Parser Expr}
  {expressionTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {expressionRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}

theorem return_rejection_excludes_every_success
    {source : SourceId} {endByte : Nat}
    (expressions : ExpressionTraceExactOutcomeSpec expressionTrace expressionRejects source endByte)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ReturnStatementTraceRejects expressionTrace expressionRejects
      source endByte input rejected diagnostic trace) :
    ¬ ∃ statement output events,
      ReturnStatementTraceParses expressionTrace source endByte input statement output events :=
  (returnStatementTraceExactOutcomeSpec expressions).successRejectDisjoint rejection

/-- Independent expression existence and execution completeness suffice for
an actual ordinary return result; exactness and soundness are not assumed. -/
theorem return_execution_has_ordinary_outcome
    (successComplete : ExpressionTraceSuccessComplete expression expressionTrace)
    (rejectComplete : ExpressionTraceRejectComplete expression expressionRejects)
    (contextFrame : ExpressionSuccessContext expression) (input : State)
    (expressions : ExpressionTraceOutcomeExists expressionTrace expressionRejects
      input.file.id input.window.endByte) :
    (∃ statement output trace, returnStatement expression input = .ok statement output ∧
      output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace, returnStatement expression input = .reject failure rejected ∧
      rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases returnStatementTrace_exists_outcome expressions input.declarativeRemainder with successful | rejected
  · rcases successful with ⟨statement, after, trace, parsed⟩
    rcases returnStatement_trace_success_complete successComplete parsed with
      ⟨output, result, _, diagnostics⟩
    exact Or.inl ⟨statement, output, trace, result, diagnostics⟩
  · rcases rejected with ⟨after, diagnostic, trace, rejection⟩
    rcases returnStatement_trace_reject_complete successComplete rejectComplete contextFrame rejection with
      ⟨failure, rejected, result, _, _, diagnostics⟩
    exact Or.inr ⟨failure, rejected, trace, result, diagnostics⟩

/-- Abstract expression contracts discharge every statement assumption for
isolated blocks restricted to returns, including a recovered inner rejection. -/
theorem isolated_return_block_trace_iff
    (successSound : ExpressionTraceSuccessSound expression expressionTrace)
    (rejectSound : ExpressionTraceRejectSound expression expressionRejects)
    (successComplete : ExpressionTraceSuccessComplete expression expressionTrace)
    (rejectComplete : ExpressionTraceRejectComplete expression expressionRejects)
    (contextFrame : ExpressionSuccessContext expression) (policy : TailExpressionPolicy)
    {input : State} {body : Block} {after : Remainder} {trace : List ParseDiagnostic} :
    IsolatedBlockTraceParses (CoreBlockTraceParses (ReturnStatementTraceParses expressionTrace) policy.declarative)
      (CoreBlockTraceRejects (ReturnStatementTraceParses expressionTrace)
        (ReturnStatementTraceRejects expressionTrace expressionRejects) policy.declarative)
      input.file.id input.window.endByte input.declarativeRemainder body after trace ↔
    ∃ output, isolateBlock (coreBlock (returnStatement expression) policy) input = .ok body output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  isolatedCoreBlock_trace_success_iff (returnStatement_trace_success_sound successSound)
    (returnStatement_reject_trace_sound successSound rejectSound contextFrame)
    (returnStatement_trace_success_complete successComplete)
    (returnStatement_trace_reject_complete successComplete rejectComplete contextFrame)
    (returnStatement_success_context contextFrame) policy

end Solcore.Test.SyntaxReturnStatementTraceExactnessProperties
