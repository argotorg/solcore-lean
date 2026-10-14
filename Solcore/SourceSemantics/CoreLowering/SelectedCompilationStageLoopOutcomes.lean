import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.Staging.RecursiveControlTransferFacts

/-! The loop consumes body break and continue. Its final result keeps the
outer environment and cannot carry either control transfer beyond the loop. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLoopOutcomes
open Frontend SourceInference Staging.Recursive

variable {program : Program} {stages : Registry} {invocation : Scope}
  {context : SourceSemantics.Context} {environment inner : Dynamic.Environment}
  {before after : Dynamic.Heap} {test : ExpressionId} {post : List ForItemForm}
  {body : List StatementId} {size : Nat} {outcome : BodyOutcome}

theorem while_closed (trace : Size.While program stages size invocation context environment before test body outcome after) :
    outcome.NoEscapedControl := by
  induction size using Nat.strongRecOn generalizing before after outcome with
  | ind size ih =>
    cases trace with
    | done | breakFromBody => exact .fallthrough environment
    | returned => exact .returned _
    | conditionFault | bodyFault => exact .fault _
    | next test body next | continueNext test body next =>
      exact ih _ (Size.child_lt_stepSize (by simp)) next

theorem for_closed (trace : Size.ForLoop program stages size invocation context environment before test post body outcome after) :
    outcome.NoEscapedControl := by
  induction size using Nat.strongRecOn generalizing before after outcome with
  | ind size ih =>
    cases trace with
    | finished | forBreakFromBody => exact .fallthrough environment
    | returnedFromBody => exact .returned _
    | testFault | bodyFailure | postFailure | continuePostFailure => exact .fault _
    | iterate test body post next | continueIterate test body post next =>
      exact ih _ (Size.child_lt_stepSize (by simp)) next

theorem while_closed_of_trace
    (trace : While program stages invocation context environment before test body outcome after) :
    outcome.NoEscapedControl := by
  obtain ⟨size, measured⟩ := Size.While.of_trace trace
  exact while_closed measured

theorem for_closed_of_trace
    (trace : ForLoop program stages invocation context environment before test post body outcome after) :
    outcome.NoEscapedControl := by
  obtain ⟨size, measured⟩ := Size.ForLoop.of_trace trace
  exact for_closed measured

theorem while_environment
    (trace : Size.While program stages size invocation context environment before test body (.fallthrough inner) after) :
    inner = environment := by
  induction size using Nat.strongRecOn generalizing before after with
  | ind size ih =>
    cases trace with
    | done | breakFromBody => rfl
    | next test body next | continueNext test body next =>
      exact ih _ (Size.child_lt_stepSize (by simp)) next

theorem for_environment
    (trace : Size.ForLoop program stages size invocation context environment before test post body (.fallthrough inner) after) :
    inner = environment := by
  induction size using Nat.strongRecOn generalizing before after with
  | ind size ih =>
    cases trace with
    | finished | forBreakFromBody => rfl
    | iterate test body post next | continueIterate test body post next =>
      exact ih _ (Size.child_lt_stepSize (by simp)) next

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLoopOutcomes
