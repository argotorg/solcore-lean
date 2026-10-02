import Solcore.SourceSemantics.CoreLowering.SourceExecutionSize
import Solcore.Test.SourceCoreRecursiveNamedCatalog

/-! These consumers use finite independent source derivations. A size is
obtained from every original rule, and actual call/loop children lie below
their containing derivation. Fault sizes also include completed successful
prefixes. Cached Core regressions retain self/mutual calls, writes and resume;
this unit does not yet prove recursive source/native correspondence. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedTraceBounds
open Solcore Frontend SourceInference SourceSemantics
open SourceSemantics.CoreLowering

#check_failure SourceTypedRuntime.run

section Leaves
variable {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {environment : Dynamic.Environment} {heap : Dynamic.Heap} {id : ExpressionId}

example : SourceExecutionSize.ExpressionsEvaluate program 1 context evidence source
    environment heap [] [] heap := .nil

example (absent : Dynamic.ExpressionMissing source id) :
    SourceExecutionSize.ExpressionFaults program 1 context evidence source environment
      heap id (.missingExpression id) heap := .missing absent
end Leaves

section Calls
variable {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {caller invocation : Dynamic.EvidenceEnvironment} {before after : Dynamic.Heap}
  {function : Dynamic.GlobalFunction} {arguments : List Dynamic.Value}
  {result : Dynamic.Value} {size : Nat}

/-- Actual named dispatch exposes its retained source body strictly below the
whole call. The instantiation fact is recovered from that dispatch. -/
theorem callee_below
    (trace : SourceExecutionSize.CallableApplies program size context caller invocation before
      (.global function) arguments result after) :
    ∃ body child,
      Dynamic.FunctionInstantiates program function.instantiation body ∧
      SourceExecutionSize.BodyInvokes program child body invocation before arguments result after ∧ child < size := by
  cases trace with
  | global instantiated _ _ invoked =>
    exact ⟨_, _, instantiated, invoked, SourceExecutionSize.child_lt_stepSize (by simp)⟩

/-- Existence is proved from the original independent dispatch, including
self or mutual calls represented by its finite body derivation. -/
theorem original_callee_below
    (trace : Dynamic.CallableApplies program context caller invocation before
      (.global function) arguments result after) :
    ∃ total body child,
      SourceExecutionSize.CallableApplies program total context caller invocation before
        (.global function) arguments result after ∧
      Dynamic.FunctionInstantiates program function.instantiation body ∧
      SourceExecutionSize.BodyInvokes program child body invocation before arguments result after ∧ child < total := by
  obtain ⟨total, sized⟩ := SourceExecutionSize.CallableApplies.has_size trace
  obtain ⟨body, child, instantiated, invoked, smaller⟩ := callee_below sized
  exact ⟨total, body, child, sized, instantiated, invoked, smaller⟩

/-- A body fault after parameter allocation remains a smaller actual child
of the source named-call fault rule. -/
theorem fault_callee_below {body : Dynamic.BodyInstance} {reason : Dynamic.SemanticFault}
    (instantiated : Dynamic.FunctionInstantiates program function.instantiation body)
    (same : invocation = function.evidence)
    (trace : SourceExecutionSize.BodyFaults program size body invocation before arguments reason after) :
    ∃ total,
      SourceExecutionSize.CallableFaults program total context caller invocation before
        (.global function) arguments reason after ∧ size < total :=
  ⟨_, .globalBody instantiated same trace, SourceExecutionSize.child_lt_stepSize (by simp)⟩
end Calls

section Prefixes
variable {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
  {before middle after : Dynamic.Heap} {id : ExpressionId} {ids : List ExpressionId}
  {value : Dynamic.Value} {reason : Dynamic.SemanticFault}

/-- The preceding successful expression is counted even when the rest of
the ordered argument vector faults. Both original children erase unchanged. -/
theorem successful_prefix_in_fault
    (head : Dynamic.ExpressionEvaluates program context evidence source environment before id value middle)
    (tail : Dynamic.ExpressionsFault program context evidence source environment middle ids reason after) :
    ∃ total first second,
      SourceExecutionSize.ExpressionsFault program total context evidence source environment before (id :: ids) reason after ∧
      SourceExecutionSize.ExpressionEvaluates program first context evidence source environment before id value middle ∧
      SourceExecutionSize.ExpressionsFault program second context evidence source environment middle ids reason after ∧
      first < total ∧ second < total := by
  obtain ⟨first, head⟩ := SourceExecutionSize.ExpressionEvaluates.has_size head
  obtain ⟨second, tail⟩ := SourceExecutionSize.ExpressionsFault.has_size tail
  exact ⟨_, first, second, .tail head tail, head, tail,
    SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp)⟩

/-- Escaped control is a fault rule containing a successful body derivation.
That successful premise is retained rather than treated as a leaf. -/
theorem escaped_success_is_counted
    {body : Dynamic.BodyInstance} {arguments : List Dynamic.Value} {roots : List StatementId}
    {inputTypes : List TypeSystem.Ty} {lexicalContext finalContext : SourceSemantics.Context}
    {bound : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (root : Dynamic.StatementRoots body.source.roots roots)
    (inputs : MonoBindersExtend body.source.owner body.context body.source.inputs inputTypes lexicalContext)
    (allocate : Dynamic.BindersAllocate [] before body.source.inputs arguments environment bound)
    (execute : Dynamic.FunctionStatementsExecute program lexicalContext evidence body.source
      environment bound roots finalContext outcome after)
    (escaped : (∃ env, outcome = .breaking env) ∨ (∃ env, outcome = .continuing env)) :
    ∃ total child,
      SourceExecutionSize.BodyFaults program total body evidence before arguments .controlEscapedFunction after ∧
      SourceExecutionSize.FunctionStatementsExecute program child lexicalContext evidence body.source
        environment bound roots finalContext outcome after ∧ child < total := by
  obtain ⟨child, execute⟩ := SourceExecutionSize.FunctionStatementsExecute.has_size execute
  exact ⟨_, child, .controlEscape root inputs allocate execute escaped, execute,
    SourceExecutionSize.child_lt_stepSize (by simp)⟩
end Prefixes

section Loops
variable {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
  {before conditionHeap bodyHeap postHeap after : Dynamic.Heap} {condition : ExpressionId}
  {body : List StatementId} {post : List ForItemForm}
  {bodyContext postContext : SourceSemantics.Context} {bodyEnvironment postEnvironment : Dynamic.Environment}
  {outcome : Dynamic.ControlOutcome} {reason : Dynamic.SemanticFault}

/-- A continuing source for loop counts condition, body, post and the next
iteration as separate actual children, in execution order. -/
theorem for_continue_children
    (conditionTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      before condition (.bool true) conditionHeap)
    (bodyTrace : Dynamic.StatementsExecute program context evidence source environment
      conditionHeap body bodyContext (.continuing bodyEnvironment) bodyHeap)
    (postTrace : Dynamic.ForItemsExecute program context evidence source environment
      bodyHeap post postContext postEnvironment postHeap)
    (nextTrace : Dynamic.ForLoopExecutes program context evidence source environment
      postHeap condition post body context outcome after) :
    ∃ total c b p n,
      SourceExecutionSize.ForLoopExecutes program total context evidence source environment before
        condition post body context outcome after ∧
      SourceExecutionSize.ExpressionEvaluates program c context evidence source environment before
        condition (.bool true) conditionHeap ∧
      SourceExecutionSize.StatementsExecute program b context evidence source environment conditionHeap
        body bodyContext (.continuing bodyEnvironment) bodyHeap ∧
      SourceExecutionSize.ForItemsExecute program p context evidence source environment bodyHeap
        post postContext postEnvironment postHeap ∧
      SourceExecutionSize.ForLoopExecutes program n context evidence source environment postHeap
        condition post body context outcome after ∧ c < total ∧ b < total ∧ p < total ∧ n < total := by
  obtain ⟨c, conditionTrace⟩ := SourceExecutionSize.ExpressionEvaluates.has_size conditionTrace
  obtain ⟨b, bodyTrace⟩ := SourceExecutionSize.StatementsExecute.has_size bodyTrace
  obtain ⟨p, postTrace⟩ := SourceExecutionSize.ForItemsExecute.has_size postTrace
  obtain ⟨n, nextTrace⟩ := SourceExecutionSize.ForLoopExecutes.has_size nextTrace
  exact ⟨_, c, b, p, n, .nextContinue conditionTrace bodyTrace postTrace nextTrace,
    conditionTrace, bodyTrace, postTrace, nextTrace,
    SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp),
    SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp)⟩

/-- A later loop fault still counts all three successful prefixes. It is
strictly smaller than the parent without claiming equal source/Core cost. -/
theorem for_later_fault_children
    (conditionTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      before condition (.bool true) conditionHeap)
    (bodyTrace : Dynamic.StatementsExecute program context evidence source environment
      conditionHeap body bodyContext (.fallthrough bodyEnvironment) bodyHeap)
    (postTrace : Dynamic.ForItemsExecute program context evidence source environment
      bodyHeap post postContext postEnvironment postHeap)
    (nextTrace : Dynamic.ForLoopFaults program context evidence source environment
      postHeap condition post body reason after) :
    ∃ total c b p n,
      SourceExecutionSize.ForLoopFaults program total context evidence source environment before condition post body reason after ∧
      c < total ∧ b < total ∧ p < total ∧ n < total ∧
      SourceExecutionSize.ExpressionEvaluates program c context evidence source environment before condition (.bool true) conditionHeap ∧
      SourceExecutionSize.StatementsExecute program b context evidence source environment conditionHeap body bodyContext
        (.fallthrough bodyEnvironment) bodyHeap ∧
      SourceExecutionSize.ForItemsExecute program p context evidence source environment bodyHeap post postContext postEnvironment postHeap ∧
      SourceExecutionSize.ForLoopFaults program n context evidence source environment postHeap condition post body reason after := by
  obtain ⟨c, conditionTrace⟩ := SourceExecutionSize.ExpressionEvaluates.has_size conditionTrace
  obtain ⟨b, bodyTrace⟩ := SourceExecutionSize.StatementsExecute.has_size bodyTrace
  obtain ⟨p, postTrace⟩ := SourceExecutionSize.ForItemsExecute.has_size postTrace
  obtain ⟨n, nextTrace⟩ := SourceExecutionSize.ForLoopFaults.has_size nextTrace
  exact ⟨_, c, b, p, n, .nextFallthrough conditionTrace bodyTrace postTrace nextTrace,
    SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp),
    SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp),
    conditionTrace, bodyTrace, postTrace, nextTrace⟩

/-- While body effects and its later fault also use the same measure. -/
theorem while_later_fault_children
    (conditionTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      before condition (.bool true) conditionHeap)
    (bodyTrace : Dynamic.StatementsExecute program context evidence source environment
      conditionHeap body bodyContext (.fallthrough bodyEnvironment) bodyHeap)
    (nextTrace : Dynamic.WhileFaults program context evidence source environment
      bodyHeap condition body reason after) :
    ∃ total c b n,
      SourceExecutionSize.WhileFaults program total context evidence source environment before condition body reason after ∧
      SourceExecutionSize.ExpressionEvaluates program c context evidence source environment before condition (.bool true) conditionHeap ∧
      SourceExecutionSize.StatementsExecute program b context evidence source environment conditionHeap body bodyContext
        (.fallthrough bodyEnvironment) bodyHeap ∧
      SourceExecutionSize.WhileFaults program n context evidence source environment bodyHeap condition body reason after ∧
      c < total ∧ b < total ∧ n < total := by
  obtain ⟨c, conditionTrace⟩ := SourceExecutionSize.ExpressionEvaluates.has_size conditionTrace
  obtain ⟨b, bodyTrace⟩ := SourceExecutionSize.StatementsExecute.has_size bodyTrace
  obtain ⟨n, nextTrace⟩ := SourceExecutionSize.WhileFaults.has_size nextTrace
  exact ⟨_, c, b, n, .nextFallthrough conditionTrace bodyTrace nextTrace,
    conditionTrace, bodyTrace, nextTrace, SourceExecutionSize.child_lt_stepSize (by simp),
    SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp)⟩
end Loops

def run : IO Unit := do
  Tests.SourceCoreRecursiveNamedCatalog.run
  IO.println "recursive named trace bounds: all 40 source judgment bridges; strict actual call/body/loop children and successful fault prefixes GREEN"

end Tests.SourceCoreRecursiveNamedTraceBounds
