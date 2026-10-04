import Solcore.SourceSemantics.CoreLowering.CallableIndirectCallSourceBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndirectCallStageBounds

/-! Original source call constructors are consumed by the new inversions.
The stage boundary tests below use an independent boundary grade. This unit
has no runtime runner or closed callable body meaning. -/

set_option autoImplicit false
namespace Tests.SourceCoreCallableIndirectCallSourceBounds
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference Solcore.SourceSemantics
open Solcore.SourceSemantics.CoreLowering
open RecursiveNamedCallBounds CallableIndirectCallSourceBounds

section OriginalIndirect
variable {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {call callee : ExpressionId} {arguments : List ExpressionId} {node : ExpressionNode}
  {metadata : IndirectCallResolution}

theorem original_callee_missing
    (found : source.lookupExpression? call = some node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (coercions : node.coercions = []) (unique : NodeOccurrencesUnique source)
    (missing : Dynamic.ExpressionMissing source callee) :
    IndirectTraceAt program 3 context evidence source environment before callee arguments metadata node.requirements
      (.fault (.missingExpression callee)) before := by
  have raw : SourceExecutionSize.ExpressionFormFaults program 2 context evidence source environment before
      node.form node.requirements node.coercions (.missingExpression callee) before := by
    rw [form]
    exact .indirectCallee (.missing missing)
  exact indirect_inv_sized found form coercions unique (.fault (.form (lookupExpression?_sound found) raw))

theorem original_not_callable {childSize : Nat} {callable : Dynamic.Value}
    (found : source.lookupExpression? call = some node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (coercions : node.coercions = []) (unique : NodeOccurrencesUnique source)
    (child : SourceExecutionSize.ExpressionEvaluates program childSize context evidence source environment before callee callable after)
    (invalid : ¬ Dynamic.CallableValue callable) :
    IndirectTraceAt program (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [childSize]])
      context evidence source environment before callee arguments metadata node.requirements (.fault .notCallable) after := by
  apply indirect_inv_sized found form coercions unique
  apply ExpressionOutcome.fault
  apply SourceExecutionSize.ExpressionFaults.form (lookupExpression?_sound found)
  rw [form]
  exact .indirectNotCallable child invalid

theorem original_arguments_fault {calleeSize argumentsSize : Nat} {callable : Dynamic.Value}
    {calleeHeap : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (found : source.lookupExpression? call = some node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (coercions : node.coercions = []) (unique : NodeOccurrencesUnique source)
    (first : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
    (callableShape : Dynamic.CallableValue callable)
    (children : SourceExecutionSize.ExpressionsFault program argumentsSize context evidence source environment calleeHeap arguments reason after) :
    IndirectTraceAt program (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [calleeSize, argumentsSize]])
      context evidence source environment before callee arguments metadata node.requirements (.fault reason) after := by
  apply indirect_inv_sized found form coercions unique
  apply ExpressionOutcome.fault
  apply SourceExecutionSize.ExpressionFaults.form (lookupExpression?_sound found)
  rw [form]
  exact .indirectArguments first callableShape children

theorem original_source_arity {calleeSize argumentsSize : Nat} {callable : Dynamic.Value}
    {calleeHeap : Dynamic.Heap} {values : List Dynamic.Value}
    (found : source.lookupExpression? call = some node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (coercions : node.coercions = []) (unique : NodeOccurrencesUnique source)
    (first : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
    (children : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment calleeHeap arguments values after)
    (mismatch : metadata.argumentCount ≠ arguments.length) :
    IndirectTraceAt program (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [calleeSize, argumentsSize]])
      context evidence source environment before callee arguments metadata node.requirements
      (.fault (.argumentArityMismatch metadata.argumentCount arguments.length)) after := by
  apply indirect_inv_sized found form coercions unique
  apply ExpressionOutcome.fault
  apply SourceExecutionSize.ExpressionFaults.form (lookupExpression?_sound found)
  rw [form]
  exact .indirectSourceArity first children mismatch

theorem original_coercion_fault {calleeSize argumentsSize coercionSize : Nat} {callable packed : Dynamic.Value}
    {calleeHeap argumentsHeap : Dynamic.Heap} {values : List Dynamic.Value} {reason : Dynamic.SemanticFault}
    (found : source.lookupExpression? call = some node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (coercions : node.coercions = []) (unique : NodeOccurrencesUnique source)
    (first : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
    (children : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment calleeHeap arguments values argumentsHeap)
    (arity : arguments.length = metadata.argumentCount) (pack : Dynamic.ValuesPack values packed)
    (failed : SourceExecutionSize.CoercionPathFaults program coercionSize context evidence argumentsHeap metadata.argumentCoercions packed reason after) :
    IndirectTraceAt program (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [calleeSize, argumentsSize, coercionSize]])
      context evidence source environment before callee arguments metadata node.requirements (.fault reason) after := by
  apply indirect_inv_sized found form coercions unique
  apply ExpressionOutcome.fault
  apply SourceExecutionSize.ExpressionFaults.form (lookupExpression?_sound found)
  rw [form]
  exact .indirectArgumentCoercion first children arity pack failed

theorem original_application_fault {calleeSize argumentsSize coercionSize callSize : Nat}
    {callable packed coerced : Dynamic.Value} {values appliedArguments : List Dynamic.Value}
    {calleeHeap argumentsHeap coercedHeap : Dynamic.Heap} {invocationEvidence : Dynamic.EvidenceEnvironment}
    {reason : Dynamic.SemanticFault}
    (found : source.lookupExpression? call = some node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (coercions : node.coercions = []) (unique : NodeOccurrencesUnique source)
    (first : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
    (children : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment calleeHeap arguments values argumentsHeap)
    (packBefore : Dynamic.ValuesPack values packed)
    (converted : SourceExecutionSize.CoercionPathExecutes program coercionSize context evidence argumentsHeap metadata.argumentCoercions packed coerced coercedHeap)
    (packAfter : Dynamic.ValuesPack appliedArguments coerced)
    (arity : arguments.length = metadata.argumentCount) (appliedArity : appliedArguments.length = metadata.argumentCount)
    (failed : SourceExecutionSize.CallableFaults program callSize context evidence invocationEvidence coercedHeap callable appliedArguments reason after) :
    IndirectTraceAt program (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [calleeSize, argumentsSize, coercionSize, callSize]])
      context evidence source environment before callee arguments metadata node.requirements (.fault reason) after := by
  apply indirect_inv_sized found form coercions unique
  apply ExpressionOutcome.fault
  apply SourceExecutionSize.ExpressionFaults.form (lookupExpression?_sound found)
  rw [form]
  exact .indirectApply first children packBefore converted packAfter arity appliedArity failed

theorem original_application_value {calleeSize argumentsSize coercionSize callSize : Nat}
    {callable packed coerced result : Dynamic.Value} {values appliedArguments : List Dynamic.Value}
    {calleeHeap argumentsHeap coercedHeap : Dynamic.Heap} {invocationEvidence : Dynamic.EvidenceEnvironment}
    (found : source.lookupExpression? call = some node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (coercions : node.coercions = []) (unique : NodeOccurrencesUnique source)
    (layout : node.requirements = coercionRequirementIds metadata.argumentCoercions)
    (first : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
    (children : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment calleeHeap arguments values argumentsHeap)
    (packBefore : Dynamic.ValuesPack values packed)
    (converted : SourceExecutionSize.CoercionPathExecutes program coercionSize context evidence argumentsHeap metadata.argumentCoercions packed coerced coercedHeap)
    (packAfter : Dynamic.ValuesPack appliedArguments coerced)
    (arity : arguments.length = metadata.argumentCount) (appliedArity : appliedArguments.length = metadata.argumentCount)
    (application : SourceExecutionSize.CallableApplies program callSize context evidence invocationEvidence coercedHeap callable appliedArguments result after) :
    IndirectTraceAt program (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [calleeSize, argumentsSize, coercionSize, callSize], 1])
      context evidence source environment before callee arguments metadata node.requirements (.value result) after := by
  apply indirect_inv_sized found form coercions unique
  apply ExpressionOutcome.value
  apply SourceExecutionSize.ExpressionEvaluates.intro (lookupExpression?_sound found)
  · rw [form]
    exact .indirectCall (by simpa [coercions, coercionRequirementIds] using layout)
      first children packBefore converted packAfter arity appliedArity application
  · rw [coercions]
    exact .nil
end OriginalIndirect

section OriginalClosure
variable {program : Program} {context : SourceSemantics.Context} {caller invocation : Dynamic.EvidenceEnvironment}
  {before bound after : Dynamic.Heap} {function : Dynamic.Closure} {arguments : List Dynamic.Value}
  {bodySize : Nat} {parameterTypes : List TypeSystem.Ty} {callContext finalContext : SourceSemantics.Context}
  {environment finalEnvironment : Dynamic.Environment}

theorem original_closure_arity (mismatch : function.parameters.length ≠ arguments.length) :
    ClosureCompletion program context caller invocation before function arguments 1
      (.fault (.argumentArityMismatch function.parameters.length arguments.length)) before :=
  closure_completed_sized (.fault (.closureArity mismatch))

theorem original_closure_returned {value : Dynamic.Value}
    (same : invocation = function.evidence) (frame : Dynamic.ClosureFrame program function)
    (parameters : MonoBindersExtend function.source.owner function.context function.parameters parameterTypes callContext)
    (allocation : Dynamic.BindersAllocate function.captured before function.parameters arguments environment bound)
    (executed : SourceExecutionSize.FunctionStatementsExecute program bodySize callContext function.evidence function.source
      environment bound function.body finalContext (.returned value) after) :
    ClosureCompletion program context caller invocation before function arguments (SourceExecutionSize.stepSize [bodySize]) (.value value) after :=
  closure_completed_sized (.value (.closure same frame parameters allocation executed rfl))

theorem original_closure_unit
    (same : invocation = function.evidence) (frame : Dynamic.ClosureFrame program function) (unit : function.resultType = .unit)
    (parameters : MonoBindersExtend function.source.owner function.context function.parameters parameterTypes callContext)
    (allocation : Dynamic.BindersAllocate function.captured before function.parameters arguments environment bound)
    (executed : SourceExecutionSize.FunctionStatementsExecute program bodySize callContext function.evidence function.source
      environment bound function.body finalContext (.fallthrough finalEnvironment) after) :
    ClosureCompletion program context caller invocation before function arguments (SourceExecutionSize.stepSize [bodySize]) (.value .unit) after :=
  closure_completed_sized (.value (.closureUnit same frame unit parameters allocation executed ⟨finalEnvironment, rfl⟩))

theorem original_closure_fault {reason : Dynamic.SemanticFault}
    (same : invocation = function.evidence) (frame : Dynamic.ClosureFrame program function)
    (parameters : MonoBindersExtend function.source.owner function.context function.parameters parameterTypes callContext)
    (allocation : Dynamic.BindersAllocate function.captured before function.parameters arguments environment bound)
    (failed : SourceExecutionSize.FunctionStatementsFault program bodySize callContext function.evidence function.source
      environment bound function.body finalContext reason after) :
    ClosureCompletion program context caller invocation before function arguments (SourceExecutionSize.stepSize [bodySize]) (.fault reason) after :=
  closure_completed_sized (.fault (.closureBody same frame parameters allocation failed))

theorem original_closure_control_escape
    (same : invocation = function.evidence) (frame : Dynamic.ClosureFrame program function)
    (parameters : MonoBindersExtend function.source.owner function.context function.parameters parameterTypes callContext)
    (allocation : Dynamic.BindersAllocate function.captured before function.parameters arguments environment bound)
    (executed : SourceExecutionSize.FunctionStatementsExecute program bodySize callContext function.evidence function.source
      environment bound function.body finalContext (.breaking finalEnvironment) after) :
    ClosureCompletion program context caller invocation before function arguments (SourceExecutionSize.stepSize [bodySize]) (.fault .controlEscapedFunction) after :=
  closure_completed_sized (.fault (.closureControlEscape same frame parameters allocation executed (Or.inl ⟨finalEnvironment, rfl⟩)))

theorem retained_captured_allocation {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (original : CallOutcome program size context caller invocation before (.closure function) arguments outcome after)
    (arity : function.parameters.length = arguments.length) :
    ∃ child types childContext childEnvironment allocated,
      invocation = function.evidence ∧ Dynamic.ClosureFrame program function ∧
      MonoBindersExtend function.source.owner function.context function.parameters types childContext ∧
      Dynamic.BindersAllocate function.captured before function.parameters arguments childEnvironment allocated ∧
      BodyTrace program child function childContext childEnvironment allocated outcome after ∧ child < size := by
  cases closure_completed_sized original with
  | arity mismatch => exact False.elim (mismatch arity)
  | reached same frame parameters allocation body smaller _ => exact ⟨_, _, _, _, _, same, frame, parameters, allocation, body, smaller⟩

theorem empty_arity_keeps_shadowed_captures {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    {name : Resolved.LocalId} {first second : Dynamic.Location} {unused : Dynamic.Environment}
    (parameters : function.parameters = [])
    (captured : function.captured = (name, first) :: (name, second) :: unused)
    (original : CallOutcome program size context caller invocation before (.closure function) [] outcome after) :
    ∃ child types childContext,
      invocation = function.evidence ∧ Dynamic.ClosureFrame program function ∧
      MonoBindersExtend function.source.owner function.context [] types childContext ∧
      BodyTrace program child function childContext ((name, first) :: (name, second) :: unused) before outcome after ∧ child < size := by
  obtain ⟨child, types, childContext, childEnvironment, allocated, same, frame, typed, allocation, body, smaller⟩ :=
    retained_captured_allocation original (by simp [parameters])
  rw [parameters] at typed
  rw [parameters, captured] at allocation
  cases allocation
  exact ⟨child, types, childContext, same, frame, typed, body, smaller⟩
end OriginalClosure

section ExistingNamedAndBuiltin
theorem original_global_child {program : Program} {instantiation : DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure}
    (unique : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (frame : NamedCalls.SourceFrame program instantiation body function)
    {size : Nat} {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (arity : function.parameters.length = arguments.length)
    (original : CallOutcome program size context caller function.evidence before
      (.global ⟨instantiation, function.evidence⟩) arguments outcome after) :
    ∃ child, BodyOutcome program child body function.evidence before arguments outcome after ∧ child < size :=
  source_call_body unique frame arity original

theorem original_builtin_pure {program : Program} {context : SourceSemantics.Context}
    {caller invocation : Dynamic.EvidenceEnvironment} {heap : Dynamic.Heap}
    {function : Dynamic.BuiltinFunction} {arguments : List Dynamic.Value} {result : Dynamic.Value}
    (applied : Dynamic.BuiltinApplies function.id arguments result) :
    CallOutcome program 1 context caller invocation heap (.builtin function) arguments (.value result) heap :=
  .value (.builtin applied)
end ExistingNamedAndBuiltin

section Boundaries
theorem boundary_grade_differs_from_wrapped_parent :
    SourceExecutionSize.stepSize [1] ≠ SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [1]] := by decide

theorem full_captured_suffix {function : Dynamic.Closure} {tail : Dynamic.Environment}
    (nonempty : tail ≠ []) : function.captured ++ tail ≠ function.captured := by
  intro equal
  have lengths := congrArg List.length equal
  have : tail.length = 0 := by simp only [List.length_append] at lengths; omega
  exact nonempty (by simpa only [List.length_eq_zero_iff] using this)
end Boundaries

end Tests.SourceCoreCallableIndirectCallSourceBounds

namespace Tests.SourceCoreCallableIndirectCallSourceBounds.Stage
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference Solcore.SourceSemantics
open Solcore.SourceSemantics.CoreLowering
open Staging.CallBoundary CallableIndirectCallStageBounds

/-- An actual rejected guard uses only the completed callee prefix. -/
theorem rejected_prefix {program : Program} {frame : Frame} {calleeSize : Nat}
    {context : Solcore.SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {call callee : ExpressionId} {arguments : List ExpressionId}
    {metadata : IndirectCallResolution} {callable : Dynamic.Value}
    {contract : Staging.CallGuard.Contract} {reason : Staging.CallGuard.Fault}
    (evaluated : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence
      source environment before callee callable after)
    (bound : frame.Binds callable contract)
    (rejected : Staging.CallGuard.Rejects frame.stages contract call arguments reason) :
    ExecutesAt program frame (SourceExecutionSize.stepSize [calleeSize]) context evidence source
      environment before call callee arguments metadata (.stageFault reason) after ∧
    Executes program frame context evidence source environment before call callee arguments
      metadata (.stageFault reason) after ∧
    calleeSize < SourceExecutionSize.stepSize [calleeSize] := by
  have boundary := ExecutesAt.stageRejected (metadata := metadata) evaluated (.contract bound rejected)
  exact ⟨boundary, boundary.sound, SourceExecutionSize.child_lt_stepSize (by simp)⟩

/-- Inversion retains the same callee witness and exact post-callee heap. -/
theorem rejected_original_child {program : Program} {frame : Frame} {size : Nat}
    {context : Solcore.SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {call callee : ExpressionId} {arguments : List ExpressionId}
    {metadata : IndirectCallResolution} {reason : Staging.CallGuard.Fault}
    (boundary : ExecutesAt program frame size context evidence source environment before
      call callee arguments metadata (.stageFault reason) after) :
    ∃ calleeSize callable, calleeSize < size ∧
      SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment
        before callee callable after ∧ GuardRejects frame call arguments callable reason := by
  obtain ⟨calleeSize, callable, _, below, evaluated, rejected⟩ := boundary.stageFault_inv
  exact ⟨calleeSize, callable, below, evaluated, rejected⟩

/-- A missing callee has boundary size two and enclosing expression size three. -/
theorem missing_callee_sizes {program : Program} {frame : Frame}
    {context : Solcore.SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {call callee : ExpressionId} {arguments : List ExpressionId}
    {metadata : IndirectCallResolution} {node : ExpressionNode}
    (contains : ContainsExpression source call node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (absent : Dynamic.ExpressionMissing source callee) :
    ExecutesAt program frame 2 context evidence source environment heap call callee arguments metadata
      (.semanticFault (.missingExpression callee)) heap ∧
    SourceExecutionSize.ExpressionFaults program 3 context evidence source environment heap call
      (.missingExpression callee) heap ∧ (2 : Nat) ≠ 3 := by
  have child : SourceExecutionSize.ExpressionFaults program 1 context evidence source environment
      heap callee (.missingExpression callee) heap := .missing absent
  have boundary : ExecutesAt program frame 2 context evidence source environment heap call callee
      arguments metadata (.semanticFault (.missingExpression callee)) heap := .calleeFault child
  have raw := boundary.semanticFault_plain_sized node.requirements node.coercions
  have original : SourceExecutionSize.ExpressionFaults program 3 context evidence source environment
      heap call (.missingExpression callee) heap :=
    .form contains (by simpa only [form] using raw)
  exact ⟨boundary, original, by decide⟩

end Tests.SourceCoreCallableIndirectCallSourceBounds.Stage
