import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionSourceBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndirectCallBounds

/-! Original source derivations at the indirect-call boundary. The retained
children keep their own grades, caller and invocation dictionaries, ordered
arguments and every intermediate heap. Closure application keeps the actual
captured binder allocation. These inversions do not construct a callable's
catalog authority, compiler receipt or body execution meaning. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndirectCallSourceBounds
open Frontend SourceInference
open RecursiveNamedCallBounds

inductive IndirectTraceAt (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (callee : ExpressionId) (arguments : List ExpressionId)
    (metadata : IndirectCallResolution) (requirements : List RequirementId) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | calleeFault {childSize reason after}
      (child : SourceExecutionSize.ExpressionFaults program childSize context evidence source environment before callee reason after)
      (smaller : childSize < size) :
      IndirectTraceAt program size context evidence source environment before callee arguments metadata requirements (.fault reason) after
  | notCallable {childSize callable after}
      (child : SourceExecutionSize.ExpressionEvaluates program childSize context evidence source environment before callee callable after)
      (invalid : ¬ Dynamic.CallableValue callable) (smaller : childSize < size) :
      IndirectTraceAt program size context evidence source environment before callee arguments metadata requirements (.fault .notCallable) after
  | argumentsFault {calleeSize argumentsSize callable calleeHeap reason after}
      (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
      (callableShape : Dynamic.CallableValue callable)
      (argumentsTrace : SourceExecutionSize.ExpressionsFault program argumentsSize context evidence source environment calleeHeap arguments reason after)
      (calleeSmaller : calleeSize < size) (argumentsSmaller : argumentsSize < size) :
      IndirectTraceAt program size context evidence source environment before callee arguments metadata requirements (.fault reason) after
  | sourceArity {calleeSize argumentsSize callable values calleeHeap argumentsHeap}
      (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
      (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment calleeHeap arguments values argumentsHeap)
      (mismatch : metadata.argumentCount ≠ arguments.length)
      (calleeSmaller : calleeSize < size) (argumentsSmaller : argumentsSize < size) :
      IndirectTraceAt program size context evidence source environment before callee arguments metadata requirements
        (.fault (.argumentArityMismatch metadata.argumentCount arguments.length)) argumentsHeap
  | argumentCoercionFault {calleeSize argumentsSize coercionSize callable values packed calleeHeap argumentsHeap reason after}
      (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
      (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment calleeHeap arguments values argumentsHeap)
      (arity : arguments.length = metadata.argumentCount) (pack : Dynamic.ValuesPack values packed)
      (coercionTrace : SourceExecutionSize.CoercionPathFaults program coercionSize context evidence argumentsHeap metadata.argumentCoercions packed reason after)
      (calleeSmaller : calleeSize < size) (argumentsSmaller : argumentsSize < size) (coercionSmaller : coercionSize < size) :
      IndirectTraceAt program size context evidence source environment before callee arguments metadata requirements (.fault reason) after
  | applied {calleeSize argumentsSize coercionSize callSize callable values packed coerced appliedArguments
        invocationEvidence calleeHeap argumentsHeap coercedHeap result after}
      (layout : requirements = coercionRequirementIds metadata.argumentCoercions)
      (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
      (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment calleeHeap arguments values argumentsHeap)
      (packBefore : Dynamic.ValuesPack values packed)
      (coercionTrace : SourceExecutionSize.CoercionPathExecutes program coercionSize context evidence argumentsHeap metadata.argumentCoercions packed coerced coercedHeap)
      (packAfter : Dynamic.ValuesPack appliedArguments coerced)
      (sourceArity : arguments.length = metadata.argumentCount) (appliedArity : appliedArguments.length = metadata.argumentCount)
      (application : SourceExecutionSize.CallableApplies program callSize context evidence invocationEvidence coercedHeap callable appliedArguments result after)
      (calleeSmaller : calleeSize < size) (argumentsSmaller : argumentsSize < size)
      (coercionSmaller : coercionSize < size) (callSmaller : callSize < size) :
      IndirectTraceAt program size context evidence source environment before callee arguments metadata requirements (.value result) after
  | applicationFault {calleeSize argumentsSize coercionSize callSize callable values packed coerced appliedArguments
        invocationEvidence calleeHeap argumentsHeap coercedHeap reason after}
      (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
      (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment calleeHeap arguments values argumentsHeap)
      (packBefore : Dynamic.ValuesPack values packed)
      (coercionTrace : SourceExecutionSize.CoercionPathExecutes program coercionSize context evidence argumentsHeap metadata.argumentCoercions packed coerced coercedHeap)
      (packAfter : Dynamic.ValuesPack appliedArguments coerced)
      (sourceArity : arguments.length = metadata.argumentCount) (appliedArity : appliedArguments.length = metadata.argumentCount)
      (application : SourceExecutionSize.CallableFaults program callSize context evidence invocationEvidence coercedHeap callable appliedArguments reason after)
      (calleeSmaller : calleeSize < size) (argumentsSmaller : argumentsSize < size)
      (coercionSmaller : coercionSize < size) (callSmaller : callSize < size) :
      IndirectTraceAt program size context evidence source environment before callee arguments metadata requirements (.fault reason) after

/-- The wrapper's original raw child is inverted once. No child is remeasured. -/
theorem indirect_inv_sized
    {program : Program} {size : Nat} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {call callee : ExpressionId} {arguments : List ExpressionId}
    {node : ExpressionNode} {metadata : IndirectCallResolution} {outcome : Dynamic.ExpressionOutcome}
    (found : source.lookupExpression? call = some node)
    (form : node.form = .call callee arguments (.indirect metadata)) (coercions : node.coercions = [])
    (unique : NodeOccurrencesUnique source)
    (original : ExpressionOutcome program size context evidence source environment before call outcome after) :
    IndirectTraceAt program size context evidence source environment before callee arguments metadata node.requirements outcome after := by
  cases original with
  | value evaluated =>
    obtain ⟨_, raw, smaller⟩ := RecursiveNamedExpressionSourceBounds.evaluation_raw_sized unique
      (lookupExpression?_sound found) (by intros; simp [form]) coercions evaluated
    rw [form, coercions] at raw
    cases raw with
    | indirectCall layout first children packed converted unpacked arity applied application =>
      refine .applied (by simpa [coercionRequirementIds] using layout) first children packed converted unpacked arity applied application ?_ ?_ ?_ ?_
      all_goals exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
  | fault failed =>
    obtain ⟨_, raw, smaller⟩ := RecursiveNamedExpressionSourceBounds.fault_raw_sized unique
      (lookupExpression?_sound found) (by intros; simp [form]) coercions failed
    rw [form, coercions] at raw
    cases raw with
    | indirectCallee child =>
      exact .calleeFault child (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
    | indirectNotCallable child invalid =>
      exact .notCallable child invalid (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
    | indirectArguments first callable children =>
      refine .argumentsFault first callable children ?_ ?_
      all_goals exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | indirectSourceArity first children mismatch =>
      refine .sourceArity first children mismatch ?_ ?_
      all_goals exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | indirectArgumentCoercion first children arity packed failed =>
      refine .argumentCoercionFault first children arity packed failed ?_ ?_ ?_
      all_goals exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | indirectApply first children packed converted unpacked arity applied failed =>
      refine .applicationFault first children packed converted unpacked arity applied failed ?_ ?_ ?_ ?_
      all_goals exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller

inductive ClosureCompletion (program : Program) (context : SourceSemantics.Context)
    (caller invocation : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (function : Dynamic.Closure) (arguments : List Dynamic.Value) :
    Nat → Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | arity (mismatch : function.parameters.length ≠ arguments.length) :
      ClosureCompletion program context caller invocation before function arguments (SourceExecutionSize.stepSize [])
        (.fault (.argumentArityMismatch function.parameters.length arguments.length)) before
  | reached {size bodySize parameterTypes callContext environment bound outcome after}
      (sameEvidence : invocation = function.evidence) (frame : Dynamic.ClosureFrame program function)
      (parameters : MonoBindersExtend function.source.owner function.context function.parameters parameterTypes callContext)
      (allocation : Dynamic.BindersAllocate function.captured before function.parameters arguments environment bound)
      (body : BodyTrace program bodySize function callContext environment bound outcome after)
      (smaller : bodySize < size) (grade : size = SourceExecutionSize.stepSize [bodySize]) :
      ClosureCompletion program context caller invocation before function arguments size outcome after

/-- Full captured allocation and the original body child are retained directly
from each closure application constructor, including control escape. -/
theorem closure_completed_sized
    {program : Program} {size : Nat} {context : SourceSemantics.Context}
    {caller invocation : Dynamic.EvidenceEnvironment} {before after : Dynamic.Heap}
    {function : Dynamic.Closure} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (original : CallOutcome program size context caller invocation before (.closure function) arguments outcome after) :
    ClosureCompletion program context caller invocation before function arguments size outcome after := by
  cases original with
  | value applied =>
    cases applied with
    | closure same frame parameters allocation executed returned =>
      cases returned
      exact .reached same frame parameters allocation (.returned executed)
        (SourceExecutionSize.child_lt_stepSize (by simp)) rfl
    | closureUnit same frame unit parameters allocation executed fellThrough =>
      obtain ⟨_, rfl⟩ := fellThrough
      exact .reached same frame parameters allocation (.unit unit executed)
        (SourceExecutionSize.child_lt_stepSize (by simp)) rfl
  | fault failed =>
    cases failed with
    | notCallable invalid => exact False.elim (invalid trivial)
    | closureArity mismatch => exact .arity mismatch
    | closureBody same frame parameters allocation failed =>
      exact .reached same frame parameters allocation (.fault failed)
        (SourceExecutionSize.child_lt_stepSize (by simp)) rfl
    | closureControlEscape same frame parameters allocation executed escaped =>
      exact .reached same frame parameters allocation (.escaped executed escaped)
        (SourceExecutionSize.child_lt_stepSize (by simp)) rfl

end Solcore.SourceSemantics.CoreLowering.CallableIndirectCallSourceBounds
