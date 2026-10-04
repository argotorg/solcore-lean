import Solcore.SourceSemantics.Staging.CallBoundary
import Solcore.SourceSemantics.CoreLowering.SourceExecutionSize

/-! An indirect stage boundary carrying the sizes of its existing dynamic
premises. Static guards keep the same contract and source metadata. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndirectCallStageBounds
open Frontend Frontend.SourceInference Staging.CallBoundary
open SourceExecutionSize (stepSize child_lt_stepSize)

inductive ExecutesAt (program : Program) (frame : Frame) : Nat →
    Context → Dynamic.EvidenceEnvironment → TypedSource → Dynamic.Environment → Dynamic.Heap →
      ExpressionId → ExpressionId → List ExpressionId → IndirectCallResolution → Outcome → Dynamic.Heap → Prop where
  | calleeFault {calleeSize : Nat}
      {context evidence source environment before after call callee arguments metadata reason}
      (fault : SourceExecutionSize.ExpressionFaults program calleeSize context evidence source environment before callee reason after) :
      ExecutesAt program frame (stepSize [calleeSize]) context evidence source environment before call callee arguments metadata (.semanticFault reason) after
  | notCallable {calleeSize : Nat}
      {context evidence source environment before after call callee arguments metadata callable}
      (evaluated : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable after)
      (invalid : ¬ Dynamic.CallableValue callable) :
      ExecutesAt program frame (stepSize [calleeSize]) context evidence source environment before call callee arguments metadata (.semanticFault .notCallable) after
  | stageRejected {calleeSize : Nat}
      {context evidence source environment before after call callee arguments metadata callable reason}
      (evaluated : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable after)
      (rejected : GuardRejects frame call arguments callable reason) :
      ExecutesAt program frame (stepSize [calleeSize]) context evidence source environment before call callee arguments metadata (.stageFault reason) after
  | argumentsFault {calleeSize argumentsSize : Nat}
      {context evidence source environment before calleeHeap after call callee arguments metadata callable reason}
      (calleeEvaluation : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
      (accepted : GuardAccepts frame call arguments callable)
      (fault : SourceExecutionSize.ExpressionsFault program argumentsSize context evidence source environment calleeHeap arguments reason after) :
      ExecutesAt program frame (stepSize [calleeSize, argumentsSize]) context evidence source environment before call callee arguments metadata (.semanticFault reason) after
  | sourceArity {calleeSize argumentsSize : Nat}
      {context evidence source environment before calleeHeap argumentsHeap call callee arguments metadata callable values}
      (calleeEvaluation : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
      (accepted : GuardAccepts frame call arguments callable)
      (argumentsEvaluation : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment calleeHeap arguments values argumentsHeap)
      (mismatch : metadata.argumentCount ≠ arguments.length) :
      ExecutesAt program frame (stepSize [calleeSize, argumentsSize]) context evidence source environment before call callee arguments metadata
        (.semanticFault (.argumentArityMismatch metadata.argumentCount arguments.length)) argumentsHeap
  | argumentCoercionFault {calleeSize argumentsSize coercionsSize : Nat}
      {context evidence source environment before calleeHeap argumentsHeap after call callee arguments metadata
        callable values packed reason}
      (calleeEvaluation : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
      (accepted : GuardAccepts frame call arguments callable)
      (argumentsEvaluation : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment calleeHeap arguments values argumentsHeap)
      (arity : arguments.length = metadata.argumentCount)
      (pack : Dynamic.ValuesPack values packed)
      (fault : SourceExecutionSize.CoercionPathFaults program coercionsSize context evidence argumentsHeap metadata.argumentCoercions packed reason after) :
      ExecutesAt program frame (stepSize [calleeSize, argumentsSize, coercionsSize]) context evidence source environment before call callee arguments metadata (.semanticFault reason) after
  | applied {calleeSize argumentsSize coercionsSize applicationSize : Nat}
      {context evidence source environment before calleeHeap argumentsHeap coercedHeap after call callee arguments metadata
        callable values packed coerced appliedArguments result invocationEvidence}
      (calleeEvaluation : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
      (accepted : GuardAccepts frame call arguments callable)
      (argumentsEvaluation : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment calleeHeap arguments values argumentsHeap)
      (packBefore : Dynamic.ValuesPack values packed)
      (coercions : SourceExecutionSize.CoercionPathExecutes program coercionsSize context evidence argumentsHeap metadata.argumentCoercions packed coerced coercedHeap)
      (packAfter : Dynamic.ValuesPack appliedArguments coerced)
      (sourceArity : arguments.length = metadata.argumentCount)
      (appliedArity : appliedArguments.length = metadata.argumentCount)
      (application : SourceExecutionSize.CallableApplies program applicationSize context evidence invocationEvidence coercedHeap callable appliedArguments result after) :
      ExecutesAt program frame (stepSize [calleeSize, argumentsSize, coercionsSize, applicationSize]) context evidence source environment before call callee arguments metadata (.value result) after
  | applicationFault {calleeSize argumentsSize coercionsSize applicationSize : Nat}
      {context evidence source environment before calleeHeap argumentsHeap coercedHeap after call callee arguments metadata
        callable values packed coerced appliedArguments reason invocationEvidence}
      (calleeEvaluation : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
      (accepted : GuardAccepts frame call arguments callable)
      (argumentsEvaluation : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment calleeHeap arguments values argumentsHeap)
      (packBefore : Dynamic.ValuesPack values packed)
      (coercions : SourceExecutionSize.CoercionPathExecutes program coercionsSize context evidence argumentsHeap metadata.argumentCoercions packed coerced coercedHeap)
      (packAfter : Dynamic.ValuesPack appliedArguments coerced)
      (sourceArity : arguments.length = metadata.argumentCount)
      (appliedArity : appliedArguments.length = metadata.argumentCount)
      (application : SourceExecutionSize.CallableFaults program applicationSize context evidence invocationEvidence coercedHeap callable appliedArguments reason after) :
      ExecutesAt program frame (stepSize [calleeSize, argumentsSize, coercionsSize, applicationSize]) context evidence source environment before call callee arguments metadata (.semanticFault reason) after

namespace ExecutesAt

variable {program : Program} {frame : Frame} {size : Nat} {context : Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {call callee : ExpressionId} {arguments : List ExpressionId}
  {metadata : IndirectCallResolution} {outcome : Outcome}

/-- Retain the original boundary and all its intermediate heaps. -/
theorem sound
    (execution : ExecutesAt program frame size context evidence source environment before
      call callee arguments metadata outcome after) :
    Executes program frame context evidence source environment before
      call callee arguments metadata outcome after := by
  cases execution with
  | calleeFault fault => exact .calleeFault fault.sound
  | notCallable evaluated invalid => exact .notCallable evaluated.sound invalid
  | stageRejected evaluated rejected => exact .stageRejected evaluated.sound rejected
  | argumentsFault evaluated accepted fault =>
    exact .argumentsFault evaluated.sound accepted fault.sound
  | sourceArity evaluated accepted arguments mismatch =>
    exact .sourceArity evaluated.sound accepted arguments.sound mismatch
  | argumentCoercionFault evaluated accepted arguments arity packed fault =>
    exact .argumentCoercionFault evaluated.sound accepted arguments.sound arity packed fault.sound
  | applied evaluated accepted arguments packed converted unpacked arity applied application =>
    exact .applied evaluated.sound accepted arguments.sound packed converted.sound unpacked
      arity applied application.sound
  | applicationFault evaluated accepted arguments packed converted unpacked arity applied fault =>
    exact .applicationFault evaluated.sound accepted arguments.sound packed converted.sound unpacked
      arity applied fault.sound

/-- Each immediate dynamic premise has a smaller size than this boundary. -/
theorem children_below
    (execution : ExecutesAt program frame size context evidence source environment before
      call callee arguments metadata outcome after) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases execution <;> exact ⟨_, rfl, fun _ member => child_lt_stepSize member⟩

/-- Rejection keeps the original callee size and its entire final heap. -/
theorem stageFault_inv {reason : Staging.CallGuard.Fault}
    (execution : ExecutesAt program frame size context evidence source environment before
      call callee arguments metadata (.stageFault reason) after) :
    ∃ calleeSize callable, size = stepSize [calleeSize] ∧ calleeSize < size ∧
      SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment
        before callee callable after ∧ GuardRejects frame call arguments callable reason := by
  cases execution with
  | stageRejected evaluated rejected =>
    exact ⟨_, _, rfl, child_lt_stepSize (by simp), evaluated, rejected⟩

/-- The same dynamic premises construct the plain form result at this size. -/
theorem value_plain_sized {result : Dynamic.Value} {requirements : List RequirementId}
    {coercions : List CoercionStep}
    (execution : ExecutesAt program frame size context evidence source environment before
      call callee arguments metadata (.value result) after)
    (layout : requirements = coercionRequirementIds metadata.argumentCoercions ++
      coercionRequirementIds coercions) :
    SourceExecutionSize.ExpressionFormEvaluates program size context evidence source environment before
      (.call callee arguments (.indirect metadata)) requirements coercions result after := by
  cases execution with
  | applied evaluated _ arguments packed converted unpacked arity applied application =>
    exact .indirectCall layout evaluated arguments packed converted unpacked arity applied application

/-- The same failing premise constructs the plain form fault at this size. -/
theorem semanticFault_plain_sized {reason : Dynamic.SemanticFault}
    (execution : ExecutesAt program frame size context evidence source environment before
      call callee arguments metadata (.semanticFault reason) after)
    (requirements : List RequirementId) (coercions : List CoercionStep) :
    SourceExecutionSize.ExpressionFormFaults program size context evidence source environment before
      (.call callee arguments (.indirect metadata)) requirements coercions reason after := by
  cases execution with
  | calleeFault fault => exact .indirectCallee fault
  | notCallable evaluated invalid => exact .indirectNotCallable evaluated invalid
  | argumentsFault evaluated accepted fault => exact .indirectArguments evaluated accepted.callable fault
  | sourceArity evaluated _ arguments mismatch => exact .indirectSourceArity evaluated arguments mismatch
  | argumentCoercionFault evaluated _ arguments arity packed fault =>
    exact .indirectArgumentCoercion evaluated arguments arity packed fault
  | applicationFault evaluated _ arguments packed converted unpacked arity applied fault =>
    exact .indirectApply evaluated arguments packed converted unpacked arity applied fault

end ExecutesAt
end Solcore.SourceSemantics.CoreLowering.CallableIndirectCallStageBounds
