import Solcore.SourceSemantics.Staging.CallGuard
import Solcore.SourceSemantics.Dynamic.Fault

/-! An explicit staged extension of the indirect-call boundary. The plain
Dynamic judgments are unchanged. Child expressions, argument coercions and
callable application use their independent Dynamic judgments. Consequently this
module specifies the boundary order, not a recursively staged whole-program
semantics; frame propagation through children and closure calls remains required.

The frame's contract ledger is static and authenticated separately. Builtins
bypass the pre-argument stage guard. User-callable guard rejection occurs after
the callee's effects and before any argument or coercion effects. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.CallBoundary
open Frontend Frontend.SourceInference

inductive UserCallable : Dynamic.Value → Prop where
  | closure (function : Dynamic.Closure) : UserCallable (.closure function)
  | global (function : Dynamic.GlobalFunction) : UserCallable (.global function)

/-- This is a static interpretation of original callable metadata. It is not
recovered merely from the erased Core function type or its contract word. -/
structure Frame where
  stages : CallGuard.Frame
  Binds : Dynamic.Value → CallGuard.Contract → Prop
  userCallable : ∀ {value contract}, Binds value contract → UserCallable value
  unique : ∀ {value left right}, Binds value left → Binds value right → left = right

inductive GuardAccepts (frame : Frame) (call : ExpressionId) (arguments : List ExpressionId) : Dynamic.Value → Prop where
  | builtin (function : Dynamic.BuiltinFunction) : GuardAccepts frame call arguments (.builtin function)
  | contract {value contract} (bound : frame.Binds value contract)
      (accepted : CallGuard.Accepts frame.stages contract call arguments) : GuardAccepts frame call arguments value

inductive GuardRejects (frame : Frame) (call : ExpressionId) (arguments : List ExpressionId) :
    Dynamic.Value → CallGuard.Fault → Prop where
  | contract {value contract reason} (bound : frame.Binds value contract)
      (rejected : CallGuard.Rejects frame.stages contract call arguments reason) :
      GuardRejects frame call arguments value reason

theorem GuardAccepts.callable {frame : Frame} {call : ExpressionId} {arguments : List ExpressionId} {value : Dynamic.Value}
    (accepted : GuardAccepts frame call arguments value) : Dynamic.CallableValue value := by
  cases accepted with
  | builtin => trivial
  | contract bound _ => cases frame.userCallable bound <;> trivial

theorem GuardAccepts.not_rejects {frame : Frame} {call : ExpressionId} {arguments : List ExpressionId}
    {value : Dynamic.Value} {reason : CallGuard.Fault}
    (accepted : GuardAccepts frame call arguments value) (rejected : GuardRejects frame call arguments value reason) : False := by
  cases rejected with
  | contract bound rejected =>
    cases accepted with
    | builtin => cases frame.userCallable bound
    | contract other accepted =>
      cases frame.unique bound other
      exact accepted.not_rejects rejected

/-- Detailed stage diagnostics remain distinct from the mathematical source
fault carrier. The compiler bridge assigns their artifact-specific words. -/
inductive Outcome where
  | value (value : Dynamic.Value)
  | semanticFault (reason : Dynamic.SemanticFault)
  | stageFault (reason : CallGuard.Fault)
  deriving Repr

/-- The form-level call boundary, before contextual result coercions. An
accepted guard is mandatory for every rule that evaluates arguments. -/
inductive Executes (program : Program) (frame : Frame) :
    Context → Dynamic.EvidenceEnvironment → TypedSource → Dynamic.Environment → Dynamic.Heap →
      ExpressionId → ExpressionId → List ExpressionId → IndirectCallResolution → Outcome → Dynamic.Heap → Prop where
  | calleeFault {context evidence source environment before after call callee arguments metadata reason}
      (fault : Dynamic.ExpressionFaults program context evidence source environment before callee reason after) :
      Executes program frame context evidence source environment before call callee arguments metadata (.semanticFault reason) after
  | notCallable {context evidence source environment before after call callee arguments metadata callable}
      (evaluated : Dynamic.ExpressionEvaluates program context evidence source environment before callee callable after)
      (invalid : ¬ Dynamic.CallableValue callable) :
      Executes program frame context evidence source environment before call callee arguments metadata (.semanticFault .notCallable) after
  | stageRejected {context evidence source environment before after call callee arguments metadata callable reason}
      (evaluated : Dynamic.ExpressionEvaluates program context evidence source environment before callee callable after)
      (rejected : GuardRejects frame call arguments callable reason) :
      Executes program frame context evidence source environment before call callee arguments metadata (.stageFault reason) after
  | argumentsFault {context evidence source environment before calleeHeap after call callee arguments metadata callable reason}
      (calleeEvaluation : Dynamic.ExpressionEvaluates program context evidence source environment before callee callable calleeHeap)
      (accepted : GuardAccepts frame call arguments callable)
      (fault : Dynamic.ExpressionsFault program context evidence source environment calleeHeap arguments reason after) :
      Executes program frame context evidence source environment before call callee arguments metadata (.semanticFault reason) after
  | sourceArity {context evidence source environment before calleeHeap argumentsHeap call callee arguments metadata callable values}
      (calleeEvaluation : Dynamic.ExpressionEvaluates program context evidence source environment before callee callable calleeHeap)
      (accepted : GuardAccepts frame call arguments callable)
      (argumentsEvaluation : Dynamic.ExpressionsEvaluate program context evidence source environment calleeHeap arguments values argumentsHeap)
      (mismatch : metadata.argumentCount ≠ arguments.length) :
      Executes program frame context evidence source environment before call callee arguments metadata
        (.semanticFault (.argumentArityMismatch metadata.argumentCount arguments.length)) argumentsHeap
  | argumentCoercionFault {context evidence source environment before calleeHeap argumentsHeap after call callee arguments metadata
        callable values packed reason}
      (calleeEvaluation : Dynamic.ExpressionEvaluates program context evidence source environment before callee callable calleeHeap)
      (accepted : GuardAccepts frame call arguments callable)
      (argumentsEvaluation : Dynamic.ExpressionsEvaluate program context evidence source environment calleeHeap arguments values argumentsHeap)
      (arity : arguments.length = metadata.argumentCount)
      (pack : Dynamic.ValuesPack values packed)
      (fault : Dynamic.CoercionPathFaults program context evidence argumentsHeap metadata.argumentCoercions packed reason after) :
      Executes program frame context evidence source environment before call callee arguments metadata (.semanticFault reason) after
  | applied {context evidence source environment before calleeHeap argumentsHeap coercedHeap after call callee arguments metadata
        callable values packed coerced appliedArguments result invocationEvidence}
      (calleeEvaluation : Dynamic.ExpressionEvaluates program context evidence source environment before callee callable calleeHeap)
      (accepted : GuardAccepts frame call arguments callable)
      (argumentsEvaluation : Dynamic.ExpressionsEvaluate program context evidence source environment calleeHeap arguments values argumentsHeap)
      (packBefore : Dynamic.ValuesPack values packed)
      (coercions : Dynamic.CoercionPathExecutes program context evidence argumentsHeap metadata.argumentCoercions packed coerced coercedHeap)
      (packAfter : Dynamic.ValuesPack appliedArguments coerced)
      (sourceArity : arguments.length = metadata.argumentCount)
      (appliedArity : appliedArguments.length = metadata.argumentCount)
      (application : Dynamic.CallableApplies program context evidence invocationEvidence coercedHeap callable appliedArguments result after) :
      Executes program frame context evidence source environment before call callee arguments metadata (.value result) after
  | applicationFault {context evidence source environment before calleeHeap argumentsHeap coercedHeap after call callee arguments metadata
        callable values packed coerced appliedArguments reason invocationEvidence}
      (calleeEvaluation : Dynamic.ExpressionEvaluates program context evidence source environment before callee callable calleeHeap)
      (accepted : GuardAccepts frame call arguments callable)
      (argumentsEvaluation : Dynamic.ExpressionsEvaluate program context evidence source environment calleeHeap arguments values argumentsHeap)
      (packBefore : Dynamic.ValuesPack values packed)
      (coercions : Dynamic.CoercionPathExecutes program context evidence argumentsHeap metadata.argumentCoercions packed coerced coercedHeap)
      (packAfter : Dynamic.ValuesPack appliedArguments coerced)
      (sourceArity : arguments.length = metadata.argumentCount)
      (appliedArity : appliedArguments.length = metadata.argumentCount)
      (application : Dynamic.CallableFaults program context evidence invocationEvidence coercedHeap callable appliedArguments reason after) :
      Executes program frame context evidence source environment before call callee arguments metadata (.semanticFault reason) after

/-- A rejected stage guard has precisely the post-callee source heap. No
argument execution is required to construct or invert this boundary result. -/
theorem Executes.stageFault_iff {program : Program} {frame : Frame} {context : Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {call callee : ExpressionId} {arguments : List ExpressionId}
    {metadata : IndirectCallResolution} {reason : CallGuard.Fault} :
    Executes program frame context evidence source environment before call callee arguments metadata (.stageFault reason) after ↔
      ∃ callable, Dynamic.ExpressionEvaluates program context evidence source environment before callee callable after ∧
        GuardRejects frame call arguments callable reason := by
  constructor
  · intro execution
    cases execution with
    | stageRejected evaluated rejected => exact ⟨_, evaluated, rejected⟩
  · rintro ⟨callable, evaluated, rejected⟩
    exact .stageRejected evaluated rejected

/-- The accepted successful boundary projects to the existing form semantics.
The extra guard is not silently added to Dynamic by this theorem. -/
theorem Executes.value_plain {program : Program} {frame : Frame} {context : Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {call callee : ExpressionId} {arguments : List ExpressionId}
    {metadata : IndirectCallResolution} {result : Dynamic.Value} {requirements : List RequirementId}
    {coercions : List CoercionStep}
    (execution : Executes program frame context evidence source environment before call callee arguments metadata (.value result) after)
    (layout : requirements = coercionRequirementIds metadata.argumentCoercions ++ coercionRequirementIds coercions) :
    Dynamic.ExpressionFormEvaluates program context evidence source environment before
      (.call callee arguments (.indirect metadata)) requirements coercions result after := by
  cases execution with
  | applied callee _ arguments packed coerce unpacked arity appliedArity application =>
    exact .indirectCall layout callee arguments packed coerce unpacked arity appliedArity application

/-- Ordinary semantic failures also project to plain Dynamic. Stage failures
have their own constructor and deliberately have no such projection. -/
theorem Executes.semanticFault_plain {program : Program} {frame : Frame} {context : Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {call callee : ExpressionId} {arguments : List ExpressionId}
    {metadata : IndirectCallResolution} {reason : Dynamic.SemanticFault}
    (execution : Executes program frame context evidence source environment before call callee arguments metadata (.semanticFault reason) after)
    (requirements : List RequirementId) (coercions : List CoercionStep) :
    Dynamic.ExpressionFormFaults program context evidence source environment before
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

end Solcore.SourceSemantics.Staging.CallBoundary
