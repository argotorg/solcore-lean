import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceAdapters

/-! The ordinary accepted indirect suffix is indexed by its actual Source
callee value and invocation dictionary. Closure, global and builtin branches
use this one parent constructor. The retained CallableValue witness is supplied
by the positive callee relation. Stage rejection belongs to the separate
staged boundary, and no guard acceptance follows from declarative typing. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedIndirectValueSourceSuffix
open Core Frontend SourceInference
open CallableIndexedOwnedIndirectSourceAdapters

/-- The same ordered Source argument and application derivations retain their
independent sizes. No body outcome is stored in the compiler certificate. -/
inductive Suffix (program : Program) (context : SourceSemantics.Context)
    (caller invocation : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (ids : List ExpressionId) (function : Dynamic.Value) :
    Nat → Nat → Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | argumentFault {size reason after}
      (failed : SourceExecutionSize.ExpressionsFault program size context caller source
        environment before ids reason after) :
      Suffix program context caller invocation source environment before ids function
        size 0 (.fault reason) after
  | called {argumentsSize callSize arguments middle outcome after}
      (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context caller
        source environment before ids arguments middle)
      (called : RecursiveNamedCallBounds.CallOutcome program callSize context caller invocation
        middle function arguments outcome after) :
      Suffix program context caller invocation source environment before ids function
        argumentsSize callSize outcome after

variable {program : Program} {context : SourceSemantics.Context}
  {caller invocation : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {environment : Dynamic.Environment} {before calleeHeap after : Dynamic.Heap}
  {call callee : ExpressionId} {ids : List ExpressionId} {function : Dynamic.Value}
  {node : ExpressionNode} {metadata : IndirectCallResolution}

/-- The real accepted parent rule wraps exactly these measured children. Its
Source arity comes from actual argument preservation, with no body premise. -/
theorem Suffix.to_expression
    (found : source.lookupExpression? call = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (argumentCoercions : metadata.argumentCoercions = [])
    (sourceArity : ids.length = metadata.argumentCount)
    (callable : Dynamic.CallableValue function)
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : caller.Covers context)
    (locals : Dynamic.EnvironmentAgrees calleeHeap context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context calleeHeap)
    {types : List TypeSystem.Ty} (typed : ExpressionsHaveTypes source context ids types)
    (count : types.length = metadata.argumentCount)
    {calleeSize argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context caller source
      environment before callee function calleeHeap)
    (suffix : Suffix program context caller invocation source environment calleeHeap ids function
      argumentsSize callSize outcome after) :
    ∃ size, RecursiveNamedCallBounds.ExpressionOutcome program size context caller source
      environment before call outcome after := by
  cases suffix with
  | argumentFault failed =>
    refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [calleeSize, argumentsSize]],
      .fault (.form (lookupExpression?_sound found) ?_)⟩
    rw [form]
    exact .indirectArguments calleeTrace callable failed
  | called argumentsTrace called =>
    rename_i arguments middle
    have appliedArity := arguments_count_of_source_admission wellFormed runtime covers locals
      heapTyped typed count argumentsTrace
    obtain ⟨packed, pack⟩ := Dynamic.ValuesPack.exists_pack arguments
    cases called with
    | @value result _ applied =>
      refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize
        [calleeSize, argumentsSize, SourceExecutionSize.stepSize [], callSize],
        SourceExecutionSize.stepSize []],
        .value (.intro (raw := result) (middle := after) (lookupExpression?_sound found) ?_ ?_)⟩
      · rw [form]
        refine .indirectCall ?_ calleeTrace argumentsTrace pack ?_ pack sourceArity appliedArity applied
        · simp [requirements, argumentCoercions, coercions, coercionRequirementIds]
        · rw [argumentCoercions]; exact .nil
      · rw [coercions]; exact .nil
    | fault failed =>
      refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize
        [calleeSize, argumentsSize, SourceExecutionSize.stepSize [], callSize]],
        .fault (.form (lookupExpression?_sound found) ?_)⟩
      rw [form]
      refine .indirectApply calleeTrace argumentsTrace pack ?_ pack sourceArity appliedArity failed
      rw [argumentCoercions]; exact .nil

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedIndirectValueSourceSuffix
