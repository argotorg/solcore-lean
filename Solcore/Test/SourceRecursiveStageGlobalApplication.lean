import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStagedCalls

/-! Independent global applications retain the selected body scope and its
full heap, including nested staging failure. These consumers require actual
source instantiation/evidence/roots and ordered allocation. The ordinary
erasure traverses the global body in the same mutual fold as callee/arguments. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceRecursiveStageGlobalApplication
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open Staging.Recursive Dynamic

theorem global_stage_failure
    {program : Program} {registry : Registry} {caller child : Scope} {context bodyContext finalContext : SourceSemantics.Context}
    {function : GlobalFunction} {bodyInstance : BodyInstance} {roots : List StatementId}
    {arguments : List Dynamic.Value} {before bound after : Dynamic.Heap} {environment : Dynamic.Environment}
    {types : List TypeSystem.Ty} {origin : Scope} {call : ExpressionId} {reason : Staging.CallGuard.Fault}
    (instantiates : FunctionInstantiates program function.instantiation bodyInstance)
    (covers : function.evidence.Covers bodyInstance.context)
    (rootsEq : StatementRoots bodyInstance.source.roots roots)
    (selected : registry.Closure (globalView bodyInstance function.evidence roots) child)
    (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs types bodyContext)
    (allocate : BindersAllocate [] before bodyInstance.source.inputs arguments environment bound)
    (body : Statements program registry child bodyContext environment bound roots finalContext
      (.fault (.stage origin call reason)) after) :
    Applies program registry caller context before (.global function) arguments
      (.fault (.stage origin call reason)) after ∧ Generated origin call reason := by
  have executed := Applies.global (scope := caller) (context := context) instantiates covers rootsEq selected parameters allocate body BodyResult.fault
  exact ⟨executed, executed.stage_origin rfl⟩

theorem global_raw_arity
    {program : Program} {registry : Registry} {caller : Scope} {context : SourceSemantics.Context}
    {function : GlobalFunction} {bodyInstance : BodyInstance} {arguments : List Dynamic.Value} {heap : Dynamic.Heap}
    (instantiates : FunctionInstantiates program function.instantiation bodyInstance)
    (mismatch : bodyInstance.source.inputs.length ≠ arguments.length) :
    Applies program registry caller context heap (.global function) arguments
      (.fault (.semantic (.argumentArityMismatch bodyInstance.source.inputs.length arguments.length))) heap :=
  .globalArity instantiates mismatch

section Erasure
variable {program : Program} {registry : Registry} {scope : Scope} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {before calleeHeap argumentsHeap after : Dynamic.Heap}
  {call callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {function : GlobalFunction} {arguments : List Dynamic.Value}
  (occurrence : Occurrence scope call (.call callee ids (.indirect metadata)))
  (uncoerced : metadata.argumentCoercions = [])
  (calleeRun : Expression program registry scope context environment before callee (.value (.global function)) calleeHeap)
  (guard : Staging.CallBoundary.GuardAccepts scope.guards call ids (.global function))
  (argumentRun : Expressions program registry scope context environment calleeHeap ids (.values arguments) argumentsHeap)
  (arity : ids.length = metadata.argumentCount)

include occurrence uncoerced calleeRun guard argumentRun arity in
theorem global_value_projects {value : Dynamic.Value}
    (invoked : Applies program registry scope context argumentsHeap (.global function) arguments (.value value) after) :
    ExpressionEvaluates program context scope.evidence scope.source environment before call value after := by
  have run := Expression.applied occurrence uncoerced calleeRun guard argumentRun arity invoked
  exact run.value_plain

include occurrence uncoerced calleeRun guard argumentRun arity in
theorem global_fault_projects {reason : SemanticFault}
    (invoked : Applies program registry scope context argumentsHeap (.global function) arguments (.fault (.semantic reason)) after) :
    ExpressionFaults program context scope.evidence scope.source environment before call reason after := by
  have run := Expression.applied occurrence uncoerced calleeRun guard argumentRun arity invoked
  exact run.semanticFault_plain
end Erasure

abbrev actual_named_view := @RecursiveNamedPreparedStagedCalls.Prepared.global_view
abbrev actual_named_scope := @RecursiveNamedPreparedStagedCalls.Prepared.selected_global
abbrev actual_named_body := @RecursiveNamedPreparedStagedCalls.Prepared.applies
abbrev actual_named_arity := @RecursiveNamedPreparedStagedCalls.Prepared.arity_failure

/-- Global views keep empty lexical captures and the exact full invocation
dictionary, independently of all native function type erasure. -/
theorem global_view_capture_and_evidence (body : BodyInstance) (evidence : EvidenceEnvironment) (roots : List StatementId) :
    (globalView body evidence roots).captured = [] ∧ (globalView body evidence roots).evidence = evidence :=
  ⟨rfl, rfl⟩
end Tests.SourceRecursiveStageGlobalApplication
