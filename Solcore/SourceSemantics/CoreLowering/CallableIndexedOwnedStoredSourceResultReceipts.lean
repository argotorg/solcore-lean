import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredSourceBundleReceipts

/-! Empty output coercions retain the authentic raw result of an indirect
Source application. Its actual successful callee trace identifies that result
with the selected closure's original result type. This is a finite Source
receipt; physical arity and native type projections remain independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredSourceResultReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

/-- The original parent typing and its real empty output path identify the
callee's result before any runtime or native representation is considered. -/
theorem original_result
    {source : TypedSource} {context : SourceSemantics.Context}
    {root callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution} {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? root = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (typed : ExpressionHasType source context root type) (empty : node.coercions = []) :
    ∃ parameter, ExpressionHasType source context callee (.function parameter type) := by
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ requirements =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    have endpoint := requirements.outputPath.foldl_target
    rw [empty, List.foldl_nil] at endpoint
    rw [form] at raw
    cases raw with
    | indirectCall calleeTyped _ _ =>
      exact ⟨_, endpoint ▸ calleeTyped⟩

/-- Genuine Source preservation at the actual callee post yields the exact
Source result equality, without a native type or packed-type inference. -/
theorem source_result_of_trace
    {program : Program} {source : TypedSource} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before calleeHeap : Dynamic.Heap} {root callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution} {node : ExpressionNode} {type : TypeSystem.Ty}
    {function : Dynamic.Closure} {size : Nat}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? root = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (typed : ExpressionHasType source context root type) (empty : node.coercions = [])
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program size context evidence source environment
      before callee (.closure function) calleeHeap) :
    type = function.resultType := by
  obtain ⟨parameter, calleeTyped⟩ := original_result unique found form typed empty
  obtain ⟨reachedTyped, _, _⟩ := wellFormed.wholeLanguagePreservation.expression context evidence source environment
    before calleeHeap callee (.closure function) (.function parameter type)
    runtime covers locals heapTyped calleeTyped calleeTrace.sound
  exact reachedTyped.closure_function_inv.2.1

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredSourceResultReceipts
