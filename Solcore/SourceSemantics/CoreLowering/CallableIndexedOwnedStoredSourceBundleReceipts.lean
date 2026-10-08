import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCallBounds

/-! The authentic ordered Source typing row identifies the stored types of
the same argument tree. Original parent typing and the actual successful
callee trace then supply the raw closure bundle. Physical arity remains
independent; no native type or packed-type equality determines that count. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredSourceBundleReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

/-- Uniqueness aligns each independently typed Source occurrence with the
actual stored node in the argument tree. Recursion is on static Source typing. -/
theorem source_row {source : TypedSource} {context : SourceSemantics.Context}
    {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
    {ids : List ExpressionId} {types storedTypes : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionsHaveTypes source context ids types)
    (tree : DataExpressionSequence.Tree source certificate scope ids storedTypes codes) :
    types = storedTypes := by
  cases typed with
  | nil => cases tree; rfl
  | cons head tail =>
    obtain ⟨typedNode, contained, sameType⟩ := head.stored_type
    cases tree with
    | single found generated =>
      cases tail
      have sameNode := Option.some.inj ((lookupExpression?_complete unique contained).symm.trans found)
      cases sameNode
      exact congrArg (fun type => [type]) sameType.symm
    | cons found generated rest =>
      have sameNode := Option.some.inj ((lookupExpression?_complete unique contained).symm.trans found)
      cases sameNode
      rw [sameType, ← source_row unique tail rest]
termination_by ids.length

/-- Real parent typing, empty argument coercions and the actual callee post
derive the raw Source bundle at the exact selected original binder row. -/
theorem source_bundle_of_trace
    {program : Program} {source : TypedSource} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before calleeHeap : Dynamic.Heap} {root callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution} {node : ExpressionNode} {type : TypeSystem.Ty}
    {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
    {storedTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {function : Dynamic.Closure} {bindings : List CallableIndexedParameterCertificates.Binding}
    {size : Nat}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? root = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (typed : ExpressionHasType source context root type)
    (tree : DataExpressionSequence.Tree source certificate scope ids storedTypes codes)
    (empty : metadata.argumentCoercions = [])
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program size context evidence source environment
      before callee (.closure function) calleeHeap)
    (binders : bindings.map (fun binding => binding.1.scheme.body) =
      function.parameters.map (fun binder => binder.scheme.body)) :
    TypeSystem.Ty.productMany storedTypes =
      TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body)) := by
  obtain ⟨parameter, result, types, calleeTyped, argumentsTyped, application⟩ :=
    CallableIndexedOwnedStoredClosureArgumentReceipts.original_facts unique found form typed
  obtain ⟨reachedTyped, _, _⟩ := wellFormed.wholeLanguagePreservation.expression context evidence source environment
    before calleeHeap callee (.closure function) (.function parameter result)
    runtime covers locals heapTyped calleeTyped calleeTrace.sound
  have closureTypes := reachedTyped.closure_function_inv
  have row := source_row unique argumentsTyped tree
  have bundle := CallableIndexedOwnedStoredClosureArgumentReceipts.empty_bundle application empty
  rw [← row, binders]
  exact bundle.trans closureTypes.1

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredSourceBundleReceipts
