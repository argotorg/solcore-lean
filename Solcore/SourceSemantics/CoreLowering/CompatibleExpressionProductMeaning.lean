import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProductSource

/-! Whole finite product trees discharge the universal child interfaces.
The existing argument sequence theorem inserts actual payload slots and
composes heap/world/admin preservation. Its child obligations are proved here
by structural induction, rather than supplied by the final caller. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProducts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

private def Two (scope : Scope) (left right : ExpressionId) (first second : SourceCoreBasic.LoweredExpr) :
    GenericExpressionMeaning.Certificate := fun current id code =>
  current = scope ∧ ((id = left ∧ code = first) ∨ (id = right ∧ code = second))

private theorem two_tree {source : TypedSource} {scope : Scope} {left right : ExpressionId}
    {leftNode rightNode : ExpressionNode} {first second : SourceCoreBasic.LoweredExpr}
    (leftFound : source.lookupExpression? left = some leftNode)
    (rightFound : source.lookupExpression? right = some rightNode) :
    DataExpressionSequence.Tree source (Two scope left right first second) scope
      [left, right] [leftNode.type, rightNode.type] [first, second] :=
  .cons leftFound ⟨rfl, .inl ⟨rfl, rfl⟩⟩ (.single rightFound ⟨rfl, .inr ⟨rfl, rfl⟩⟩)

private theorem pair_result {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {leftType rightType : TypeSystem.Ty}
    {first second : SourceCoreBasic.LoweredExpr} {faults : FunctionCalls.FaultRep}
    {sequence : DataExpressionSequence.Outcome} {value : Value}
    (result : DataExpressionSequence.Result (CompatibleAmbientHeap.payloadModel checked registry functions)
      mapping world [leftType, rightType] [first, second] faults sequence value) :
    ∃ outcome, PacksOutcome sequence outcome ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked registry functions)
        mapping world (.product leftType rightType) (.product first.type second.type) faults outcome value := by
  cases result with
  | values represented =>
    change DataExpressionSequence.Values _ _ _ [leftType, rightType] [first.type, second.type] _ _ at represented
    cases represented with
    | cons left tail =>
      cases tail with
      | cons right tail =>
        cases tail
        exact ⟨_, .values (.cons (.singleton _)), .value (.product left right)⟩
  | fault matched => exact ⟨_, .fault _, .fault matched⟩

variable {fuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))

include extension valid unique uninitialized in
/-- Every independent completed source execution is preserved for the entire
certified tree. There is no external child semantic hypothesis. -/
theorem preserves :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  intro scope id lowered tree
  induction tree with
  | literal receipt =>
    exact CompatibleExpressionLiterals.preserves functions program context evidence valid unique faults receipt
  | read receipt =>
    exact CompatibleExpressionReads.loweredRead_preserves functions extension program context evidence reasonAt uninitialized unique receipt
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
    intro root found mapping world administrative environment canonical actual before store ξ outcome after
      environments heaps locals agrees trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
      ih innerFound environments heaps locals agrees (group_inv metadata form unique trace)
    refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
    simpa only [sourceType] using represented
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstTree secondTree leftIH rightIH =>
    intro root found mapping world administrative environment canonical actual before store ξ outcome after
      environments heaps locals agrees trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have children : GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Two scope left right first second) faults := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH
      · exact rightIH
    obtain ⟨sequence, sourceTrace, packed⟩ := pair_inv metadata form unique trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
      (two_tree (first := first) (second := second) leftFound rightFound).preserves children environments heaps locals agrees sourceTrace
    obtain ⟨actualOutcome, actualPack, payload⟩ := pair_result represented
    have sameOutcome := actualPack.functional packed
    subst actualOutcome
    refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
    simpa only [sourceType] using payload

include extension valid uninitialized in
/-- Every native completion reconstructs the independent source execution of
the whole tree, including a fault after an effectful successful left prefix. -/
theorem reflects :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  intro scope id lowered tree
  induction tree with
  | literal receipt =>
    exact CompatibleExpressionLiterals.reflects functions program context evidence valid source faults receipt
  | read receipt =>
    exact CompatibleExpressionReads.loweredRead_reflects functions extension program context evidence reasonAt uninitialized receipt
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
    intro root found mapping world administrative environment canonical actual before store ξ value finalStore
      environments heaps locals agrees evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
      ih innerFound environments heaps locals agrees evaluated
    refine ⟨outcome, after, finalMap, finalWorld, group_intro metadata form trace, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
    simpa only [sourceType] using represented
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstTree secondTree leftIH rightIH =>
    intro root found mapping world administrative environment canonical actual before store ξ value finalStore
      environments heaps locals agrees evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have children : GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Two scope left right first second) faults := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH
      · exact rightIH
    obtain ⟨sequence, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
      (two_tree (first := first) (second := second) leftFound rightFound).reflects children environments heaps locals agrees evaluated
    obtain ⟨outcome, packed, payload⟩ := pair_result represented
    refine ⟨outcome, after, finalMap, finalWorld, pair_intro metadata form sourceTrace packed, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
    simpa only [sourceType] using payload

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProducts
