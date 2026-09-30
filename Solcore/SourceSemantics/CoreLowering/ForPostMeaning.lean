import Solcore.SourceSemantics.CoreLowering.ForHeaderConstruction

/-! A certified post vector finishes or raises its specified scalar read
fault. Its final lexical bindings are recorded in independent source semantics
and can be discarded when the next loop iteration restores its captured scope. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ForHeaders

open Frontend Frontend.SourceInference TypeSystem LocalCell CoreProof LoopStatements

inductive PostMeaning (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (items : List ForItemForm) (type : Core.Ty) :
    Context → Dynamic.ControlOutcome → Dynamic.Heap → Core.Value → Prop where
  | success {finalContext finalEnvironment after}
      (execution : Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after) :
      PostMeaning program context evidence source reasonAt environment before items type finalContext
        (.fallthrough finalEnvironment) after (Core.LocalLoop.fallthroughValue type)
  | fault {finalContext reason word after}
      (fault : Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after)
      (related : Internal.FaultRepresents program evidence source reasonAt reason word) :
      PostMeaning program context evidence source reasonAt environment before items type finalContext
        (.fault reason) after (.inLeft (Core.LocalLoop.controlType type) (.word word))

def PostResult (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (items : List ForItemForm) (type : Core.Ty)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping)
    (actual : Core.Environment) (store : Core.Store) (code : Core.Expr) : Prop :=
  ∃ finalContext outcome after result finalStore finalMap finalWorld,
    PostMeaning program context evidence source reasonAt environment before items type finalContext outcome after result ∧
    Core.Evaluates actual store code result finalStore ∧
    GeneralHeap.HeapRepresents finalMap finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMap ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMap finalStore

theorem Tree.construct_post
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {reasonAt : ExpressionId → Core.Word}
    {resultType : Core.Ty} {scope : SourceCoreLocalCell.Scope} {context : Context} {items : List ForItemForm} {code : Core.Expr}
    (tree : Tree compilation source reasonAt resultType (Fallthrough resultType) scope context items code)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap : Dynamic.Heap} {store : Core.Store}
    (valid : PrimitiveExpressions.ContextValid compilation context)
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ) :
    PostResult program context evidence source reasonAt environment heap items resultType mapping world actual store (code.rename ξ) := by
  have constructed := tree.construct program evidence valid environments heaps layout
  cases constructed with
  | continues tail execution _ maps worlds frame agreement =>
    have endpoint : tail.code = Core.LocalLoop.fallthrough resultType := tail.certificate
    have completed : Core.Evaluates tail.actual tail.store (tail.code.rename tail.embedding)
        (Core.LocalLoop.fallthroughValue resultType) tail.store := by
      rw [endpoint, Core.LoopRenaming.fallthrough]
      exact Core.LocalLoop.fallthrough_evaluates _ _ _
    exact ⟨tail.context, _, tail.heap, _, tail.store, tail.mapping, tail.world,
      .success execution, agreement.wrap completed, tail.heaps, maps, worlds, frame⟩
  | @fault finalContext reason word after finalMap finalWorld finalStore fault related heaps maps worlds frame evaluation =>
    exact ⟨finalContext, _, after, _, finalStore, finalMap, finalWorld,
      .fault fault related, evaluation, heaps, maps, worlds, frame⟩

end Solcore.SourceSemantics.CoreLowering.ForHeaders
