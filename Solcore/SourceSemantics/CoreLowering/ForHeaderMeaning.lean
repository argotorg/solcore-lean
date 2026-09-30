import Solcore.SourceSemantics.CoreLowering.ForHeaderTree
import Solcore.SourceSemantics.CoreLowering.LoopStatementReconstruction
import Solcore.SourceSemantics.CoreLowering.CoreContinuationAgreement

/-! Execute only a finite scalar/product header prefix in independent source
semantics. Its static continuation is preserved as an unevaluated Core hole:
finite evaluations can be composed around it and recovered from the whole
header. The loop itself is never evaluated by this construction. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ForHeaders

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements CoreProof
open LoopStatements

structure TailState (administrativeContext : Core.Context)
    (continuation : SourceCoreLocalCell.Scope → Context → Core.Expr → Prop) where
  scope : SourceCoreLocalCell.Scope
  context : Context
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  mapping : GeneralHeap.LocationMap
  world : Core.StoreTyping
  canonical : Core.Environment
  actual : Core.Environment
  actualContext : Core.Context
  embedding : Core.Renaming
  store : Core.Store
  code : Core.Expr
  certificate : continuation scope context code
  environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical
  heaps : GeneralHeap.HeapRepresents mapping world heap store
  layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual embedding

/-- A header only adds lexical binders to its context. This records the
source binder derivation needed to transport ledger validity and evidence. -/
def ContextExtends (owner : Resolved.DeclarationId) (before after : Context) : Prop :=
  ∃ binders, BindersExtend owner before binders after

namespace ContextExtends

theorem refl (owner : Resolved.DeclarationId) (context : Context) : ContextExtends owner context context :=
  ⟨[], .nil _⟩

theorem binder {owner : Resolved.DeclarationId} {before after : Context} {binder : TypedBinder}
    (extension : BinderExtends owner before binder after) : ContextExtends owner before after :=
  ⟨[binder], .cons extension (.nil _)⟩

private theorem append {owner : Resolved.DeclarationId} {before middle after : Context}
    {left right : List TypedBinder} (first : BindersExtend owner before left middle)
    (second : BindersExtend owner middle right after) : BindersExtend owner before (left ++ right) after := by
  induction first with
  | nil => exact second
  | cons head _ tail => exact .cons head (tail second)

theorem trans {owner : Resolved.DeclarationId} {before middle after : Context}
    (first : ContextExtends owner before middle) (second : ContextExtends owner middle after) :
    ContextExtends owner before after := by
  obtain ⟨left, first⟩ := first
  obtain ⟨right, second⟩ := second
  exact ⟨left ++ right, append first second⟩

theorem valid {owner : Resolved.DeclarationId} {before after : Context} {compilation : SourceCorePrimitive.Context}
    (extension : ContextExtends owner before after) (valid : PrimitiveExpressions.ContextValid compilation before) :
    PrimitiveExpressions.ContextValid compilation after := by
  obtain ⟨binders, extension⟩ := extension
  induction extension with
  | nil => exact valid
  | cons head _ tail =>
    apply tail
    cases head
    exact ⟨valid.ledger, valid.valid.transport rfl rfl rfl⟩

theorem covers {owner : Resolved.DeclarationId} {before after : Context} {evidence : Dynamic.EvidenceEnvironment}
    (extension : ContextExtends owner before after) (covers : evidence.Covers before) : evidence.Covers after := by
  obtain ⟨binders, extension⟩ := extension
  exact covers.transportBinders extension

end ContextExtends

inductive Result (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (resultType : Core.Ty)
    (continuation : SourceCoreLocalCell.Scope → Context → Core.Expr → Prop) (administrativeContext : Core.Context)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) (items : List ForItemForm)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping)
    (actual : Core.Environment) (store : Core.Store) (code : Core.Expr) : Prop where
  | continues (tail : TailState administrativeContext continuation)
      (execution : Dynamic.ForItemsExecute program context evidence source environment heap items
        tail.context tail.environment tail.heap)
      (contextExtension : ContextExtends source.owner context tail.context)
      (maps : GeneralHeap.LocationMap.Extends mapping tail.mapping)
      (worlds : Core.WorldExtends world tail.world)
      (frame : GeneralHeap.AdministrativePreserved mapping store tail.mapping tail.store)
      (agreement : ContinuationAgreement actual store code tail.actual tail.store (tail.code.rename tail.embedding)) :
      Result program context evidence source reasonAt resultType continuation administrativeContext environment heap items mapping world actual store code
  | fault {finalContext reason word after finalMap finalWorld finalStore}
      (fault : Dynamic.ForItemsFault program context evidence source environment heap items finalContext reason after)
      (related : Internal.FaultRepresents program evidence source reasonAt reason word)
      (heaps : GeneralHeap.HeapRepresents finalMap finalWorld after finalStore)
      (maps : GeneralHeap.LocationMap.Extends mapping finalMap)
      (worlds : Core.WorldExtends world finalWorld)
      (frame : GeneralHeap.AdministrativePreserved mapping store finalMap finalStore)
      (evaluation : Core.Evaluates actual store code (.inLeft (Core.LocalLoop.controlType resultType) (.word word)) finalStore) :
      Result program context evidence source reasonAt resultType continuation administrativeContext environment heap items mapping world actual store code

theorem Result.prepend
    {program : Program} {context middleContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {resultType : Core.Ty}
    {continuation : SourceCoreLocalCell.Scope → Context → Core.Expr → Prop} {administrativeContext : Core.Context}
    {environment middleEnvironment : Dynamic.Environment} {heap middleHeap : Dynamic.Heap}
    {item : ForItemForm} {items : List ForItemForm} {mapping middleMap : GeneralHeap.LocationMap}
    {world middleWorld : Core.StoreTyping} {actual middleActual : Core.Environment}
    {store middleStore : Core.Store} {code middleCode : Core.Expr}
    (head : Dynamic.ForItemExecutes program context evidence source environment heap item middleContext middleEnvironment middleHeap)
    (contextExtension : ContextExtends source.owner context middleContext)
    (maps : GeneralHeap.LocationMap.Extends mapping middleMap) (worlds : Core.WorldExtends world middleWorld)
    (frame : GeneralHeap.AdministrativePreserved mapping store middleMap middleStore)
    (agreement : ContinuationAgreement actual store code middleActual middleStore middleCode)
    (tail : Result program middleContext evidence source reasonAt resultType continuation administrativeContext
      middleEnvironment middleHeap items middleMap middleWorld middleActual middleStore middleCode) :
    Result program context evidence source reasonAt resultType continuation administrativeContext
      environment heap (item :: items) mapping world actual store code := by
  cases tail with
  | continues tail execution tailContext futureMaps futureWorlds futureFrame futureAgreement =>
    exact .continues tail (.cons head execution) (contextExtension.trans tailContext) (maps.trans futureMaps) (worlds.trans futureWorlds)
      (frame.trans futureFrame) (agreement.trans futureAgreement)
  | fault fault related heaps futureMaps futureWorlds futureFrame evaluated =>
    exact .fault (.tail head fault) related heaps (maps.trans futureMaps) (worlds.trans futureWorlds)
      (frame.trans futureFrame) (agreement.wrap evaluated)

end Solcore.SourceSemantics.CoreLowering.ForHeaders
