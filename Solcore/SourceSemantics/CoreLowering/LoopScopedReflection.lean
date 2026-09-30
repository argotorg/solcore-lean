import Solcore.SourceSemantics.CoreLowering.LoopStatementReconstruction

/-! Scoped-head reconstruction contracts and sequencing. Source local names
and contexts are restored at a block, conditional, or loop boundary; allocated
cells and their location-map/world extensions remain observable. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection

open Frontend Frontend.SourceInference TypeSystem LocalCell Internal CoreProof

inductive ScopedMeaning (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (id : StatementId) (type : Core.Ty) : Dynamic.ControlOutcome → Dynamic.Heap → Core.Value → Prop where
  | control {outcome after result}
      (execution : Dynamic.StatementExecutes program context evidence source environment before id context
        (Dynamic.restoreControl environment outcome) after)
      (related : ControlRepresents type outcome result) :
      ScopedMeaning program context evidence source reasonAt environment before id type outcome after result
  | fault {reason after word}
      (execution : Dynamic.StatementFaults program context evidence source environment before id reason after)
      (related : FaultRepresents program evidence source reasonAt reason word) :
      ScopedMeaning program context evidence source reasonAt environment before id type (.fault reason) after
        (.inLeft (Core.LocalLoop.controlType type) (.word word))

def ScopedResult (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (id : StatementId) (type : Core.Ty)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping) (store : Core.Store)
    (result : Core.Value) (finalStore : Core.Store) : Prop :=
  ∃ outcome after finalMapping finalWorld,
    ScopedMeaning program context evidence source reasonAt environment before id type outcome after result ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore

def ScopedReflects (compilation : SourceCorePrimitive.Context) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (scope : SourceCoreLocalCell.Scope)
    (context : Context) (id : StatementId) (type : Core.Ty) (code : Core.Expr) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap : Dynamic.Heap} {store finalStore : Core.Store} {result : Core.Value},
    Core.Ty.WellFormed [] type → PrimitiveExpressions.ContextValid compilation context →
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ →
    Core.Evaluates actual store (code.rename ξ) result finalStore →
    ScopedResult program context evidence source reasonAt environment heap id type mapping world store result finalStore

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection
