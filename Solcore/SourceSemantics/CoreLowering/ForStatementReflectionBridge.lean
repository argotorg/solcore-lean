import Solcore.SourceSemantics.CoreLowering.ForStatementReflection
import Solcore.SourceSemantics.CoreLowering.ForLoopStatementCertificates
import Solcore.SourceSemantics.CoreLowering.LoopFinishedReflection

/-! Actual accepted default while/for lowering reflects every completed Core run
into independent source semantics. No finite source trace is assumed. Static
metadata/context validity and represented initial heap/environment delimit the
scalar/product default profile; source calls remain outside it. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor

open Frontend Frontend.SourceInference BasicStatements Reflection

private theorem identity_respects (scope : SourceCoreLocalCell.Scope) (administrativeContext : Core.Context) :
    Core.Renaming.Respects Core.Renaming.id (SourceCoreLocalCell.coreContext scope)
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext) := by
  intro index foundType found
  change (SourceCoreLocalCell.coreContext scope ++ administrativeContext)[index]? = some foundType
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

private theorem canonical_layout
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {scope : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment) :
    Layout world (SourceCoreLocalCell.coreContext scope) coreEnvironment
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext) coreEnvironment Core.Renaming.id :=
  ⟨identity_respects scope administrativeContext, fun found => found, environments.runtime_hasTypes⟩


theorem lowerFlowStatements_run_reflects
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : SourceSemantics.Context} {statements : List StatementId} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {tailReturns : Bool} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithExpression
      (fun fuel source scope id reasons => SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope id reasons)
      fuel source scope statements type reasonAt tailReturns selfReason = .ok code)
    (wellFormed : Core.Ty.WellFormed [] type) {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    (valid : PrimitiveExpressions.ContextValid compilation context)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store finalStore : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    {runtimeFuel : Nat} {result : Core.Value}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (completed : Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done result finalStore) :
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code = some (Core.LocalLoop.resultType type) ∧
    Reflection.Result program context evidence source reasonAt tailReturns environment heap statements type mapping world store result finalStore := by
  have tree := tree_of_lowerFlowStatementsWithExpression aligned unique accepted
  have typed : Core.HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code (Core.LocalLoop.resultType type) := by
    simpa only [Core.Expr.rename_id] using (tree.hasType wellFormed).rename (identity_respects scope administrativeContext)
  exact ⟨Core.infer_complete typed,
    tree.reflects program evidence wellFormed valid environments heaps (canonical_layout environments)
      (by simpa only [Core.Expr.rename_id] using Core.runStateful_evaluation_sound completed)⟩

/-- Every completed result of actual accepted function lowering constructs a
finite source function trace with matching result, mapped cells and untouched
administrative cells. The theorem does not accept fuel exhaustion as done. -/
theorem lowerStatements_run_reflects
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : SourceSemantics.Context} {statements : List StatementId} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {fellThroughReason escapedReason : Core.Word} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreLoops.lowerStatementsWithReasons fuel compilation source scope statements type reasonAt fellThroughReason escapedReason = .ok code)
    (wellFormed : Core.Ty.WellFormed [] type) {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    (valid : PrimitiveExpressions.ContextValid compilation context)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store finalStore : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    {runtimeFuel : Nat} {result : Core.Value}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (completed : Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done result finalStore) :
    FinishedResult program context evidence source reasonAt fellThroughReason escapedReason environment heap statements type mapping world store result finalStore := by
  obtain ⟨flow, same, tree⟩ := tree_of_lowerStatements aligned unique accepted
  change code = Core.LocalControl.finish type (Core.LocalLoop.toControl type flow escapedReason) (Default.fallback type fellThroughReason) at same
  subst code
  apply reflects_finished (tree.reflects program evidence) wellFormed valid environments heaps
    (canonical_layout environments) fellThroughReason escapedReason
  simpa only [Core.Expr.rename_id] using Core.runStateful_evaluation_sound completed


end Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor
