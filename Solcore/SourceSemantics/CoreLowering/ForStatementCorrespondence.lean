import Solcore.SourceSemantics.CoreLowering.ForStatementBridge
import Solcore.SourceSemantics.CoreLowering.ForStatementReflectionBridge

/-! Finite completion equivalence for the actual accepted default while/for
compiler. Forward preservation retains all source outcomes and represented
state; reverse reflection constructs a source trace from Core completion only.
Fuel exhaustion remains a suspended computation, not a completed outcome. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor

open Frontend Frontend.SourceInference BasicStatements Reflection

/-- Finite completion is equivalent at the accepted function boundary. The
source side includes its specified semantic faults. Neither side treats a
fuel-exhausted checkpoint as a completed execution. -/
theorem lowerStatements_finite_iff
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : SourceSemantics.Context} {statements : List StatementId} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {fellThroughReason escapedReason : Core.Word} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreLoops.lowerStatementsWithReasons fuel compilation source scope statements type reasonAt fellThroughReason escapedReason = .ok code)
    (wellFormed : Core.Ty.WellFormed [] type) {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    (valid : PrimitiveExpressions.ContextValid compilation context) (covers : evidence.Covers context)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    (∃ runtimeFuel result finalStore, Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done result finalStore) ↔
    (∃ finalContext outcome after, Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment heap statements finalContext outcome after) := by
  constructor
  · rintro ⟨runtimeFuel, result, finalStore, completed⟩
    obtain ⟨finalContext, outcome, after, _, _, execution, _⟩ :=
      lowerStatements_run_reflects aligned unique accepted wellFormed valid environments heaps completed
    exact ⟨finalContext, outcome, after, execution⟩
  · rintro ⟨finalContext, outcome, after, execution⟩
    obtain ⟨_, result, finalStore, _, _, required, _, _, _, _, _, completes, _⟩ :=
      lowerStatements_source_run_preserves aligned unique accepted wellFormed valid covers environments heaps execution
    exact ⟨required, result, finalStore, completes required (Nat.le_refl _)⟩

end Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor
