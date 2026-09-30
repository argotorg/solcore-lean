import Solcore.SourceSemantics.CoreLowering.ControlStatementCertificates
import Solcore.SourceSemantics.CoreLowering.ControlStatementMeaning

/-! Actual accepted scoped-control lowering implies independent source/Core
correspondence. Static certificates and all child evaluations are extracted,
not supplied by the caller. This is the finite, loop-free scalar/product
profile; its administrative heap may contain recursive closures. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ControlStatements

open Frontend Frontend.SourceInference BasicStatements

theorem lowerFlowStatements_run_preserves
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {tailReturns : Bool} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreControl.lowerFlowStatementsWithReasons fuel source scope statements type reasonAt tailReturns = .ok code)
    (wellFormed : Core.Ty.WellFormed [] type) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code = some (Core.LocalControl.resultType type) ∧
    ∃ finalContext outcome after result finalStore finalMapping finalWorld required,
      Executes tailReturns program context evidence source environment heap statements finalContext outcome after ∧
      OutcomeRepresents program evidence source finalMapping finalWorld administrativeContext reasonAt type outcome result ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.EnvRepresents finalMapping finalWorld administrativeContext scope environment coreEnvironment ∧
      GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore ∧
      (∀ runtimeFuel, required ≤ runtimeFuel → Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done result finalStore) ∧
      (∀ runtimeFuel actual actualStore, Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done actual actualStore →
        actual = result ∧ actualStore = finalStore) := by
  have tree := tree_of_lowerFlowStatements aligned unique accepted
  obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
    sourceExecution, related, coreExecution, finalHeaps, mapsExtended, worldsExtended, frame⟩ :=
    tree.preserves program evidence environments heaps
  obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel coreExecution
  refine ⟨Core.infer_complete (tree.hasType_with_administrative wellFormed administrativeContext),
    finalContext, outcome, after, result, finalStore, finalMapping, finalWorld, required,
    sourceExecution, related, finalHeaps, mapsExtended, worldsExtended,
    environments.extend mapsExtended worldsExtended, frame, completes, ?_⟩
  intro runtimeFuel actual actualStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) coreExecution

/-- The executable function compiler's finished result agrees with source
execution. The relation distinguishes ordinary returns, Unit fallthrough,
non-Unit missing returns, and the provider token of uninitialized reads. -/
theorem lowerStatements_run_preserves
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {fellThroughReason : Core.Word} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreControl.lowerStatementsWithReasons fuel source scope statements type reasonAt fellThroughReason = .ok code)
    (wellFormed : Core.Ty.WellFormed [] type) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code = some (Core.LanguageResult.resultType type) ∧
    ∃ finalContext outcome after result finalStore finalMapping finalWorld required,
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment heap statements finalContext outcome after ∧
      FinishedOutcomeRepresents program evidence source finalMapping finalWorld administrativeContext reasonAt fellThroughReason
        type outcome result ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.EnvRepresents finalMapping finalWorld administrativeContext scope environment coreEnvironment ∧
      GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore ∧
      (∀ runtimeFuel, required ≤ runtimeFuel → Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done result finalStore) ∧
      (∀ runtimeFuel actual actualStore, Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done actual actualStore →
        actual = result ∧ actualStore = finalStore) := by
  obtain ⟨flow, same, tree⟩ := tree_of_lowerStatements aligned unique accepted
  change code = Core.LocalControl.finish type flow (fallback type fellThroughReason) at same
  subst code
  obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
    sourceExecution, related, coreExecution, finalHeaps, mapsExtended, worldsExtended, frame⟩ :=
    tree.finish_preserves fellThroughReason program evidence environments heaps
  obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel coreExecution
  refine ⟨Core.infer_complete (tree.finish_hasType wellFormed administrativeContext fellThroughReason),
    finalContext, outcome, after, result, finalStore, finalMapping, finalWorld, required,
    sourceExecution, related, finalHeaps, mapsExtended, worldsExtended,
    environments.extend mapsExtended worldsExtended, frame, completes, ?_⟩
  intro runtimeFuel actual actualStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) coreExecution

end Solcore.SourceSemantics.CoreLowering.ControlStatements
