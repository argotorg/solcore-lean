import Solcore.SourceSemantics.CoreLowering.LoopStatementCertificates
import Solcore.SourceSemantics.CoreLowering.LoopStatementFault

/-! Accepted default while lowering preserves supplied finite source success
and fault derivations. The source trace is the only termination witness. This
does not assert termination of every checked loop or general source fault
completeness. All completed Core runs agree with the preserved finite trace. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Default

open Frontend Frontend.SourceInference BasicStatements Internal ScalarStatementViews

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

theorem Tree.hasType_with_administrative
    {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : SourceSemantics.Context} {mode : Bool} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree compilation source reasonAt selfReason scope context mode statements type code)
    (wellFormed : Core.Ty.WellFormed [] type) (administrativeContext : Core.Context) :
    Core.HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code (Core.LocalLoop.resultType type) := by
  simpa only [Core.Expr.rename_id] using (tree.hasType wellFormed).rename (identity_respects scope administrativeContext)

/-- A successful source trace determines a finite executable Core result,
including the allocated administrative cells and the source-location map. -/
theorem lowerFlowStatements_source_success_run_preserves
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context finalContext : SourceSemantics.Context} {statements : List StatementId} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {tailReturns : Bool} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source) (noFor : NoForLoops source)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithExpression
      (fun fuel source scope id reasons => SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope id reasons)
      fuel source scope statements type reasonAt tailReturns selfReason = .ok code)
    (wellFormed : Core.Ty.WellFormed [] type) {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {heap after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (execution : ListExecutes tailReturns program context evidence source environment heap statements finalContext outcome after) :
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code = some (Core.LocalLoop.resultType type) ∧
    ∃ result finalStore finalMapping finalWorld required,
      ControlRepresents type outcome result ∧ GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore ∧
      (∀ runtimeFuel, required ≤ runtimeFuel → Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done result finalStore) ∧
      (∀ runtimeFuel actual actualStore, Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done actual actualStore →
        actual = result ∧ actualStore = finalStore) := by
  have tree := tree_of_lowerFlowStatementsWithExpression aligned unique noFor accepted
  obtain ⟨result, finalStore, finalMapping, finalWorld, related, evaluated, finalHeaps, maps, worlds, frame⟩ :=
    tree.source_success unique program evidence wellFormed environments heaps (canonical_layout environments) execution
  simp only [Core.Expr.rename_id] at evaluated
  obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel evaluated
  refine ⟨Core.infer_complete (tree.hasType_with_administrative wellFormed administrativeContext),
    result, finalStore, finalMapping, finalWorld, required, related, finalHeaps, maps, worlds, frame, completes, ?_⟩
  intro runtimeFuel actual actualStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) evaluated

theorem lowerFlowStatements_source_fault_run_preserves
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context finalContext : SourceSemantics.Context} {statements : List StatementId} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {tailReturns : Bool} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source) (noFor : NoForLoops source)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithExpression
      (fun fuel source scope id reasons => SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope id reasons)
      fuel source scope statements type reasonAt tailReturns selfReason = .ok code)
    (wellFormed : Core.Ty.WellFormed [] type) {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    (valid : PrimitiveExpressions.ContextValid compilation context) (covers : evidence.Covers context)
    {environment : Dynamic.Environment} {heap after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (fault : ListFaults tailReturns program context evidence source environment heap statements finalContext reason after) :
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code = some (Core.LocalLoop.resultType type) ∧
    ∃ word finalStore finalMapping finalWorld required,
      FaultRepresents program evidence source reasonAt reason word ∧ GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore ∧
      (∀ runtimeFuel, required ≤ runtimeFuel → Core.runStateful runtimeFuel (.initial code coreEnvironment store) =
        .done (.inLeft (Core.LocalLoop.controlType type) (.word word)) finalStore) ∧
      (∀ runtimeFuel actual actualStore, Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done actual actualStore →
        actual = .inLeft (Core.LocalLoop.controlType type) (.word word) ∧ actualStore = finalStore) := by
  have tree := tree_of_lowerFlowStatementsWithExpression aligned unique noFor accepted
  obtain ⟨word, finalStore, finalMapping, finalWorld, related, evaluated, finalHeaps, maps, worlds, frame⟩ :=
    tree.source_fault unique program evidence wellFormed valid covers environments heaps (canonical_layout environments) fault
  simp only [Core.Expr.rename_id] at evaluated
  obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel evaluated
  refine ⟨Core.infer_complete (tree.hasType_with_administrative wellFormed administrativeContext),
    word, finalStore, finalMapping, finalWorld, required, related, finalHeaps, maps, worlds, frame, completes, ?_⟩
  intro runtimeFuel actual actualStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) evaluated

inductive FinishedControlRepresents (type : Core.Ty) (fellThroughReason escapedReason : Core.Word) :
    Dynamic.ControlOutcome → Core.Value → Prop where
  | fallthrough (environment : Dynamic.Environment) :
      FinishedControlRepresents type fellThroughReason escapedReason (.fallthrough environment)
        (if type = .unit then .inRight .word .unit else .inLeft type (.word fellThroughReason))
  | returned (value : SourceStagedValue.Value) (typed : SourceStagedValue.coreType value = type) :
      FinishedControlRepresents type fellThroughReason escapedReason (.returned (StagedValue.toSource value))
        (.inRight .word (SourceStagedValue.toCore value))
  | breaking (environment : Dynamic.Environment) :
      FinishedControlRepresents type fellThroughReason escapedReason (.breaking environment) (.inLeft type (.word escapedReason))
  | continuing (environment : Dynamic.Environment) :
      FinishedControlRepresents type fellThroughReason escapedReason (.continuing environment) (.inLeft type (.word escapedReason))

def fallback (type : Core.Ty) (reason : Core.Word) : Core.Expr :=
  if type = .unit then Core.LanguageResult.success .unit else Core.LanguageResult.failure type (.word reason)

private theorem finish_success
    {type : Core.Ty} {outcome : Dynamic.ControlOutcome} {result : Core.Value}
    {environment : Core.Environment} {before after : Core.Store} {code : Core.Expr}
    (related : ControlRepresents type outcome result)
    (evaluated : Core.Evaluates environment before code result after) (fellThrough escaped : Core.Word) :
    ∃ finished, FinishedControlRepresents type fellThrough escaped outcome finished ∧
      Core.Evaluates environment before
        (Core.LocalControl.finish type (Core.LocalLoop.toControl type code escaped) (fallback type fellThrough)) finished after := by
  cases related with
  | fallthrough sourceEnv =>
    refine ⟨_, .fallthrough sourceEnv, Core.LocalControl.finish_fallthrough type
      (Core.LocalLoop.toControl_normal type escaped evaluated) ?_⟩
    by_cases unit : type = .unit
    · simp [fallback, unit, Core.LanguageResult.success, Core.Expr.weakenAt]
      exact .inRight .unit
    · simp [fallback, unit, Core.LanguageResult.failure, Core.Expr.weakenAt]
      exact .inLeft .word
  | returned value typed =>
    exact ⟨_, .returned value typed, Core.LocalControl.finish_returned type
      (Core.LocalLoop.toControl_normal type escaped evaluated)⟩
  | breaking sourceEnv =>
    exact ⟨_, .breaking sourceEnv, Core.LocalControl.finish_failure type
      (Core.LocalLoop.toControl_transfer type escaped evaluated)⟩
  | continuing sourceEnv =>
    exact ⟨_, .continuing sourceEnv, Core.LocalControl.finish_failure type
      (Core.LocalLoop.toControl_transfer type escaped evaluated)⟩

private theorem finish_hasType
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : SourceSemantics.Context} {statements : List StatementId} {type : Core.Ty} {flow : Core.Expr}
    {reasonAt : ExpressionId → Core.Word} {escaped : Core.Word}
    (tree : Tree compilation source reasonAt escaped scope context true statements type flow)
    (wellFormed : Core.Ty.WellFormed [] type) (admin : Core.Context) (fellThrough : Core.Word) :
    Core.HasType (SourceCoreLocalCell.coreContext scope ++ admin)
      (Core.LocalControl.finish type (Core.LocalLoop.toControl type flow escaped) (fallback type fellThrough))
      (Core.LanguageResult.resultType type) := by
  apply Core.LocalControl.finish_hasType wellFormed
    (Core.LocalLoop.toControl_hasType escaped wellFormed (tree.hasType_with_administrative wellFormed admin))
  by_cases unit : type = .unit
  · simpa [fallback, unit] using Core.LanguageResult.success_hasType (context := SourceCoreLocalCell.coreContext scope ++ admin) Core.HasType.unit
  · simpa [fallback, unit] using Core.LanguageResult.failure_hasType wellFormed (Core.HasType.word (value := fellThrough))

inductive FinishedOutcomeRepresents (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (type : Core.Ty)
    (fellThrough escaped : Core.Word) : Dynamic.ControlOutcome → Core.Value → Prop where
  | control {outcome value} (related : FinishedControlRepresents type fellThrough escaped outcome value) :
      FinishedOutcomeRepresents program evidence source reasonAt type fellThrough escaped outcome value
  | fault {reason word} (related : FaultRepresents program evidence source reasonAt reason word) :
      FinishedOutcomeRepresents program evidence source reasonAt type fellThrough escaped (.fault reason) (.inLeft type (.word word))

/-- Actual accepted function lowering preserves a supplied finite source
outcome. Fallthrough, return, escaped control and semantic faults retain their
separate boundary meanings. Fuel exhaustion is never a completed result. -/
theorem lowerStatements_source_run_preserves
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context finalContext : SourceSemantics.Context} {statements : List StatementId} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {fellThroughReason escapedReason : Core.Word} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source) (noFor : NoForLoops source)
    (accepted : SourceCoreLoops.lowerStatementsWithReasons fuel compilation source scope statements type reasonAt fellThroughReason escapedReason = .ok code)
    (wellFormed : Core.Ty.WellFormed [] type) {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    (valid : PrimitiveExpressions.ContextValid compilation context) (covers : evidence.Covers context)
    {environment : Dynamic.Environment} {heap after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (execution : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment heap statements finalContext outcome after) :
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code = some (Core.LanguageResult.resultType type) ∧
    ∃ result finalStore finalMapping finalWorld required,
      FinishedOutcomeRepresents program evidence source reasonAt type fellThroughReason escapedReason outcome result ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore ∧
      (∀ runtimeFuel, required ≤ runtimeFuel → Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done result finalStore) ∧
      (∀ runtimeFuel actual actualStore, Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done actual actualStore →
        actual = result ∧ actualStore = finalStore) := by
  obtain ⟨flow, same, tree⟩ := tree_of_lowerStatements aligned unique noFor accepted
  change code = Core.LocalControl.finish type (Core.LocalLoop.toControl type flow escapedReason) (fallback type fellThroughReason) at same
  subst code
  refine ⟨Core.infer_complete (finish_hasType tree wellFormed administrativeContext fellThroughReason), ?_⟩
  cases execution with
  | control execution =>
    obtain ⟨result, finalStore, finalMapping, finalWorld, related, evaluated, finalHeaps, maps, worlds, frame⟩ :=
      tree.source_success unique program evidence wellFormed environments heaps (canonical_layout environments) execution
    simp only [Core.Expr.rename_id] at evaluated
    obtain ⟨finished, related, finishedEval⟩ := finish_success related evaluated fellThroughReason escapedReason
    obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel finishedEval
    refine ⟨finished, finalStore, finalMapping, finalWorld, required, .control related, finalHeaps, maps, worlds, frame, completes, ?_⟩
    intro runtimeFuel actual actualStore completed
    exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) finishedEval
  | fault fault =>
    obtain ⟨word, finalStore, finalMapping, finalWorld, related, evaluated, finalHeaps, maps, worlds, frame⟩ :=
      tree.source_fault unique program evidence wellFormed valid covers environments heaps (canonical_layout environments) fault
    simp only [Core.Expr.rename_id] at evaluated
    have finishedEval := Core.LocalControl.finish_failure (fallback := fallback type fellThroughReason) type
      (Core.LocalLoop.toControl_failure type escapedReason evaluated)
    obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel finishedEval
    refine ⟨_, finalStore, finalMapping, finalWorld, required, .fault related, finalHeaps, maps, worlds, frame, completes, ?_⟩
    intro runtimeFuel actual actualStore completed
    exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) finishedEval

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Default
