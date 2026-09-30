import Solcore.SourceSemantics.CoreLowering.LoopScopedComposition
import Solcore.SourceSemantics.CoreLowering.LoopStatementBridge

/-! The function-boundary helper is inverted before reconstructing its source
flow. Fallthrough, returned values, escaped control and semantic faults retain
their distinct source outcomes. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection

open Frontend Frontend.SourceInference TypeSystem LocalCell Internal CoreProof Default

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


def FinishedResult (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (fellThrough escaped : Core.Word)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (statements : List StatementId) (type : Core.Ty)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping) (store : Core.Store)
    (result : Core.Value) (finalStore : Core.Store) : Prop :=
  ∃ finalContext outcome after finalMapping finalWorld,
    Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before statements finalContext outcome after ∧
    FinishedOutcomeRepresents program evidence source reasonAt type fellThrough escaped outcome result ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore

/-- This wrapper requires only the structural flow induction hypothesis and
an actual finite finished Core evaluation, never a source trace. -/
theorem reflects_finished
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty} {flow : Core.Expr}
    (correct : Reflects compilation program evidence source reasonAt scope context true statements type flow)
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap : Dynamic.Heap} {store finalStore : Core.Store} {result : Core.Value}
    (wellFormed : Core.Ty.WellFormed [] type) (valid : PrimitiveExpressions.ContextValid compilation context)
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ)
    (fellThrough escaped : Core.Word)
    (evaluated : Core.Evaluates actual store
      (Core.LocalControl.finish type (Core.LocalLoop.toControl type (flow.rename ξ) escaped) (fallback type fellThrough)) result finalStore) :
    FinishedResult program context evidence source reasonAt fellThrough escaped environment heap statements type mapping world store result finalStore := by
  obtain ⟨size, sized⟩ := evaluation_has_size evaluated
  obtain ⟨_, _, _, _, toControl⟩ := sized.bind_computation
  obtain ⟨_, flowStore, flowResult, _, flowEvaluation⟩ := toControl.bind_computation
  obtain ⟨finalContext, outcome, after, finalMapping, finalWorld, meaning, finalHeaps, maps, worlds, frame⟩ :=
    correct wellFormed valid environments heaps layout flowEvaluation.sound
  cases meaning with
  | control execution related =>
    obtain ⟨finished, finishedRelated, finishedEval⟩ := finish_success related flowEvaluation.sound fellThrough escaped
    obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated finishedEval
    exact ⟨finalContext, outcome, after, finalMapping, finalWorld, .control execution, .control finishedRelated,
      finalHeaps, maps, worlds, frame⟩
  | fault execution related =>
    have finishedEval := Core.LocalControl.finish_failure (fallback := fallback type fellThrough) type
      (Core.LocalLoop.toControl_failure type escaped flowEvaluation.sound)
    obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated finishedEval
    exact ⟨finalContext, _, after, finalMapping, finalWorld, .fault execution, .fault related,
      finalHeaps, maps, worlds, frame⟩

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection
