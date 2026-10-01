import Solcore.SourceSemantics.CoreLowering.GenericImperativeWhileIteration
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileReflection

/-! Completed native iterations reconstruct source iterations by strict
induction on the actual Core derivation. Condition and body traces are obtained
from their concrete-tree induction hypotheses, including their heap effects. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeWhile
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext LoopState Progress FlowRep Preserves Reflects HeadPreserves HeadReflects body_reflects initial_state restored restore_rep)
open CompatibleExpressionPrimitives (bool_fields)

inductive SourceLoop (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (condition : ExpressionId) (statements : List StatementId) :
    Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | control {outcome after} (trace : Dynamic.WhileExecutes program context evidence source environment before condition statements context outcome after) :
      SourceLoop program context evidence source environment before condition statements outcome after
  | fault {reason after} (trace : Dynamic.WhileFaults program context evidence source environment before condition statements reason after) :
      SourceLoop program context evidence source environment before condition statements (.fault reason) after

variable {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
  {scope : Scope}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (meaning : TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults)
  (reflection : TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults)

include reflection in
theorem iterations_reflect {condition : ExpressionId} {node : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (correct : Reflects functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (bodyCannotFault : ∀ {before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ (size : Nat) {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
      LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (LocalLoop.fallthrough type) selfReason) value finalStore →
      ∃ outcome after finalMap finalWorld,
        SourceLoop program context evidence source environment before condition statements outcome after ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro mapping world before store finalStore value state evaluation
    obtain ⟨conditionSize, conditionStore, conditionValue, _, conditionEval⟩ := evaluation.bind_computation
    obtain ⟨conditionOutcome, conditionHeap, conditionMap, conditionWorld, conditionTrace, conditionRelated, conditionProgress⟩ :=
      condition_reflects functions program evidence reflection conditionTree found valid agrees state conditionEval.sound
    cases conditionRelated with
    | fault matched =>
      cases conditionTrace with
      | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_failure conditionEval.sound)
        exact ⟨_, conditionHeap, conditionMap, conditionWorld, .fault (.condition failed), .fault matched, conditionProgress⟩
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      subst sameSource
      subst sameCore
      cases conditionTrace with
      | value conditionTrace =>
        cases boolean with
        | false =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_false conditionEval.sound)
          exact ⟨_, conditionHeap, conditionMap, conditionWorld, .control (.done conditionTrace), .fallthrough environment, conditionProgress⟩
        | true =>
          obtain ⟨branchSize, branchSmaller, branch⟩ := evaluation.loop_true_branch conditionEval.sound
          obtain ⟨bodySize, bodyStore, bodyValue, _, bodyEval⟩ := branch.bind_computation
          obtain ⟨bodyContext, bodyOutcome, bodyHeap, bodyMap, bodyWorld, bodyTrace, bodyRelated, bodyProgress⟩ :=
            body_reflects functions program evidence correct valid agrees reference (state.progress conditionProgress) bodyEval.sound
          have progress := conditionProgress.trans bodyProgress
          cases bodyRelated with
          | fault matched =>
            cases bodyTrace with
            | control impossible => exact False.elim (bodyCannotFault impossible)
            | fault failed =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_failure conditionEval.sound bodyEval.sound)
              exact ⟨_, bodyHeap, bodyMap, bodyWorld, .fault (.body conditionTrace failed), .fault matched, progress⟩
          | returned payload =>
            cases bodyTrace with
            | control bodyTrace =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_returned conditionEval.sound bodyEval.sound)
              exact ⟨_, bodyHeap, bodyMap, bodyWorld, .control (.returns conditionTrace bodyTrace), .returned payload, progress⟩
          | breaking bodyEnvironment =>
            cases bodyTrace with
            | control bodyTrace =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_breaking conditionEval.sound bodyEval.sound)
              exact ⟨_, bodyHeap, bodyMap, bodyWorld, .control (.breaks conditionTrace bodyTrace), .fallthrough environment, progress⟩
          | fallthrough bodyEnvironment =>
            cases bodyTrace with
            | control bodyTrace =>
              have nextState := state.progress progress
              obtain ⟨nextSize, smaller, nextEval⟩ := branch.loop_next_fallthrough bodyEval.sound nextState.selfRead
              obtain ⟨outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress⟩ :=
                ih nextSize (Nat.lt_trans smaller branchSmaller) nextState nextEval
              cases nextTrace with
              | control nextTrace => exact ⟨_, after, finalMap, finalWorld, .control (.nextFallthrough conditionTrace bodyTrace nextTrace), related, progress.trans nextProgress⟩
              | fault nextTrace => exact ⟨_, after, finalMap, finalWorld, .fault (.nextFallthrough conditionTrace bodyTrace nextTrace), related, progress.trans nextProgress⟩
          | continuing bodyEnvironment =>
            cases bodyTrace with
            | control bodyTrace =>
              have nextState := state.progress progress
              obtain ⟨nextSize, smaller, nextEval⟩ := branch.loop_next_continuing bodyEval.sound nextState.selfRead
              obtain ⟨outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress⟩ :=
                ih nextSize (Nat.lt_trans smaller branchSmaller) nextState nextEval
              cases nextTrace with
              | control nextTrace => exact ⟨_, after, finalMap, finalWorld, .control (.nextContinue conditionTrace bodyTrace nextTrace), related, progress.trans nextProgress⟩
              | fault nextTrace => exact ⟨_, after, finalMap, finalWorld, .fault (.nextContinue conditionTrace bodyTrace nextTrace), related, progress.trans nextProgress⟩
/- The generated prelude installs its self closure before the first condition;
source heap and scope stay unchanged during this administrative step. -/
include meaning in
theorem while_preserves {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode code selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : Preserves functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code) :
    HeadPreserves functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) id expected type (LocalLoop.whileLoop type conditionCode code selfReason) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped trace
  obtain ⟨state, installedProgress⟩ := initial_state functions environments heaps locals agrees actualTyped read unmapped typed
  cases trace with
  | control sourceTrace =>
    obtain ⟨rfl, _, innerOutcome, rfl, sourceLoop⟩ := ScalarStatementViews.whileLoop unique (lookupStatement?_sound found) form sourceTrace
    obtain ⟨value, finalStore, finalMap, finalWorld, nativeTrace, represented, progress⟩ :=
      iterations_success sourceLoop meaning conditionTree conditionFound valid unique agrees reference correct state
    exact ⟨rfl, restored environment innerOutcome, value, finalStore, finalMap, finalWorld,
      by simpa only [LoopRenaming.whileLoop] using nativeTrace.whileLoop_evaluates,
      restore_rep represented environment, installedProgress.trans progress⟩
  | fault failed =>
    have sourceLoop := ScalarStatementViews.whileLoop_fault unique (lookupStatement?_sound found) form failed
    obtain ⟨value, finalStore, finalMap, finalWorld, nativeTrace, represented, progress⟩ :=
      iterations_fault sourceLoop meaning conditionTree conditionFound valid unique agrees reference correct state
    exact ⟨rfl, (by intro next impossible; cases impossible), value, finalStore, finalMap, finalWorld,
      by simpa only [LoopRenaming.whileLoop] using nativeTrace.whileLoop_evaluates,
      represented, installedProgress.trans progress⟩

include reflection in
theorem while_reflects {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode code selfReason) (LocalLoop.resultType type) ambient.definitions)
    (correct : Reflects functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    HeadReflects functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) id expected type (LocalLoop.whileLoop type conditionCode code selfReason) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped evaluated
  obtain ⟨state, installedProgress⟩ := initial_state functions environments heaps locals agrees actualTyped read unmapped typed
  rw [LoopRenaming.whileLoop] at evaluated
  obtain ⟨size, sized⟩ := evaluation_has_size evaluated
  obtain ⟨entrySize, _, entry⟩ := sized.iterate_entry
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, progress⟩ :=
    iterations_reflect functions program evidence reflection conditionTree conditionFound valid agrees reference correct
      bodyCannotFault entrySize state entry
  refine ⟨Dynamic.restoreControl environment outcome, after, finalMap, finalWorld, ?_, restored environment outcome,
    restore_rep represented environment, installedProgress.trans progress⟩
  cases trace with
  | control sourceLoop => exact .control (.whileLoop (lookupStatement?_sound found) form sourceLoop)
  | fault sourceLoop => exact .fault (.whileIteration (lookupStatement?_sound found) form sourceLoop)
end Solcore.SourceSemantics.CoreLowering.GenericImperativeWhile
