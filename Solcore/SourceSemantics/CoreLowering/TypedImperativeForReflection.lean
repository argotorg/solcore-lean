import Solcore.SourceSemantics.CoreLowering.TypedImperativeForIteration

/-! Completed native iterations reconstruct source iterations by strict
induction on the actual Core derivation. Condition and body traces are obtained
from their concrete-tree induction hypotheses, including their heap effects. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext Reflects FlowRep)
open CompatibleExpressionPrimitives (bool_fields)

inductive SourceLoop (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) :
    Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | control {outcome after} (trace : Dynamic.ForLoopExecutes program context evidence source environment before condition post statements context outcome after) :
      SourceLoop program context evidence source environment before condition post statements outcome after
  | fault {reason after} (trace : Dynamic.ForLoopFaults program context evidence source environment before condition post statements reason after) :
      SourceLoop program context evidence source environment before condition post statements (.fault reason) after

/-- Internal post contract, discharged by `TypedForHeader.Tree.reflects_post`.
It consumes the actual post subtree, not a prior source execution. -/
def PostReflects {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (faults : FunctionCalls.FaultRep) (items : List ForItemForm) (code : Expr) : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
    LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason mapping world before store →
    ∀ continued : Bool,
    Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ)) value finalStore →
    (∃ finalContext finalEnvironment after finalMap finalWorld,
      Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore) ∨
    (∃ finalContext reason token after finalMap finalWorld,
      Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore)

private theorem insertion_zero : Renaming.insertion 0 = (fun index => index + 1) := by
  funext index
  simp [Renaming.insertion]

private theorem shift_comp (left right : Nat) :
    Renaming.comp (fun index => index + left) (fun index => index + right) =
      (fun index => index + (right + left)) := by
  funext index
  simp [Renaming.comp, Nat.add_assoc]

set_option maxRecDepth 3000 in
/-- Inversion of the actual body envelope exposes the actual post computation.
The four branch temporaries and Unit/self slots retain their concrete values. -/
theorem post_computation {size : Nat} {actual : Environment} {before bodyStore after : Store}
    {type : Ty} {location : Location} {body post : Expr} {reason : Word} {value : Value}
    (continued : Bool)
    (evaluation : EvaluationSize size (Core.LoopExecution.bodyEnvironment type location actual) before
      (LocalLoop.advance type (Core.LoopExecution.bodyCode body)
        ((LocalLoop.advance type (Core.LoopExecution.conditionCode post) (LocalLoop.invoke type (.var 1) reason)).weakenAt 0)) value after)
    (bodyEval : Evaluates (Core.LoopExecution.bodyEnvironment type location actual) before
      (Core.LoopExecution.bodyCode body) (if continued then LocalLoop.continuingValue type else LocalLoop.fallthroughValue type) bodyStore) :
    ∃ postStore postValue,
      Evaluates (postValues type location continued ++ actual) bodyStore (ForLoop.postCode post) postValue postStore := by
  cases continued
  · obtain ⟨next, _, postAdvance⟩ := evaluation.advance_fallthrough bodyEval
    have renamed : EvaluationSize next
        (ForLoop.fallthroughPrefix type ++ Core.LoopExecution.entryEnvironment type location actual) bodyStore
        ((LocalLoop.advance type (Core.LoopExecution.conditionCode post) (LocalLoop.invoke type (.var 1) reason)).rename
          (fun index => index + 4)) value after := by
      simpa only [← Expr.rename_insertion, Expr.rename_comp, insertion_zero, shift_comp, Nat.reduceAdd, Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment, ForLoop.fallthroughPrefix, ForLoop.continuingPrefix, List.cons_append, List.nil_append] using postAdvance
    rw [LoopRenaming.advance] at renamed
    obtain ⟨_, store, result, _, evaluated⟩ := renamed.bind_computation
    exact ⟨store, result, evaluated.sound⟩
  · obtain ⟨next, _, postAdvance⟩ := evaluation.advance_continuing bodyEval
    have renamed : EvaluationSize next
        (ForLoop.continuingPrefix type ++ Core.LoopExecution.entryEnvironment type location actual) bodyStore
        ((LocalLoop.advance type (Core.LoopExecution.conditionCode post) (LocalLoop.invoke type (.var 1) reason)).rename
          (fun index => index + 4)) value after := by
      simpa only [← Expr.rename_insertion, Expr.rename_comp, insertion_zero, shift_comp, Nat.reduceAdd, Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment, ForLoop.fallthroughPrefix, ForLoop.continuingPrefix, List.cons_append, List.nil_append] using postAdvance
    rw [LoopRenaming.advance] at renamed
    obtain ⟨_, store, result, _, evaluated⟩ := renamed.bind_computation
    exact ⟨store, result, evaluated.sound⟩

variable {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
  {scope : Scope}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension uninitialized missing in
theorem iterations_reflect {condition : ExpressionId} {node : ExpressionNode}
    {post : List ForItemForm} {statements : List StatementId} {expected : TypeSystem.Ty}
    (conditionTree : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (correct : Reflects functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (postCorrect : PostReflects functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) faults post postCode)
    (bodyCannotFault : ∀ {before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ (size : Nat) {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
      LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore →
      ∃ outcome after finalMap finalWorld,
        SourceLoop program context evidence source environment before condition post statements outcome after ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro mapping world before store finalStore value state evaluation
    obtain ⟨conditionSize, conditionStore, conditionValue, _, conditionEval⟩ := evaluation.bind_computation
    obtain ⟨conditionOutcome, conditionHeap, conditionMap, conditionWorld, conditionTrace, conditionRelated, conditionProgress⟩ :=
      condition_reflects functions extension program evidence uninitialized missing conditionTree found valid agrees state conditionEval.sound
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
              obtain ⟨postStore, postValue, postEval⟩ := post_computation false branch bodyEval.sound
              rcases postCorrect (state.progress progress) false postEval with done | failed
              · obtain ⟨postContext, postEnvironment, postHeap, postMap, postWorld, postTrace, rfl, postProgress⟩ := done
                have prefixProgress := progress.trans postProgress
                have nextState := state.progress prefixProgress
                obtain ⟨nextSize, smaller, nextEval⟩ := ForLoop.next_fallthrough branch bodyEval.sound postEval nextState.selfRead
                obtain ⟨outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress⟩ :=
                  ih nextSize (Nat.lt_trans smaller branchSmaller) nextState nextEval
                cases nextTrace with
                | control nextTrace => exact ⟨_, after, finalMap, finalWorld, .control (.nextFallthrough conditionTrace bodyTrace postTrace nextTrace), related, prefixProgress.trans nextProgress⟩
                | fault nextTrace => exact ⟨_, after, finalMap, finalWorld, .fault (.nextFallthrough conditionTrace bodyTrace postTrace nextTrace), related, prefixProgress.trans nextProgress⟩
              · obtain ⟨postContext, reason, token, postHeap, postMap, postWorld, postTrace, rfl, matched, postProgress⟩ := failed
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                  (ForLoop.body_fallthrough_post_fault conditionEval.sound bodyEval.sound postEval)
                exact ⟨_, postHeap, postMap, postWorld, .fault (.postFallthrough conditionTrace bodyTrace postTrace), .fault matched, progress.trans postProgress⟩
          | continuing bodyEnvironment =>
            cases bodyTrace with
            | control bodyTrace =>
              obtain ⟨postStore, postValue, postEval⟩ := post_computation true branch bodyEval.sound
              rcases postCorrect (state.progress progress) true postEval with done | failed
              · obtain ⟨postContext, postEnvironment, postHeap, postMap, postWorld, postTrace, rfl, postProgress⟩ := done
                have prefixProgress := progress.trans postProgress
                have nextState := state.progress prefixProgress
                obtain ⟨nextSize, smaller, nextEval⟩ := ForLoop.next_continuing branch bodyEval.sound postEval nextState.selfRead
                obtain ⟨outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress⟩ :=
                  ih nextSize (Nat.lt_trans smaller branchSmaller) nextState nextEval
                cases nextTrace with
                | control nextTrace => exact ⟨_, after, finalMap, finalWorld, .control (.nextContinue conditionTrace bodyTrace postTrace nextTrace), related, prefixProgress.trans nextProgress⟩
                | fault nextTrace => exact ⟨_, after, finalMap, finalWorld, .fault (.nextContinue conditionTrace bodyTrace postTrace nextTrace), related, prefixProgress.trans nextProgress⟩
              · obtain ⟨postContext, reason, token, postHeap, postMap, postWorld, postTrace, rfl, matched, postProgress⟩ := failed
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                  (ForLoop.body_continuing_post_fault conditionEval.sound bodyEval.sound postEval)
                exact ⟨_, postHeap, postMap, postWorld, .fault (.postContinue conditionTrace bodyTrace postTrace), .fault matched, progress.trans postProgress⟩

end Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
