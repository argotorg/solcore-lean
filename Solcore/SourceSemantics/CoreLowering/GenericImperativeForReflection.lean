import Solcore.SourceSemantics.CoreLowering.GenericImperativeForIteration
import Solcore.SourceSemantics.CoreLowering.TypedImperativeForReflection

/-! A finite actual for-loop evaluation reconstructs condition, body and post
source traces in evaluation order. The post and body contracts are intermediate
induction results, supplied by the recursive statement tree. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext Reflects FlowRep)
open TypedImperativeFor (LoopState Progress SourceLoop PostReflects post_computation body_reflects)
open CompatibleExpressionPrimitives (bool_fields)
variable {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
  {scope : Scope}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (reflection : TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults)

include reflection in
theorem iterations_reflect {condition : ExpressionId} {node : ExpressionNode}
    {post : List ForItemForm} {statements : List StatementId} {expected : TypeSystem.Ty}
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
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

end Solcore.SourceSemantics.CoreLowering.GenericImperativeFor
