import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedConditionalHeads
import Solcore.SourceSemantics.CoreLowering.ProtectedStateFor
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForEdges
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForPostEdges
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedForContracts

/-! Staged condition and body children run under the actual installed loop
self cell. Hidden native arguments change only renamings; the reached Source
heap, staged fault tag, and full admitted caller post are retained. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForIterations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedConditionalHeads (FlowPreserves FlowReflects)
open TypedLexicalWhile (Progress)
open CompatibleExpressionPrimitives (bool_fields)
open CallableIndexedOwnedAdmittedStagedForEdges
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before after : Dynamic.Heap} {store : Store}
  {certificate : GenericExpressionMeaning.Certificate} {body : Expr}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
local notation "values" => SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable (guard : Location → CallableIndexedHistory.NativeFrame → Prop)
  {condition : ExpressionId} {node : ExpressionNode} {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}

theorem reflects {budget : Nat}
    (children : ∀ childSize, childSize < budget → ReflectsAt bridge context model stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? condition = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context condition node.type)
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (correct : FlowReflects (administrative := administrative) (receiving := registry) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions guard context scope false statements expected type code budget)
    (postCorrect : CallableIndexedOwnedAdmittedStagedForPostContracts.Reflects (administrative := administrative)
      (receiving := registry) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions guard context scope post expected type postCode budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation)) :
    ∀ size, size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
      {store finalStore : Store} {value : Value},
    ∀ state : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store,
    ∀ {native : CallableIndexedHistory.NativeFrame},
      store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) →
      guard contextLocation native → Admission bridge context state.retained →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.ForLoop program stages sourceSize invocation context environment before condition post statements outcome after ∧
        Represents model finalMap finalWorld false expected type faults outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧ Post bridge context expected outcome reached.retained := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro bounded mapping world before store finalStore value state native fixedRead guarded ready evaluation
    obtain ⟨conditionSize, conditionStore, conditionValue, conditionSmaller, conditionEval⟩ := evaluation.bind_computation
    obtain ⟨conditionSourceSize, conditionOutcome, conditionHeap, conditionMap, conditionWorld,
        conditionTrace, conditionRelated, conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
      condition_reflects_at bridge functions (children _ (Nat.lt_of_lt_of_le conditionSmaller bounded))
        tree found typed agrees state ready conditionEval
    cases conditionRelated with
    | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_failure conditionEval.sound)
      exact ⟨_, _, conditionHeap, conditionMap, conditionWorld, .testFault conditionTrace, .fault matched,
        conditionProgress, conditionState, conditionRetained, conditionPost.at_fault_type⟩
    | value payload =>
      rw [nodeType] at payload
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      subst sameSource
      subst sameCore
      cases boolean with
      | false =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_false conditionEval.sound)
        exact ⟨_, _, conditionHeap, conditionMap, conditionWorld, .finished conditionTrace, .fallthrough environment (.inl rfl),
          conditionProgress, conditionState, conditionRetained, conditionPost.at_value.2⟩
      | true =>
        obtain ⟨branchSize, branchSmaller, branch⟩ := evaluation.loop_true_branch conditionEval.sound
        obtain ⟨bodySize, bodyStore, bodyValue, bodySmaller, bodyEval⟩ := branch.bind_computation
        obtain ⟨bodySourceSize, bodyContext, bodyOutcome, bodyHeap, bodyMap, bodyWorld, bodyTrace,
            bodyRelated, bodyProgress, bodyState, bodyRetained, bodyPost⟩ :=
          body_reflects_at bridge functions guard correct
            (Nat.le_trans (Nat.le_of_lt bodySmaller) (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded))
            agrees reference conditionState
            (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2
            guarded conditionPost.at_value.2 bodyEval
        have progress := conditionProgress.trans bodyProgress
        cases bodyRelated with
        | fault matched =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
            (Core.LoopExecution.body_failure conditionEval.sound bodyEval.sound)
          exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .bodyFailure conditionTrace bodyTrace, .fault matched,
            progress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
        | returned payload =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
            (Core.LoopExecution.body_returned conditionEval.sound bodyEval.sound)
          exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .returnedFromBody conditionTrace bodyTrace, .returned payload,
            progress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
        | fallthrough innerEnvironment allowed =>
          obtain ⟨postSize, postStore, postValue, postSmaller, postEval⟩ :=
            RecursiveNamedForContracts.post_computation_size false branch bodyEval.sound
          obtain ⟨postSourceSize, postContext, postOutcome, postHeap, postMap, postWorld, postTrace,
              postRelated, postProgress, postState, postRetained, postPost⟩ :=
            CallableIndexedOwnedAdmittedStagedForPostEdges.reflects_at (continuing := false) bridge functions guard postCorrect
              (Nat.le_trans (Nat.le_of_lt postSmaller) (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded))
              agrees reference bodyState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2
              guarded bodyPost postEval
          cases postOutcome with
          | fault failure =>
            cases postRelated with
            | fault matched =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (ForLoop.body_fallthrough_post_fault conditionEval.sound bodyEval.sound postEval.sound)
              exact ⟨_, _, postHeap, postMap, postWorld, .postFailure conditionTrace bodyTrace postTrace,
                .fault matched, progress.trans postProgress, postState,
                callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained, postPost⟩
          | done postEnvironment =>
            cases postRelated with
            | fallthrough _ _ =>
              have prefixProgress := progress.trans postProgress
              obtain ⟨nextSize, smaller, nextEval⟩ :=
                ForLoop.next_fallthrough branch bodyEval.sound postEval.sound postState.live.selfRead
              obtain ⟨nextSourceSize, outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress,
                  finalState, finalRetained, finalPost⟩ :=
                ih nextSize (Nat.lt_trans smaller branchSmaller)
                  (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) bounded) postState
                  (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead prefixProgress.2.2.2.1).2
                  guarded postPost nextEval
              exact ⟨_, _, after, finalMap, finalWorld, .iterate conditionTrace bodyTrace postTrace nextTrace, related,
                prefixProgress.trans nextProgress, finalState,
                callerProtocol.trans (callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩

        | breaking innerEnvironment =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
            (Core.LoopExecution.body_breaking conditionEval.sound bodyEval.sound)
          exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .forBreakFromBody conditionTrace bodyTrace,
            .fallthrough environment (.inl rfl), progress, bodyState,
            callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
        | continuing innerEnvironment =>
          obtain ⟨postSize, postStore, postValue, postSmaller, postEval⟩ :=
            RecursiveNamedForContracts.post_computation_size true branch bodyEval.sound
          obtain ⟨postSourceSize, postContext, postOutcome, postHeap, postMap, postWorld, postTrace,
              postRelated, postProgress, postState, postRetained, postPost⟩ :=
            CallableIndexedOwnedAdmittedStagedForPostEdges.reflects_at (continuing := true) bridge functions guard postCorrect
              (Nat.le_trans (Nat.le_of_lt postSmaller) (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded))
              agrees reference bodyState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2
              guarded bodyPost postEval
          cases postOutcome with
          | fault failure =>
            cases postRelated with
            | fault matched =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (ForLoop.body_continuing_post_fault conditionEval.sound bodyEval.sound postEval.sound)
              exact ⟨_, _, postHeap, postMap, postWorld, .continuePostFailure conditionTrace bodyTrace postTrace,
                .fault matched, progress.trans postProgress, postState,
                callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained, postPost⟩
          | done postEnvironment =>
            cases postRelated with
            | fallthrough _ _ =>
              have prefixProgress := progress.trans postProgress
              obtain ⟨nextSize, smaller, nextEval⟩ :=
                ForLoop.next_continuing branch bodyEval.sound postEval.sound postState.live.selfRead
              obtain ⟨nextSourceSize, outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress,
                  finalState, finalRetained, finalPost⟩ :=
                ih nextSize (Nat.lt_trans smaller branchSmaller)
                  (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) bounded) postState
                  (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead prefixProgress.2.2.2.1).2
                  guarded postPost nextEval
              exact ⟨_, _, after, finalMap, finalWorld, .continueIterate conditionTrace bodyTrace postTrace nextTrace, related,
                prefixProgress.trans nextProgress, finalState,
                callerProtocol.trans (callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩

theorem preserves {budget : Nat}
    (children : ∀ childSize, childSize < budget → PreservesAt bridge context model stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? condition = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context condition node.type)
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (correct : FlowPreserves (administrative := administrative) (receiving := registry) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions guard context scope false statements expected type code budget)
    (postCorrect : CallableIndexedOwnedAdmittedStagedForPostContracts.Preserves (administrative := administrative)
      (receiving := registry) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions guard context scope post expected type postCode budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation)) :
    ∀ size, size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
      {store : Store} {outcome : Staging.Recursive.BodyOutcome},
    ∀ state : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store,
    ∀ {native : CallableIndexedHistory.NativeFrame},
      store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) →
      guard contextLocation native → Admission bridge context state.retained →
      Staging.Recursive.Size.ForLoop program stages size invocation context environment before condition post statements outcome after →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        Represents model finalMap finalWorld false expected type faults outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧ Post bridge context expected outcome reached.retained := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro bounded mapping world before after store outcome state native fixedRead guarded ready trace
    cases trace with
    | finished testTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge functions
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          exact ⟨_, conditionStore, conditionMap, conditionWorld, Core.LoopExecution.condition_false conditionEval,
            .fallthrough environment (.inl rfl), conditionProgress, conditionState, conditionRetained, conditionPost.at_value.2⟩
    | testFault testTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge functions
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | fault matched =>
          exact ⟨_, conditionStore, conditionMap, conditionWorld, Core.LoopExecution.condition_failure conditionEval,
            .fault matched, conditionProgress, conditionState, conditionRetained, conditionPost.at_fault_type⟩
    | returnedFromBody testTrace bodyTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge functions
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge functions guard correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2
              guarded conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | returned payload =>
            exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_returned conditionEval bodyEval, .returned payload,
              conditionProgress.trans bodyProgress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
    | forBreakFromBody testTrace bodyTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge functions
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge functions guard correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2
              guarded conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | breaking innerEnvironment =>
            exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_breaking conditionEval bodyEval, .fallthrough environment (.inl rfl),
              conditionProgress.trans bodyProgress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
    | bodyFailure testTrace bodyTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge functions
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge functions guard correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2
              guarded conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | fault matched =>
            exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_failure conditionEval bodyEval, .fault matched,
              conditionProgress.trans bodyProgress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
    | postFailure testTrace bodyTrace postTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge functions
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge functions guard correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2
              guarded conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | fallthrough innerEnvironment allowed =>
            have progress := conditionProgress.trans bodyProgress
            obtain ⟨postValue, postStore, postMap, postWorld, postEval, postRelated, postProgress,
                postState, postRetained, postPost⟩ :=
              CallableIndexedOwnedAdmittedStagedForPostEdges.preserves_at (continuing := false) bridge functions guard postCorrect
                (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                agrees reference bodyState
                (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2
                guarded bodyPost postTrace
            cases postRelated with
            | fault matched =>
              exact ⟨_, postStore, postMap, postWorld,
                ForLoop.body_fallthrough_post_fault conditionEval bodyEval postEval, .fault matched,
                progress.trans postProgress, postState,
                callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained, postPost⟩
    | iterate testTrace bodyTrace postTrace next =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge functions
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge functions guard correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2
              guarded conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | fallthrough innerEnvironment allowed =>
            have progress := conditionProgress.trans bodyProgress
            obtain ⟨postValue, postStore, postMap, postWorld, postEval, postRelated, postProgress,
                postState, postRetained, postPost⟩ :=
              CallableIndexedOwnedAdmittedStagedForPostEdges.preserves_at (continuing := false) bridge functions guard postCorrect
                (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                agrees reference bodyState
                (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2
                guarded bodyPost postTrace
            cases postRelated with
            | fallthrough _ _ =>
              have prefixProgress := progress.trans postProgress
              obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress,
                  finalState, finalRetained, finalPost⟩ :=
                ih _ (Staging.Recursive.Size.child_lt_stepSize (by simp))
                  (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                  postState (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead prefixProgress.2.2.2.1).2
                  guarded postPost next
              exact ⟨result, finalStore, finalMap, finalWorld,
                ForLoop.body_fallthrough conditionEval bodyEval postEval postState.live.selfRead nativeTrace,
                related, prefixProgress.trans finalProgress, finalState,
                callerProtocol.trans (callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩

    | continuePostFailure testTrace bodyTrace postTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge functions
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge functions guard correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2
              guarded conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | continuing innerEnvironment =>
            have progress := conditionProgress.trans bodyProgress
            obtain ⟨postValue, postStore, postMap, postWorld, postEval, postRelated, postProgress,
                postState, postRetained, postPost⟩ :=
              CallableIndexedOwnedAdmittedStagedForPostEdges.preserves_at (continuing := true) bridge functions guard postCorrect
                (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                agrees reference bodyState
                (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2
                guarded bodyPost postTrace
            cases postRelated with
            | fault matched =>
              exact ⟨_, postStore, postMap, postWorld,
                ForLoop.body_continuing_post_fault conditionEval bodyEval postEval, .fault matched,
                progress.trans postProgress, postState,
                callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained, postPost⟩
    | continueIterate testTrace bodyTrace postTrace next =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge functions
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge functions guard correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2
              guarded conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | continuing innerEnvironment =>
            have progress := conditionProgress.trans bodyProgress
            obtain ⟨postValue, postStore, postMap, postWorld, postEval, postRelated, postProgress,
                postState, postRetained, postPost⟩ :=
              CallableIndexedOwnedAdmittedStagedForPostEdges.preserves_at (continuing := true) bridge functions guard postCorrect
                (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                agrees reference bodyState
                (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2
                guarded bodyPost postTrace
            cases postRelated with
            | fallthrough _ _ =>
              have prefixProgress := progress.trans postProgress
              obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress,
                  finalState, finalRetained, finalPost⟩ :=
                ih _ (Staging.Recursive.Size.child_lt_stepSize (by simp))
                  (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                  postState (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead prefixProgress.2.2.2.1).2
                  guarded postPost next
              exact ⟨result, finalStore, finalMap, finalWorld,
                ForLoop.body_continuing conditionEval bodyEval postEval postState.live.selfRead nativeTrace,
                related, prefixProgress.trans finalProgress, finalState,
                callerProtocol.trans (callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForIterations
