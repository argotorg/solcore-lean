import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForEdges
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostEdges
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedForContracts
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForState
import Solcore.SourceSemantics.CoreLowering.CellAwareLoopProgress
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationFlowBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedWhileEdges

/-! Actual condition and body children execute under the installed self cell.
The reached mixed heap, exact descriptor effect and caller admission survive
both Source preservation and native reflection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForIterations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds (PostAdmission)
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CellAwareLoopState (Progress)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    projects compiled.indexed.layouts.definitions)
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) callerProtocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  {administrative actualContext : Core.Context} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {location : Location} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before after : Dynamic.Heap} {store : Store}
  {certificate : GenericExpressionMeaning.Certificate} {body : Expr}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

open CellAwareInvocationForEdges
variable {condition : ExpressionId} {node : ExpressionNode}
  {statements : List StatementId} {expected : TypeSystem.Ty} {post : List ForItemForm}

theorem reflects {budget : Nat}
    (children : ∀ childSize, childSize < budget → CellAwareInvocationExpressionBounds.ReflectsAt (attachment := attachment) bridge context model bodyIndex stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? condition = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context condition node.type)
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (correct : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope false statements expected type code budget)
    (postCorrect : CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope post expected type postCode budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (booleans : ∀ {mapping world sourceValue nativeValue},
      model.Represents mapping world .bool sourceValue nativeValue .bool →
      ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
    (runtime : Dynamic.SourceRuntimeValid program context (bodyIndex.source))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = bodyIndex.compilation.solvedRequirements)
    (bodyTyped : ProtectedStateImperativeTypedSourceSites.Statements (bodyIndex.source) context statements)
    (postTyped : ∃ control final, ForItemsHaveType (bodyIndex.source) control context post final) :
    ∀ size, size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
      {store finalStore : Store} {value : Value},
    ∀ state : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store,
      Admission bridge context state.retained →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.ForLoop program stages sourceSize invocation context environment before condition post statements outcome after ∧
        Represents model finalMap finalWorld false expected type faults outcome value ∧
        Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
        location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧ Post bridge context expected outcome reached.retained := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro bounded mapping world before store finalStore value state ready evaluation
    obtain ⟨conditionSize, conditionStore, conditionValue, conditionSmaller, conditionEval⟩ := evaluation.bind_computation
    obtain ⟨conditionSourceSize, conditionOutcome, conditionHeap, conditionMap, conditionWorld,
        conditionTrace, conditionRelated, conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
      condition_reflects_at bridge model producer (children _ (Nat.lt_of_lt_of_le conditionSmaller bounded))
        tree found typed agrees state ready conditionEval
    cases conditionRelated with
    | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_failure conditionEval.sound)
      exact ⟨_, _, conditionHeap, conditionMap, conditionWorld, .testFault conditionTrace, .fault matched,
        conditionProgress, conditionState, conditionRetained, conditionPost.at_fault_type⟩
    | value payload =>
      rw [nodeType] at payload
      obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
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
          body_reflects_at bridge model producer correct
            (Nat.le_trans (Nat.le_of_lt bodySmaller) (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded))
            agrees conditionState runtime covers sameLedger bodyTyped conditionPost.at_value.2 bodyEval
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
            CellAwareInvocationForPostEdges.reflects_at (continuing := false) bridge model producer postCorrect
              (Nat.le_trans (Nat.le_of_lt postSmaller) (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded))
              agrees bodyState runtime covers sameLedger postTyped bodyPost postEval
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
                ForLoop.next_fallthrough branch bodyEval.sound postEval.sound postState.selfRead
              obtain ⟨nextSourceSize, outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress,
                  finalState, finalRetained, finalPost⟩ :=
                ih nextSize (Nat.lt_trans smaller branchSmaller)
                  (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) bounded) postState postPost nextEval
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
            CellAwareInvocationForPostEdges.reflects_at (continuing := true) bridge model producer postCorrect
              (Nat.le_trans (Nat.le_of_lt postSmaller) (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded))
              agrees bodyState runtime covers sameLedger postTyped bodyPost postEval
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
                ForLoop.next_continuing branch bodyEval.sound postEval.sound postState.selfRead
              obtain ⟨nextSourceSize, outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress,
                  finalState, finalRetained, finalPost⟩ :=
                ih nextSize (Nat.lt_trans smaller branchSmaller)
                  (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) bounded) postState postPost nextEval
              exact ⟨_, _, after, finalMap, finalWorld, .continueIterate conditionTrace bodyTrace postTrace nextTrace, related,
                prefixProgress.trans nextProgress, finalState,
                callerProtocol.trans (callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩

theorem preserves {budget : Nat}
    (children : ∀ childSize, childSize < budget → CellAwareInvocationExpressionBounds.PreservesAt (attachment := attachment) bridge context model bodyIndex stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? condition = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context condition node.type)
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (correct : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope false statements expected type code budget)
    (postCorrect : CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope post expected type postCode budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (booleans : ∀ {mapping world sourceValue nativeValue},
      model.Represents mapping world .bool sourceValue nativeValue .bool →
      ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
    (runtime : Dynamic.SourceRuntimeValid program context (bodyIndex.source))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = bodyIndex.compilation.solvedRequirements)
    (bodyTyped : ProtectedStateImperativeTypedSourceSites.Statements (bodyIndex.source) context statements)
    (postTyped : ∃ control final, ForItemsHaveType (bodyIndex.source) control context post final) :
    ∀ size, size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
      {store : Store} {outcome : Staging.Recursive.BodyOutcome},
    ∀ state : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store,
      Admission bridge context state.retained →
      Staging.Recursive.Size.ForLoop program stages size invocation context environment before condition post statements outcome after →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        Represents model finalMap finalWorld false expected type faults outcome value ∧
        Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
        location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧ Post bridge context expected outcome reached.retained := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro bounded mapping world before after store outcome state ready trace
    cases trace with
    | finished testTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
          cases sameSource
          subst sameCore
          exact ⟨_, conditionStore, conditionMap, conditionWorld, Core.LoopExecution.condition_false conditionEval,
            .fallthrough environment (.inl rfl), conditionProgress, conditionState, conditionRetained, conditionPost.at_value.2⟩
    | testFault testTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | fault matched =>
          exact ⟨_, conditionStore, conditionMap, conditionWorld, Core.LoopExecution.condition_failure conditionEval,
            .fault matched, conditionProgress, conditionState, conditionRetained, conditionPost.at_fault_type⟩
    | returnedFromBody testTrace bodyTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge model producer correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees conditionState runtime covers sameLedger bodyTyped conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | returned payload =>
            exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_returned conditionEval bodyEval, .returned payload,
              conditionProgress.trans bodyProgress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
    | forBreakFromBody testTrace bodyTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge model producer correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees conditionState runtime covers sameLedger bodyTyped conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | breaking innerEnvironment =>
            exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_breaking conditionEval bodyEval, .fallthrough environment (.inl rfl),
              conditionProgress.trans bodyProgress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
    | bodyFailure testTrace bodyTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge model producer correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees conditionState runtime covers sameLedger bodyTyped conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | fault matched =>
            exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_failure conditionEval bodyEval, .fault matched,
              conditionProgress.trans bodyProgress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
    | postFailure testTrace bodyTrace postTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge model producer correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees conditionState runtime covers sameLedger bodyTyped conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | fallthrough innerEnvironment allowed =>
            have progress := conditionProgress.trans bodyProgress
            obtain ⟨postValue, postStore, postMap, postWorld, postEval, postRelated, postProgress,
                postState, postRetained, postPost⟩ :=
              CellAwareInvocationForPostEdges.preserves_at (continuing := false) bridge model producer postCorrect
                (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                agrees bodyState runtime covers sameLedger postTyped bodyPost postTrace
            cases postRelated with
            | fault matched =>
              exact ⟨_, postStore, postMap, postWorld,
                ForLoop.body_fallthrough_post_fault conditionEval bodyEval postEval, .fault matched,
                progress.trans postProgress, postState,
                callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained, postPost⟩
    | iterate testTrace bodyTrace postTrace next =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge model producer correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees conditionState runtime covers sameLedger bodyTyped conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | fallthrough innerEnvironment allowed =>
            have progress := conditionProgress.trans bodyProgress
            obtain ⟨postValue, postStore, postMap, postWorld, postEval, postRelated, postProgress,
                postState, postRetained, postPost⟩ :=
              CellAwareInvocationForPostEdges.preserves_at (continuing := false) bridge model producer postCorrect
                (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                agrees bodyState runtime covers sameLedger postTyped bodyPost postTrace
            cases postRelated with
            | fallthrough _ _ =>
              have prefixProgress := progress.trans postProgress
              obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress,
                  finalState, finalRetained, finalPost⟩ :=
                ih _ (Staging.Recursive.Size.child_lt_stepSize (by simp))
                  (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                  postState postPost next
              exact ⟨result, finalStore, finalMap, finalWorld,
                ForLoop.body_fallthrough conditionEval bodyEval postEval postState.selfRead nativeTrace,
                related, prefixProgress.trans finalProgress, finalState,
                callerProtocol.trans (callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩

    | continuePostFailure testTrace bodyTrace postTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge model producer correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees conditionState runtime covers sameLedger bodyTyped conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | continuing innerEnvironment =>
            have progress := conditionProgress.trans bodyProgress
            obtain ⟨postValue, postStore, postMap, postWorld, postEval, postRelated, postProgress,
                postState, postRetained, postPost⟩ :=
              CellAwareInvocationForPostEdges.preserves_at (continuing := true) bridge model producer postCorrect
                (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                agrees bodyState runtime covers sameLedger postTyped bodyPost postTrace
            cases postRelated with
            | fault matched =>
              exact ⟨_, postStore, postMap, postWorld,
                ForLoop.body_continuing_post_fault conditionEval bodyEval postEval, .fault matched,
                progress.trans postProgress, postState,
                callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained, postPost⟩
    | continueIterate testTrace bodyTrace postTrace next =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge model producer correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees conditionState runtime covers sameLedger bodyTyped conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | continuing innerEnvironment =>
            have progress := conditionProgress.trans bodyProgress
            obtain ⟨postValue, postStore, postMap, postWorld, postEval, postRelated, postProgress,
                postState, postRetained, postPost⟩ :=
              CellAwareInvocationForPostEdges.preserves_at (continuing := true) bridge model producer postCorrect
                (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                agrees bodyState runtime covers sameLedger postTyped bodyPost postTrace
            cases postRelated with
            | fallthrough _ _ =>
              have prefixProgress := progress.trans postProgress
              obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress,
                  finalState, finalRetained, finalPost⟩ :=
                ih _ (Staging.Recursive.Size.child_lt_stepSize (by simp))
                  (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                  postState postPost next
              exact ⟨result, finalStore, finalMap, finalWorld,
                ForLoop.body_continuing conditionEval bodyEval postEval postState.selfRead nativeTrace,
                related, prefixProgress.trans finalProgress, finalState,
                callerProtocol.trans (callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForIterations
