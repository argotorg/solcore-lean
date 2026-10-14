import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForLiftBounds

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageBodyLiftBounds Staging.Recursive.Lifting
open SelectedCompilationStageWhileLifting SelectedCompilationStagePhysicalReadiness
open SelectedCompilationStageForLiftBounds
open CallableIndexedOwnedAdmittedStagedConditionalHeads
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {certificate : GenericExpressionMeaning.Certificate}
  {test : ExpressionId} {node : ExpressionNode} {statements : List StatementId} {post : List ForItemForm}
  {expected : TypeSystem.Ty} {type : Ty} {testCode loopCode postCode : Expr}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

variable {environment : Dynamic.Environment} {canonical actual : Environment}
  {actualContext : Core.Context} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}

local notation "ReadyAt" => PhysicalReady (administrative := administrative) (receiving := receiving)
  (frame := frame) (globals := globals) (context := context) (scope := scope)
  bridge functions condition environment canonical actual actualContext ξ contextLocation native

private theorem post_ready {before after : Dynamic.Heap} {finalContext : SourceSemantics.Context}
    {finalEnvironment : Dynamic.Environment}
    (preservation : ∀ n, CallableIndexedOwnedAdmittedStagedForPostContracts.Preserves
      (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope post expected type postCode n)
    (ready : ReadyAt before)
    (trace : Staging.Recursive.ForItems program stages invocation context environment before post
      finalContext (.done finalEnvironment) after) : ReadyAt after := by
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  obtain ⟨size, measured⟩ := Staging.Recursive.Size.ForItems.of_trace trace
  obtain ⟨_, finalStore, finalMap, finalWorld, _, _, finalHeaps, maps, worlds, preserved, metadata,
    last, _, post⟩ := preservation size (Nat.le_refl _) environments heaps locals agrees actualTyped
      reference read unmapped initial conditioned admitted measured
  exact ⟨finalMap, finalWorld, finalStore, environments.extend maps worlds, finalHeaps, locals.mono metadata,
    agrees, actualTyped.weaken worlds, reference,
    ((preserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read),
    (preserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1, last, conditioned, post⟩

private theorem post_value {budget size : Nat} {before after : Dynamic.Heap}
    {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment}
    (postLift : ItemsLifts (administrative := administrative) (receiving := receiving) (frame := frame)
      (globals := globals) (context := context) (scope := scope) (stages := stages) (invocation := invocation)
      bridge functions condition post budget)
    (postPreservation : ∀ n, CallableIndexedOwnedAdmittedStagedForPostContracts.Preserves
      (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope post expected type postCode n)
    (ready : ReadyAt before) (within : size ≤ budget)
    (trace : SourceExecutionSize.ForItemsExecute program size context invocation.evidence invocation.source
      environment before post finalContext finalEnvironment after) :
    (∃ failedContext origin call reason reached,
      Staging.Recursive.ForItems program stages invocation context environment before post
        failedContext (.fault (.stage origin call reason)) reached) ∨
    (Staging.Recursive.ForItems program stages invocation context environment before post
      finalContext (.done finalEnvironment) after ∧ ReadyAt after) := by
  obtain ⟨last, staged, reached, lifted, adapted⟩ := postLift within ready (.done trace)
  cases staged with
  | done env =>
    cases adapted with
    | completed matched =>
      cases matched
      exact .inr ⟨lifted, post_ready bridge functions condition postPreservation ready lifted⟩
  | fault reason =>
    cases adapted with
    | completed matched => cases matched
    | rejected origin call reason finalContext reached =>
      exact .inl ⟨_, origin, call, reason, reached, lifted⟩

theorem for_ready {budget : Nat}
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (body : FlowLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) bridge functions condition context scope false statements budget)
    (bodyPreservation : ∀ n, FlowPreserves (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope false statements expected type loopCode n)
    (postLift : ItemsLifts (administrative := administrative) (receiving := receiving) (frame := frame)
      (globals := globals) (context := context) (scope := scope) (stages := stages) (invocation := invocation)
      bridge functions condition post budget)
    (postPreservation : ∀ n, CallableIndexedOwnedAdmittedStagedForPostContracts.Preserves
      (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope post expected type postCode n)
    {size : Nat} {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (within : size ≤ budget) (ready : ReadyAt before)
    (trace : PlainFor program size invocation context environment before test post statements outcome after) :
    ForLift program stages invocation context environment before test post statements outcome after := by
  induction size using Nat.strongRecOn generalizing before after outcome with
  | ind size ih =>
    cases trace with
    | control trace =>
      cases trace with
      | done testTrace =>
        rcases test_value bridge functions condition children preservation found typed generated ready
          (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within) testTrace with
          stopped | ⟨lifted, _, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · exact ⟨_, _, .finished lifted, .completed (.fallthrough environment)⟩
      | nextFallthrough testTrace bodyTrace postTrace next =>
        rcases test_value bridge functions condition children preservation found typed generated ready
          (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within) testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge functions condition body testReady
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have bodyReady := body_ready bridge functions condition bodyPreservation testReady liftedBody
            rcases post_value bridge functions condition postLift postPreservation bodyReady
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within) postTrace with
              stopped | ⟨liftedPost, nextReady⟩
            · obtain ⟨failedContext, origin, call, reason, reached, stopped⟩ := stopped
              exact ⟨_, reached, .postFailure liftedTest liftedBody stopped,
                .rejected origin call reason context reached⟩
            · obtain ⟨staged, reached, liftedNext, adaptedNext⟩ := ih _
                (SourceExecutionSize.child_lt_stepSize (by simp))
                (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
                nextReady (.control next)
              exact ⟨staged, reached, .iterate liftedTest liftedBody liftedPost liftedNext, adaptedNext⟩
      | nextContinue testTrace bodyTrace postTrace next =>
        rcases test_value bridge functions condition children preservation found typed generated ready
          (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within) testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge functions condition body testReady
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have bodyReady := body_continue_ready bridge functions condition bodyPreservation testReady liftedBody
            rcases post_value bridge functions condition postLift postPreservation bodyReady
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within) postTrace with
              stopped | ⟨liftedPost, nextReady⟩
            · obtain ⟨failedContext, origin, call, reason, reached, stopped⟩ := stopped
              exact ⟨_, reached, .continuePostFailure liftedTest liftedBody stopped,
                .rejected origin call reason context reached⟩
            · obtain ⟨staged, reached, liftedNext, adaptedNext⟩ := ih _
                (SourceExecutionSize.child_lt_stepSize (by simp))
                (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
                nextReady (.control next)
              exact ⟨staged, reached, .continueIterate liftedTest liftedBody liftedPost liftedNext, adaptedNext⟩

      | breaks testTrace bodyTrace =>
        rcases test_value bridge functions condition children preservation found typed generated ready
          (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within) testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge functions condition body testReady
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            exact ⟨_, _, .forBreakFromBody liftedTest liftedBody, .completed (.fallthrough environment)⟩
      | returns testTrace bodyTrace =>
        rcases test_value bridge functions condition children preservation found typed generated ready
          (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within) testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge functions condition body testReady
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            exact ⟨_, _, .returnedFromBody liftedTest liftedBody, .completed (.returned _)⟩
    | fault trace =>
      cases trace with
      | condition failed =>
        obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
          initial, conditioned, admitted⟩ := ready
        obtain ⟨staged, reached, lifted, adapted⟩ := children _
          (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within) generated found typed
          environments heaps locals agrees actualTyped initial admitted (.fault failed)
        cases adapted with
        | completed => exact ⟨_, _, .testFault lifted, .completed (.fault _)⟩
        | rejected origin call reason reached =>
          exact ⟨_, reached, .testFault lifted, .rejected origin call reason context reached⟩
      | conditionType testTrace notBoolean _ =>
        rcases test_value bridge functions condition children preservation found typed generated ready
          (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within) testTrace with
          stopped | ⟨_, _, valueTyped⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · exact False.elim (notBoolean valueTyped)
      | body testTrace bodyTrace =>
        rcases test_value bridge functions condition children preservation found typed generated ready
          (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within) testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge functions condition body testReady
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
              (.fault bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .completed (.fault _)⟩
      | postFallthrough testTrace bodyTrace failed =>
        rcases test_value bridge functions condition children preservation found typed generated ready
          (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within) testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge functions condition body testReady
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have bodyReady := body_ready bridge functions condition bodyPreservation testReady liftedBody
            obtain ⟨last, stagedPost, reached, liftedPost, adaptedPost⟩ := postLift
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
              bodyReady (.fault failed)
            cases stagedPost with
            | done env => cases adaptedPost with | completed matched => cases matched
            | fault reason =>
              cases adaptedPost with
              | completed matched =>
                cases matched
                exact ⟨_, _, .postFailure liftedTest liftedBody liftedPost, .completed (.fault _)⟩
              | rejected origin call reason finalContext reached =>
                exact ⟨_, reached, .postFailure liftedTest liftedBody liftedPost,
                  .rejected origin call reason context reached⟩
      | postContinue testTrace bodyTrace failed =>
        rcases test_value bridge functions condition children preservation found typed generated ready
          (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within) testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge functions condition body testReady
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have bodyReady := body_continue_ready bridge functions condition bodyPreservation testReady liftedBody
            obtain ⟨last, stagedPost, reached, liftedPost, adaptedPost⟩ := postLift
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
              bodyReady (.fault failed)
            cases stagedPost with
            | done env => cases adaptedPost with | completed matched => cases matched
            | fault reason =>
              cases adaptedPost with
              | completed matched =>
                cases matched
                exact ⟨_, _, .continuePostFailure liftedTest liftedBody liftedPost, .completed (.fault _)⟩
              | rejected origin call reason finalContext reached =>
                exact ⟨_, reached, .continuePostFailure liftedTest liftedBody liftedPost,
                  .rejected origin call reason context reached⟩
      | nextFallthrough testTrace bodyTrace postTrace next =>
        rcases test_value bridge functions condition children preservation found typed generated ready
          (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within) testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge functions condition body testReady
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have bodyReady := body_ready bridge functions condition bodyPreservation testReady liftedBody
            rcases post_value bridge functions condition postLift postPreservation bodyReady
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within) postTrace with
              stopped | ⟨liftedPost, nextReady⟩
            · obtain ⟨failedContext, origin, call, reason, reached, stopped⟩ := stopped
              exact ⟨_, reached, .postFailure liftedTest liftedBody stopped,
                .rejected origin call reason context reached⟩
            · obtain ⟨staged, reached, liftedNext, adaptedNext⟩ := ih _
                (SourceExecutionSize.child_lt_stepSize (by simp))
                (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
                nextReady (.fault next)
              exact ⟨staged, reached, .iterate liftedTest liftedBody liftedPost liftedNext, adaptedNext⟩
      | nextContinue testTrace bodyTrace postTrace next =>
        rcases test_value bridge functions condition children preservation found typed generated ready
          (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within) testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge functions condition body testReady
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have bodyReady := body_continue_ready bridge functions condition bodyPreservation testReady liftedBody
            rcases post_value bridge functions condition postLift postPreservation bodyReady
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within) postTrace with
              stopped | ⟨liftedPost, nextReady⟩
            · obtain ⟨failedContext, origin, call, reason, reached, stopped⟩ := stopped
              exact ⟨_, reached, .continuePostFailure liftedTest liftedBody stopped,
                .rejected origin call reason context reached⟩
            · obtain ⟨staged, reached, liftedNext, adaptedNext⟩ := ih _
                (SourceExecutionSize.child_lt_stepSize (by simp))
                (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
                nextReady (.fault next)
              exact ⟨staged, reached, .continueIterate liftedTest liftedBody liftedPost liftedNext, adaptedNext⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForLifting
