import Solcore.SourceSemantics.CoreLowering.CellAwareSourceForLiftBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowReadiness
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceWhileLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForLiftBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeForPostBounds

/-! Independent Source for-loop headers use the same reached mixed state as
ordinary statements. Source and native grades are independent. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open SelectedCompilationStageBodyLiftBounds

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}

open CellAwareSourceFlowReadiness (Ready body_prefix body_ready test_value)
open SelectedCompilationStageForLiftBounds (PlainItems ItemsLift PlainFor ForLift)
variable {certificate : GenericExpressionMeaning.Certificate}
  {test : ExpressionId} {node : ExpressionNode} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {testCode loopCode postCode : Expr} {post : List ForItemForm}
variable {environment : Dynamic.Environment} {canonical actual : Environment}
  {actualContext : Core.Context} {embedding : Renaming}

open CellAwareSourceForLiftBounds (ItemsLifts)
open CellAwareSourceWhileLifting (body_continue_ready)

local notation "ReadyAt" => Ready (named := named) (administrative := administrative)
  (invocation := invocation) (context := context) (scope := scope)
  bridge producer environment canonical actual actualContext embedding

theorem post_ready {before after : Dynamic.Heap} {finalContext : SourceSemantics.Context}
    {finalEnvironment : Dynamic.Environment}
    (preservation : ∀ size, CellAwareScopeForPostBounds.PreservesAt bridge context model named producer
      registry invocation faults administrative scope post expected type postCode size)
    (postTyped : ∃ control final, ForItemsHaveType (source named) control context post final)
    (ready : ReadyAt before)
    (trace : Staging.Recursive.ForItems program registry invocation context environment before post
      finalContext (.done finalEnvironment) after) : ReadyAt after := by
  obtain ⟨mapping,world,store,environments,heaps,locals,agrees,actualTyped,runtime,covers,sameLedger,
    initial,admitted,authority,physical,owner,sameLocation,allocationReady⟩ := ready
  obtain ⟨size,measured⟩ := Staging.Recursive.Size.ForItems.of_trace trace
  obtain ⟨_,finalStore,finalMap,finalWorld,_,_,finalHeaps,maps,worlds,preserved,metadata,effect,
    last,_,post⟩ := preservation size environments heaps locals agrees actualTyped runtime covers sameLedger postTyped
      initial admitted authority physical owner sameLocation allocationReady measured
  exact ⟨finalMap,finalWorld,finalStore,environments.extend maps worlds,finalHeaps,
    locals.mono metadata,agrees,actualTyped.weaken worlds,runtime,covers,sameLedger,
    last,post,authority.transport effect,physical.transport effect preserved,owner,sameLocation,allocationReady⟩

theorem post_value {size : Nat} {before after : Dynamic.Heap}
    {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment}
    (postLift : ItemsLifts (named := named) (administrative := administrative) (context := context)
      (scope := scope) (registry := registry) (invocation := invocation) bridge producer post)
    (postPreservation : ∀ size, CellAwareScopeForPostBounds.PreservesAt bridge context model named producer
      registry invocation faults administrative scope post expected type postCode size)
    (postTyped : ∃ control final, ForItemsHaveType (source named) control context post final)
    (ready : ReadyAt before)
    (trace : SourceExecutionSize.ForItemsExecute program size context invocation.evidence invocation.source
      environment before post finalContext finalEnvironment after) :
    (∃ failedContext origin call reason reached,
      Staging.Recursive.ForItems program registry invocation context environment before post
        failedContext (.fault (.stage origin call reason)) reached) ∨
    (Staging.Recursive.ForItems program registry invocation context environment before post
      finalContext (.done finalEnvironment) after ∧ ReadyAt after) := by
  obtain ⟨last,staged,reached,lifted,adapted⟩ := postLift ready (.done trace)
  cases staged with
  | done env =>
    cases adapted with
    | completed matched =>
      cases matched
      exact .inr ⟨lifted,post_ready bridge producer postPreservation postTyped ready lifted⟩
  | fault reason =>
    cases adapted with
    | completed matched => cases matched
    | rejected origin call reason finalContext reached =>
      exact .inl ⟨_,origin,call,reason,reached,lifted⟩

theorem for_ready
    (children : ∀ childSize, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation certificate childSize)
    (preservation : ∀ childSize, CellAwareScopeExpressionBounds.PreservesAt
      bridge context model named registry invocation certificate faults childSize)
    (booleans : ∀ {mapping world sourceValue nativeValue},
      model.Represents mapping world .bool sourceValue nativeValue .bool →
      ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (body : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope false statements)
    (bodyPreservation : ∀ size, CellAwareScopeFlowBounds.PreservesAt bridge context model named producer registry invocation faults
      administrative scope false statements expected type loopCode size)
    (bodyTyped : ProtectedStateImperativeTypedSourceSites.Statements (source named) context statements)
    (postLift : ItemsLifts (named := named) (administrative := administrative) (context := context)
      (scope := scope) (registry := registry) (invocation := invocation) bridge producer post)
    (postPreservation : ∀ size, CellAwareScopeForPostBounds.PreservesAt bridge context model named producer
      registry invocation faults administrative scope post expected type postCode size)
    (postTyped : ∃ control final, ForItemsHaveType (source named) control context post final)
    {size : Nat} {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (ready : ReadyAt before)
    (trace : PlainFor program size invocation context environment before test post statements outcome after) :
    ForLift program registry invocation context environment before test post statements outcome after := by
  induction size using Nat.strongRecOn generalizing before after outcome with
  | ind size ih =>
    cases trace with
    | control trace =>
      cases trace with
      | done testTrace =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨lifted, _, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · exact ⟨_, _, .finished lifted, .completed (.fallthrough environment)⟩
      | nextFallthrough testTrace bodyTrace postTrace next =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have bodyReady := body_ready bridge producer bodyPreservation bodyTyped testReady liftedBody
            rcases post_value bridge producer postLift postPreservation postTyped bodyReady postTrace with
              stopped | ⟨liftedPost, nextReady⟩
            · obtain ⟨failedContext, origin, call, reason, reached, stopped⟩ := stopped
              exact ⟨_, reached, .postFailure liftedTest liftedBody stopped,
                .rejected origin call reason context reached⟩
            · obtain ⟨staged, reached, liftedNext, adaptedNext⟩ := ih _
                (SourceExecutionSize.child_lt_stepSize (by simp))
                nextReady (.control next)
              exact ⟨staged, reached, .iterate liftedTest liftedBody liftedPost liftedNext, adaptedNext⟩
      | nextContinue testTrace bodyTrace postTrace next =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have bodyReady := body_continue_ready bridge producer bodyPreservation bodyTyped testReady liftedBody
            rcases post_value bridge producer postLift postPreservation postTyped bodyReady postTrace with
              stopped | ⟨liftedPost, nextReady⟩
            · obtain ⟨failedContext, origin, call, reason, reached, stopped⟩ := stopped
              exact ⟨_, reached, .continuePostFailure liftedTest liftedBody stopped,
                .rejected origin call reason context reached⟩
            · obtain ⟨staged, reached, liftedNext, adaptedNext⟩ := ih _
                (SourceExecutionSize.child_lt_stepSize (by simp))
                nextReady (.control next)
              exact ⟨staged, reached, .continueIterate liftedTest liftedBody liftedPost liftedNext, adaptedNext⟩

      | breaks testTrace bodyTrace =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            exact ⟨_, _, .forBreakFromBody liftedTest liftedBody, .completed (.fallthrough environment)⟩
      | returns testTrace bodyTrace =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
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
        obtain ⟨mapping,world,store,environments,heaps,locals,agrees,actualTyped,_runtime,_covers,_sameLedger,
          initial,admitted,authority,physical,owner,sameLocation,_allocationReady⟩ := ready
        obtain ⟨staged, reached, lifted, adapted⟩ := children _ generated found typed
          environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation (.fault failed)
        cases adapted with
        | completed => exact ⟨_, _, .testFault lifted, .completed (.fault _)⟩
        | rejected origin call reason reached =>
          exact ⟨_, reached, .testFault lifted, .rejected origin call reason context reached⟩
      | conditionType testTrace notBoolean _ =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨_, _, valueTyped⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · exact False.elim (notBoolean valueTyped)
      | body testTrace bodyTrace =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.fault bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .completed (.fault _)⟩
      | postFallthrough testTrace bodyTrace failed =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have bodyReady := body_ready bridge producer bodyPreservation bodyTyped testReady liftedBody
            obtain ⟨last, stagedPost, reached, liftedPost, adaptedPost⟩ := postLift
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
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have bodyReady := body_continue_ready bridge producer bodyPreservation bodyTyped testReady liftedBody
            obtain ⟨last, stagedPost, reached, liftedPost, adaptedPost⟩ := postLift
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
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have bodyReady := body_ready bridge producer bodyPreservation bodyTyped testReady liftedBody
            rcases post_value bridge producer postLift postPreservation postTyped bodyReady postTrace with
              stopped | ⟨liftedPost, nextReady⟩
            · obtain ⟨failedContext, origin, call, reason, reached, stopped⟩ := stopped
              exact ⟨_, reached, .postFailure liftedTest liftedBody stopped,
                .rejected origin call reason context reached⟩
            · obtain ⟨staged, reached, liftedNext, adaptedNext⟩ := ih _
                (SourceExecutionSize.child_lt_stepSize (by simp))
                nextReady (.fault next)
              exact ⟨staged, reached, .iterate liftedTest liftedBody liftedPost liftedNext, adaptedNext⟩
      | nextContinue testTrace bodyTrace postTrace next =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .testFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFailure liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have bodyReady := body_continue_ready bridge producer bodyPreservation bodyTyped testReady liftedBody
            rcases post_value bridge producer postLift postPreservation postTyped bodyReady postTrace with
              stopped | ⟨liftedPost, nextReady⟩
            · obtain ⟨failedContext, origin, call, reason, reached, stopped⟩ := stopped
              exact ⟨_, reached, .continuePostFailure liftedTest liftedBody stopped,
                .rejected origin call reason context reached⟩
            · obtain ⟨staged, reached, liftedNext, adaptedNext⟩ := ih _
                (SourceExecutionSize.child_lt_stepSize (by simp))
                nextReady (.fault next)
              exact ⟨staged, reached, .continueIterate liftedTest liftedBody liftedPost liftedNext, adaptedNext⟩


end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForLifting
