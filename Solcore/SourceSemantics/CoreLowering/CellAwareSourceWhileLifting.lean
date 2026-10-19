import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowReadiness
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageWhileLifting

/-! Independent Source while execution follows the actual mixed continuation.
Repeated and continued iterations retain all descriptor bundles; a genuine
earlier stage rejection records its reached heap and stops the remaining loop. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceWhileLifting
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
open SelectedCompilationStageWhileLifting (PlainWhile WhileLift)
variable {certificate : GenericExpressionMeaning.Certificate}
  {test : ExpressionId} {node : ExpressionNode} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {testCode loopCode : Expr}
variable {environment : Dynamic.Environment} {canonical actual : Environment}
  {actualContext : Core.Context} {embedding : Renaming}

local notation "ReadyAt" => Ready (named := named) (administrative := administrative)
  (invocation := invocation) (context := context) (scope := scope)
  bridge producer environment canonical actual actualContext embedding

theorem body_continue_ready {before after : Dynamic.Heap} {finalContext : SourceSemantics.Context}
    {finalEnvironment : Dynamic.Environment} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (preservation : ∀ size, CellAwareScopeFlowBounds.PreservesAt bridge context model named producer registry invocation faults
      administrative scope false statements expected type code size)
    (sourceTyped : ProtectedStateImperativeTypedSourceSites.Statements (source named) context statements)
    (ready : ReadyAt before)
    (trace : Staging.Recursive.StatementsIn program registry false invocation context environment before statements
      finalContext (.continuing finalEnvironment) after) : ReadyAt after := by
  obtain ⟨mapping,world,store,environments,heaps,locals,agrees,actualTyped,runtime,covers,sameLedger,
    initial,admitted,authority,physical,owner,sameLocation,allocationReady⟩ := ready
  obtain ⟨size,measured⟩ := Staging.Recursive.Size.StatementsIn.of_trace trace
  obtain ⟨_,finalStore,finalMap,finalWorld,_,_,finalHeaps,maps,worlds,preserved,metadata,effect,
    last,_,post⟩ := preservation size environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation allocationReady measured
  exact ⟨finalMap,finalWorld,finalStore,environments.extend maps worlds,finalHeaps,
    locals.mono metadata,agrees,actualTyped.weaken worlds,runtime,covers,sameLedger,
    last,post,authority.transport effect,physical.transport effect preserved,owner,sameLocation,allocationReady⟩

theorem while_ready
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
    {size : Nat} {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (ready : ReadyAt before)
    (trace : PlainWhile program size invocation context environment before test statements outcome after) :
    WhileLift program registry invocation context environment before test statements outcome after := by
  induction size using Nat.strongRecOn generalizing before after outcome with
  | ind size ih =>
    cases trace with
    | control trace =>
      cases trace with
      | done testTrace =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨lifted, _, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · exact ⟨_, _, .done lifted, .completed (.fallthrough environment)⟩
      | nextFallthrough testTrace bodyTrace next =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFault liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have nextReady := body_ready bridge producer bodyPreservation bodyTyped testReady liftedBody
            obtain ⟨staged, reached, liftedNext, adaptedNext⟩ := ih _
              (SourceExecutionSize.child_lt_stepSize (by simp))
              nextReady (.control next)
            exact ⟨staged, reached, .next liftedTest liftedBody liftedNext, adaptedNext⟩
      | nextContinue testTrace bodyTrace next =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFault liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have nextReady := body_continue_ready bridge producer bodyPreservation bodyTyped testReady liftedBody
            obtain ⟨staged, reached, liftedNext, adaptedNext⟩ := ih _
              (SourceExecutionSize.child_lt_stepSize (by simp))
              nextReady (.control next)
            exact ⟨staged, reached, .continueNext liftedTest liftedBody liftedNext, adaptedNext⟩

      | breaks testTrace bodyTrace =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFault liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            exact ⟨_, _, .breakFromBody liftedTest liftedBody, .completed (.fallthrough environment)⟩
      | returns testTrace bodyTrace =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFault liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            exact ⟨_, _, .returned liftedTest liftedBody, .completed (.returned _)⟩
    | fault trace =>
      cases trace with
      | condition failed =>
        obtain ⟨mapping,world,store,environments,heaps,locals,agrees,actualTyped,_runtime,_covers,_sameLedger,
          initial,admitted,authority,physical,owner,sameLocation,_allocationReady⟩ := ready
        obtain ⟨staged, reached, lifted, adapted⟩ := children _ generated found typed
          environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation (.fault failed)
        cases adapted with
        | completed => exact ⟨_, _, .conditionFault lifted, .completed (.fault _)⟩
        | rejected origin call reason reached =>
          exact ⟨_, reached, .conditionFault lifted, .rejected origin call reason context reached⟩
      | conditionType testTrace notBoolean _ =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨_, _, valueTyped⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · exact False.elim (notBoolean valueTyped)
      | body testTrace bodyTrace =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.fault bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFault liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            exact ⟨_, _, .bodyFault liftedTest liftedBody, .completed (.fault _)⟩
      | nextFallthrough testTrace bodyTrace next =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFault liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have nextReady := body_ready bridge producer bodyPreservation bodyTyped testReady liftedBody
            obtain ⟨staged, reached, liftedNext, adaptedNext⟩ := ih _
              (SourceExecutionSize.child_lt_stepSize (by simp))
              nextReady (.fault next)
            exact ⟨staged, reached, .next liftedTest liftedBody liftedNext, adaptedNext⟩
      | nextContinue testTrace bodyTrace next =>
        rcases test_value bridge producer children preservation booleans found nodeType typed generated ready testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge producer body bodyTyped testReady
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFault liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have nextReady := body_continue_ready bridge producer bodyPreservation bodyTyped testReady liftedBody
            obtain ⟨staged, reached, liftedNext, adaptedNext⟩ := ih _
              (SourceExecutionSize.child_lt_stepSize (by simp))
              nextReady (.fault next)
            exact ⟨staged, reached, .continueNext liftedTest liftedBody liftedNext, adaptedNext⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceWhileLifting
