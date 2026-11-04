import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageStatements
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageExpressions
import Solcore.SourceSemantics.Staging.RecursiveBareBitNotFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerBitNotSource
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedBareBitNotHeads

/-!
# Lifting to staged Source: for loops

Bounds and sequences of `for` lifting, and the Source inversions of loops and their items.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForLiftBounds
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForLiftBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageWhileLifting
universe u

inductive PlainItems (program : Program) (size : Nat) (invocation : Staging.Recursive.Scope)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (items : List ForItemForm) : SourceSemantics.Context → Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | done {finalContext finalEnvironment after}
      (trace : SourceExecutionSize.ForItemsExecute program size context invocation.evidence invocation.source
        environment before items finalContext finalEnvironment after) :
      PlainItems program size invocation context environment before items finalContext (.fallthrough finalEnvironment) after
  | fault {finalContext reason after}
      (trace : SourceExecutionSize.ForItemsFault program size context invocation.evidence invocation.source
        environment before items finalContext reason after) :
      PlainItems program size invocation context environment before items finalContext (.fault reason) after

def itemsControl : Staging.Recursive.ForItemsOutcome → Staging.Recursive.BodyOutcome
  | .done environment => .fallthrough environment
  | .fault reason => .fault reason

def ItemsLift (program : Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (items : List ForItemForm) (finalContext : SourceSemantics.Context) (outcome : Dynamic.ControlOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ stagedContext staged reached,
    Staging.Recursive.ForItems program stages invocation context environment before items stagedContext staged reached ∧
    BodyAdapted finalContext outcome after stagedContext (itemsControl staged) reached

inductive PlainFor (program : Program) (size : Nat) (invocation : Staging.Recursive.Scope)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (test : ExpressionId) (post : List ForItemForm) (statements : List StatementId) : Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | control {outcome after}
      (trace : SourceExecutionSize.ForLoopExecutes program size context invocation.evidence invocation.source
        environment before test post statements context outcome after) :
      PlainFor program size invocation context environment before test post statements outcome after
  | fault {reason after}
      (trace : SourceExecutionSize.ForLoopFaults program size context invocation.evidence invocation.source
        environment before test post statements reason after) :
      PlainFor program size invocation context environment before test post statements (.fault reason) after

def ForLift (program : Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (test : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (outcome : Dynamic.ControlOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ staged reached,
    Staging.Recursive.ForLoop program stages invocation context environment before test post statements staged reached ∧
    BodyAdapted context outcome after context staged reached

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
  {expected : TypeSystem.Ty} {type : Ty} {testCode loopCode : Expr}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

def ItemsLifts (items : List ForItemForm) (budget : Nat) : Prop :=
  ∀ {size : Nat}, size ≤ budget →
  ∀ {environment : Dynamic.Environment} {canonical actual : Environment} {actualContext : Core.Context}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {before after : Dynamic.Heap},
    PhysicalReady (administrative := administrative) (receiving := receiving) (frame := frame)
      (globals := globals) (context := context) (scope := scope)
      bridge functions condition environment canonical actual actualContext ξ contextLocation native before →
    ∀ {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome},
      PlainItems program size invocation context environment before items finalContext outcome after →
      ItemsLift program stages invocation context environment before items finalContext outcome after

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForLiftBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsSourceInversion
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsSourceInversion
open Frontend SourceInference
open SelectedCompilationStageForLiftBounds

variable {program : Program} {invocation : Staging.Recursive.Scope}
  {context nextContext finalContext : SourceSemantics.Context}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {items : List ForItemForm} {binder : TypedBinder} {expression : ExpressionId}
  {size : Nat} {outcome : Dynamic.ControlOutcome}

theorem nil (trace : PlainItems program size invocation context environment before [] finalContext outcome after) :
    finalContext = context ∧ outcome = .fallthrough environment ∧ after = before := by
  cases trace with
  | done trace => cases trace; exact ⟨rfl, rfl, rfl⟩
  | fault trace => cases trace

theorem absent (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : PlainItems program size invocation context environment before
      (.letDecl binder none :: items) finalContext outcome after) :
    ∃ tailSize location bound, tailSize < size ∧
      Dynamic.Heap.Allocates before binder.scheme.body none location bound ∧
      PlainItems program tailSize invocation nextContext ((binder.id, location) :: environment)
        bound items finalContext outcome after := by
  cases trace with
  | done trace =>
    cases trace with
    | cons head tail =>
      cases head with
      | letUninitialized _ extension allocated =>
        cases Dynamic.BinderExtends.functional extended extension
        exact ⟨_, _, _, SourceExecutionSize.child_lt_stepSize (by simp), allocated, .done tail⟩
  | fault trace =>
    cases trace with
    | head failed => cases failed; contradiction
    | tail head failed =>
      cases head with
      | letUninitialized _ extension allocated =>
        cases Dynamic.BinderExtends.functional extended extension
        exact ⟨_, _, _, SourceExecutionSize.child_lt_stepSize (by simp), allocated, .fault failed⟩

theorem initialized (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : PlainItems program size invocation context environment before
      (.letDecl binder (some expression) :: items) finalContext outcome after) :
    (∃ child reason, child < size ∧ finalContext = context ∧ outcome = .fault reason ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before expression (.fault reason) after) ∨
    (∃ child tailSize value middle location bound, child < size ∧ tailSize < size ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before expression (.value value) middle ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location bound ∧
      PlainItems program tailSize invocation nextContext ((binder.id, location) :: environment)
        bound items finalContext outcome after) := by
  cases trace with
  | done trace =>
    cases trace with
    | cons head tail =>
      cases head with
      | letInitialized evaluated _ extension allocated =>
        cases Dynamic.BinderExtends.functional extended extension
        refine .inr ⟨_, _, _, _, _, _, ?_, SourceExecutionSize.child_lt_stepSize (by simp), .value evaluated, allocated, .done tail⟩
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega
      | letInitializedGeneralized _ _ poly => exact (poly mono).elim
  | fault trace =>
    cases trace with
    | head failed =>
      cases failed with
      | polymorphicLet poly => exact (poly mono).elim
      | letInitializer _ failed =>
        refine .inl ⟨_, _, ?_, rfl, rfl, .fault failed⟩
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega
    | tail head failed =>
      cases head with
      | letInitialized evaluated _ extension allocated =>
        cases Dynamic.BinderExtends.functional extended extension
        refine .inr ⟨_, _, _, _, _, _, ?_, SourceExecutionSize.child_lt_stepSize (by simp), .value evaluated, allocated, .fault failed⟩
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega
      | letInitializedGeneralized _ _ poly => exact (poly mono).elim

theorem discard (trace : PlainItems program size invocation context environment before
      (.expression expression :: items) finalContext outcome after) :
    (∃ child reason, child < size ∧ finalContext = context ∧ outcome = .fault reason ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before expression (.fault reason) after) ∨
    (∃ child tailSize value middle, child < size ∧ tailSize < size ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before expression (.value value) middle ∧
      PlainItems program tailSize invocation context environment middle items finalContext outcome after) := by
  cases trace with
  | done trace =>
    cases trace with
    | cons head tail =>
      cases head with
      | expression evaluated =>
        refine .inr ⟨_, _, _, _, ?_, SourceExecutionSize.child_lt_stepSize (by simp), .value evaluated, .done tail⟩
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega
  | fault trace =>
    cases trace with
    | head failed =>
      cases failed with
      | expression failed =>
        refine .inl ⟨_, _, ?_, rfl, rfl, .fault failed⟩
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega
    | tail head failed =>
      cases head with
      | expression evaluated =>
        refine .inr ⟨_, _, _, _, ?_, SourceExecutionSize.child_lt_stepSize (by simp), .value evaluated, .fault failed⟩
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsSourceInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForLifting
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialBounds
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageWhileLifting
open SelectedCompilationStageForLiftBounds
universe u

inductive PlainInitial (program : Program) (invocation : Staging.Recursive.Scope)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (items : List ForItemForm) (test : ExpressionId) (post : List ForItemForm) (statements : List StatementId) :
    Nat → Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | initializerFault {size finalContext reason after}
      (trace : SourceExecutionSize.ForItemsFault program size context invocation.evidence invocation.source
        environment before items finalContext reason after) :
      PlainInitial program invocation context environment before items test post statements
        (SourceExecutionSize.stepSize [size]) (.fault reason) after
  | loop {initialSize loopSize loopContext loopEnvironment middle outcome after}
      (initial : SourceExecutionSize.ForItemsExecute program initialSize context invocation.evidence invocation.source
        environment before items loopContext loopEnvironment middle)
      (trace : PlainFor program loopSize invocation loopContext loopEnvironment middle test post statements outcome after) :
      PlainInitial program invocation context environment before items test post statements
        (SourceExecutionSize.stepSize [initialSize, loopSize]) (Dynamic.restoreControl environment outcome) after

def InitialLift (program : Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (items : List ForItemForm) (test : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (outcome : Dynamic.ControlOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ size staged reached,
    CallableIndexedOwnedAdmittedStagedForHeadContracts.Trace program stages invocation context environment before
      items test post statements size staged reached ∧
    BodyAdapted context outcome after context staged reached

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
  {expected : TypeSystem.Ty} {type : Ty} {testCode loopCode : Expr}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

def InitializersLifts (items : List ForItemForm) (test : ExpressionId) (post : List ForItemForm)
    (statements : List StatementId) (budget : Nat) : Prop :=
  ∀ {size : Nat}, size ≤ budget →
  ∀ {environment : Dynamic.Environment} {canonical actual : Environment} {actualContext : Core.Context}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {before after : Dynamic.Heap},
    PhysicalReady (administrative := administrative) (receiving := receiving) (frame := frame)
      (globals := globals) (context := context) (scope := scope)
      bridge functions condition environment canonical actual actualContext ξ contextLocation native before →
    ∀ {outcome : Dynamic.ControlOutcome},
      PlainInitial program invocation context environment before items test post statements size outcome after →
      InitialLift program stages invocation context environment before items test post statements outcome after

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForSourceInversion
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForSourceInversion
open Frontend SourceInference
open SelectedCompilationStageForLiftBounds SelectedCompilationStageForInitialBounds

private theorem loop_fields {program : Program} {source : TypedSource}
    {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {test : ExpressionId} {body : List StatementId} {post : List ForItemForm} {size : Nat} {outcome : Dynamic.ControlOutcome}
    (trace : SourceExecutionSize.ForLoopExecutes program size context evidence source environment before
      test post body finalContext outcome after) :
    finalContext = context ∧ Dynamic.restoreControl environment outcome = outcome := by
  induction size using Nat.strongRecOn generalizing before after outcome finalContext with
  | ind size ih =>
    cases trace with
    | done => exact ⟨rfl, rfl⟩
    | breaks => exact ⟨rfl, rfl⟩
    | returns => exact ⟨rfl, rfl⟩
    | nextFallthrough _ _ _ next | nextContinue _ _ _ next =>
      exact ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) next

theorem control {program : Program} {invocation : Staging.Recursive.Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode}
    {test : ExpressionId} {items post : List ForItemForm} {body : List StatementId}
    {size : Nat} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .forLoop items test post body)
    (trace : SourceExecutionSize.StatementExecutes program size context invocation.evidence invocation.source
      environment before id finalContext outcome after) :
    finalContext = context ∧
      PlainInitial program invocation context environment before items test post body size outcome after := by
  have sameNode : ∀ {other}, ContainsStatement invocation.source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace <;> have same := sameNode (by assumption) <;> subst_vars <;> simp_all
  obtain ⟨sameContext, _⟩ := loop_fields (by assumption)
  subst_vars
  exact .loop (by assumption) (.control (by assumption))

theorem fault {program : Program} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode}
    {test : ExpressionId} {items post : List ForItemForm} {body : List StatementId}
    {size : Nat} {reason : Dynamic.SemanticFault}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .forLoop items test post body)
    (trace : SourceExecutionSize.StatementFaults program size context invocation.evidence invocation.source
      environment before id reason after) :
    PlainInitial program invocation context environment before items test post body size (.fault reason) after := by
  have sameNode : ∀ {other}, ContainsStatement invocation.source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  all_goals have same := sameNode (by assumption)
  all_goals subst_vars; simp_all
  · exact .initializerFault (by assumption)
  · exact .loop (by assumption) (.fault (by assumption))

theorem fallthrough_environment {program : Program} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment nextEnvironment : Dynamic.Environment}
    {before after : Dynamic.Heap} {test : ExpressionId} {items post : List ForItemForm} {body : List StatementId}
    {size : Nat}
    (trace : PlainInitial program invocation context environment before items test post body size
      (.fallthrough nextEnvironment) after) : nextEnvironment = environment := by
  generalize same : Dynamic.ControlOutcome.fallthrough nextEnvironment = result at trace
  cases trace with
  | initializerFault => cases same
  | @loop _ _ _ _ _ outcome _ initial trace =>
    cases outcome <;> simp_all [Dynamic.restoreControl]

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForSourceInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForSequenceLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForSequenceLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageWhileLifting
open SelectedCompilationStageForInitialBounds
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
  {test : ExpressionId} {node : ExpressionNode} {statements : List StatementId} {items postItems : List ForItemForm}
  {expected : TypeSystem.Ty} {type : Ty} {initialCode : Expr}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions


variable {mode : Bool} {id : StatementId} {statement : StatementNode}
  {rest : List StatementId} {selfReason : Word}

/-- Lift the actual for head and precisely the suffix reached after normal
completion. Earlier returns and genuine failures retain their original scope. -/
theorem lifts {budget : Nat}
    (initialLift : InitializersLifts (administrative := administrative) (receiving := receiving) (frame := frame)
      (globals := globals) (context := context) (scope := scope) (stages := stages) (invocation := invocation)
      bridge functions condition items test postItems statements budget)
    (initialPreservation : ∀ n, CallableIndexedOwnedAdmittedStagedForHeadContracts.Preserves
      (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope items test postItems statements expected type initialCode n)
    (unique : NodeOccurrencesUnique invocation.source)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .forLoop items test postItems statements)
    (remaining : FlowLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) bridge functions condition context scope mode rest budget) :
    FlowLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) bridge functions condition context scope mode (id :: rest) budget := by
  intro size within mapping world actualContext environment canonical actual before store ξ contextLocation native
    environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
    finalContext outcome after trace
  have ready : PhysicalReady (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (context := context) (scope := scope)
      bridge functions condition environment canonical actual actualContext ξ contextLocation native before :=
    ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
      initial, conditioned, admitted⟩
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique statementFound
    (by intro expression equal; rw [form] at equal; cases equal) trace with
    ⟨headSize, reason, headSmaller, rfl, rfl, failed⟩ |
    ⟨headSize, headSmaller, terminal, executed⟩ |
    ⟨headSize, tailSize, middleContext, nextEnvironment, middle, headSmaller, tailSmaller, executed, tail⟩
  · have loop := SelectedCompilationStageForSourceInversion.fault unique statementFound form failed
    obtain ⟨stagedSize, staged, reached, lifted, adapted⟩ := initialLift
      (Nat.le_trans (Nat.le_of_lt headSmaller) within) ready loop
    cases adapted with
    | completed matched =>
      cases matched
      exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.fault statementFound form lifted).sound, .completed (.fault reason)⟩
    | rejected origin call reason finalContext reached =>
      exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.fault statementFound form lifted).sound,
        .rejected origin call reason _ _⟩
  · obtain ⟨rfl, loop⟩ := SelectedCompilationStageForSourceInversion.control unique statementFound form executed
    obtain ⟨stagedSize, staged, reached, lifted, adapted⟩ := initialLift
      (Nat.le_trans (Nat.le_of_lt headSmaller) within) ready loop
    cases adapted with
    | rejected origin call reason finalContext reached =>
      exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.fault statementFound form lifted).sound,
        .rejected origin call reason _ _⟩
    | completed matched =>
      cases matched with
      | breaking innerEnvironment => exact ((CallableIndexedOwnedAdmittedStagedForSourceBridge.closed lifted).1 innerEnvironment rfl).elim
      | continuing innerEnvironment => exact ((CallableIndexedOwnedAdmittedStagedForSourceBridge.closed lifted).2 innerEnvironment rfl).elim
      | returned value =>
        exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.returned statementFound form lifted).sound, .completed (.returned value)⟩
      | fault reason =>
        exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.fault statementFound form lifted).sound, .completed (.fault reason)⟩
      | fallthrough innerEnvironment =>
        cases SelectedCompilationStageForSourceInversion.fallthrough_environment loop
        rcases terminal with terminal | rfl
        · cases terminal
        · exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.fallthrough statementFound form lifted .nil).sound,
            .completed (.fallthrough environment)⟩
  · obtain ⟨rfl, loop⟩ := SelectedCompilationStageForSourceInversion.control unique statementFound form executed
    cases SelectedCompilationStageForSourceInversion.fallthrough_environment loop
    obtain ⟨stagedSize, staged, reached, lifted, adapted⟩ := initialLift
      (Nat.le_trans (Nat.le_of_lt headSmaller) within) ready loop
    cases adapted with
    | rejected origin call reason finalContext reached =>
      exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.fault statementFound form lifted).sound,
        .rejected origin call reason _ _⟩
    | completed matched =>
      cases matched
      obtain ⟨_, finalStore, finalMap, finalWorld, _, _, finalHeaps, maps, worlds, preserved, metadata,
        last, _, post⟩ := initialPreservation stagedSize (Nat.le_refl _) environments heaps locals agrees actualTyped
          reference read unmapped initial conditioned admitted lifted
      obtain ⟨tailContext, tailOutcome, tailHeap, liftedTail, adaptedTail⟩ := remaining
        (Nat.le_trans (Nat.le_of_lt tailSmaller) within)
        (environments.extend maps worlds) finalHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
        reference ((preserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
        (preserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 last conditioned post tail
      obtain ⟨tailGrade, tailMeasured⟩ := Staging.Recursive.Size.StatementsIn.of_trace liftedTail
      exact ⟨tailContext, tailOutcome, tailHeap,
        (CallableIndexedOwnedAdmittedStagedForSourceBridge.fallthrough statementFound form lifted tailMeasured).sound,
        adaptedTail⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForSequenceLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsAssignmentInversion
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsAssignmentInversion
open Frontend SourceInference
open SelectedCompilationStageForLiftBounds
open Staging.Recursive (BareTarget)

private theorem target_functional {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {place : PlaceResolution} {left right : Dynamic.ResolvedPlace}
    (first : BareTarget environment heap place left) (second : BareTarget environment heap place right) : left = right := by
  cases first with
  | intro _ leftLookup leftRead leftValue =>
    cases second with
    | intro _ rightLookup rightRead rightValue =>
      cases leftLookup.functional rightLookup
      cases leftRead.functional rightRead
      cases leftValue.functional rightValue
      rfl

private theorem resolve_same {program : Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {place : PlaceResolution} {target actual : Dynamic.ResolvedPlace} {size : Nat}
    (snapshot : BareTarget environment before place target)
    (resolved : SourceExecutionSize.SourcePlaceResolves program size context evidence source environment before place actual after) :
    after = before ∧ actual = target := by
  have bare : place.projections = [] := by cases snapshot; assumption
  obtain ⟨same, other⟩ := BareTarget.of_resolves bare resolved.sound
  exact ⟨same.symm, target_functional other snapshot⟩

private theorem target_fault_excluded {program : Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {place : PlaceResolution} {target : Dynamic.ResolvedPlace} {reason : Dynamic.SemanticFault}
    (snapshot : BareTarget environment before place target)
    (fault : Dynamic.SourcePlaceFaults program context evidence source environment before place reason after) : False := by
  cases snapshot with
  | intro bare present cell initial =>
    cases fault with
    | unbound missing => exact missing.excludes_lookup present
    | dangling lookup missing =>
      cases lookup.functional present
      exact missing.excludes_read cell
    | projectionExpression _ _ failed => rw [bare] at failed; cases failed
    | danglingAfterProjections lookup _ evaluated missing =>
      rw [bare] at evaluated
      cases evaluated
      cases lookup.functional present
      exact missing.excludes_read cell
    | projectionRead _ _ evaluated _ _ failed =>
      rw [bare] at evaluated
      cases evaluated
      cases failed
    | uninitialized _ _ evaluated _ _ _ nonempty =>
      rw [bare] at evaluated
      cases evaluated
      exact nonempty rfl

variable {program : Program} {invocation : Staging.Recursive.Scope}
  {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  {target : Dynamic.ResolvedPlace} {size : Nat} {outcome : Dynamic.ControlOutcome} {reason : Dynamic.SemanticFault}

theorem item_value {nextEnvironment : Dynamic.Environment}
    (snapshot : BareTarget environment before assignment.target target)
    (trace : SourceExecutionSize.ForItemExecutes program size context invocation.evidence invocation.source environment
      before (.assignValue assignment operator rhs) finalContext nextEnvironment after) :
    ∃ child value middle updated, child < size ∧ finalContext = context ∧ nextEnvironment = environment ∧
      SourceExecutionSize.ExpressionEvaluates program child context invocation.evidence invocation.source environment
        before rhs value middle ∧
      Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected value replacement)
        middle target updated after := by
  cases trace with
  | assignValue assigned =>
    cases assigned with
    | intro resolved evaluated written =>
      obtain ⟨rfl, rfl⟩ := resolve_same snapshot resolved
      refine ⟨_, _, _, _, ?_, rfl, rfl, evaluated, written⟩
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega

theorem item_fault
    (snapshot : BareTarget environment before assignment.target target)
    (trace : SourceExecutionSize.ForItemFaults program size context invocation.evidence invocation.source environment
      before (.assignValue assignment operator rhs) reason after) :
    (∃ child, child < size ∧
      SourceExecutionSize.ExpressionFaults program child context invocation.evidence invocation.source environment
        before rhs reason after) ∨
    (∃ child right currentCell initial currentSelected, child < size ∧
      reason = .invalidAssignmentOperands operator ∧
      SourceExecutionSize.ExpressionEvaluates program child context invocation.evidence invocation.source environment
        before rhs right after ∧
      Dynamic.Heap.Reads after target.location currentCell ∧ currentCell.type = target.rootType ∧
      Dynamic.RootInitialValue currentCell initial ∧ Dynamic.ProjectionsRead initial target.projections currentSelected ∧
      Dynamic.AssignmentOperandsInvalid operator target.selected right) := by
  cases trace with
  | assignValue failed =>
    cases failed with
    | target failed => exact (target_fault_excluded snapshot failed.sound).elim
    | rhs resolved failed =>
      obtain ⟨rfl, rfl⟩ := resolve_same snapshot resolved
      refine .inl ⟨_, ?_, failed⟩
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega
    | operands resolved evaluated currentRead rootType initialValue pathRead invalid =>
      obtain ⟨rfl, rfl⟩ := resolve_same snapshot resolved
      refine .inr ⟨_, _, _, _, _, ?_, rfl, evaluated, currentRead, rootType, initialValue, pathRead, invalid⟩
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega
    | structuralUpdate resolved _ _ _ _ failed =>
      obtain ⟨rfl, rfl⟩ := resolve_same snapshot resolved
      cases snapshot
      cases failed

theorem child_and_tail {rest : List ForItemForm}
    (snapshot : BareTarget environment before assignment.target target)
    (trace : PlainItems program size invocation context environment before
      (.assignValue assignment operator rhs :: rest) finalContext outcome after) :
    (∃ child reason, child < size ∧ finalContext = context ∧ outcome = .fault reason ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before rhs (.fault reason) after) ∨
    (∃ child right currentCell initial currentSelected, child < size ∧ finalContext = context ∧
      outcome = .fault (.invalidAssignmentOperands operator) ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before rhs (.value right) after ∧
      Dynamic.Heap.Reads after target.location currentCell ∧ currentCell.type = target.rootType ∧
      Dynamic.RootInitialValue currentCell initial ∧ Dynamic.ProjectionsRead initial target.projections currentSelected ∧
      Dynamic.AssignmentOperandsInvalid operator target.selected right) ∨
    (∃ child tailSize value middle updated written, child < size ∧ tailSize < size ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before rhs (.value value) middle ∧
      Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected value replacement)
        middle target updated written ∧
      PlainItems program tailSize invocation context environment written rest finalContext outcome after) := by
  cases trace with
  | done trace =>
    cases trace with
    | cons head tail =>
      obtain ⟨child, value, middle, updated, strict, rfl, rfl, evaluated, written⟩ := item_value snapshot head
      exact .inr (.inr ⟨child, _, value, middle, updated, _,
        Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)),
        SourceExecutionSize.child_lt_stepSize (by simp), .value evaluated, written, .done tail⟩)
  | fault trace =>
    cases trace with
    | head failed =>
      rcases item_fault snapshot failed with
        ⟨child, strict, failed⟩ |
        ⟨child, right, currentCell, initial, currentSelected, strict, reasonEq, evaluated,
          currentRead, rootType, initialValue, pathRead, invalid⟩
      · exact .inl ⟨child, _, Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)), rfl, rfl, .fault failed⟩
      · cases reasonEq
        exact .inr (.inl ⟨child, right, currentCell, initial, currentSelected,
          Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)), rfl, rfl,
          .value evaluated, currentRead, rootType, initialValue, pathRead, invalid⟩)
    | tail head failed =>
      obtain ⟨child, value, middle, updated, strict, rfl, rfl, evaluated, written⟩ := item_value snapshot head
      exact .inr (.inr ⟨child, _, value, middle, updated, _,
        Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)),
        SourceExecutionSize.child_lt_stepSize (by simp), .value evaluated, written, .fault failed⟩)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsAssignmentInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsBitNotInversion
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsBitNotInversion
open Frontend SourceInference
open SelectedCompilationStageForLiftBounds
open Staging.Recursive (BareTarget)

variable {program : Program} {invocation : Staging.Recursive.Scope}
  {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {assignment : AssignmentResolution}
  {size : Nat} {outcome : Dynamic.ControlOutcome} {reason : Dynamic.SemanticFault}

theorem item_value {nextEnvironment : Dynamic.Environment}
    (bare : assignment.target.projections = [])
    (trace : SourceExecutionSize.ForItemExecutes program size context invocation.evidence invocation.source environment
      before (.assignBitNot assignment) finalContext nextEnvironment after) :
    ∃ target updated, finalContext = context ∧ nextEnvironment = environment ∧
      BareTarget environment before assignment.target target ∧
      Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
        before target updated after := by
  cases trace with
  | assignBitNot executed =>
    obtain ⟨target, snapshot, written⟩ := (Staging.Recursive.bitNot_update_iff bare).mp executed.sound
    exact ⟨target, _, rfl, rfl, snapshot, written⟩

theorem item_fault (bare : assignment.target.projections = [])
    (trace : SourceExecutionSize.ForItemFaults program size context invocation.evidence invocation.source environment
      before (.assignBitNot assignment) reason after) :
    after = before ∧ Dynamic.SourcePlaceBitNotFaults program context invocation.evidence invocation.source environment
      before assignment.target reason before := by
  cases trace with
  | assignBitNot failed => exact (Staging.Recursive.bitNot_fault_iff bare).mp failed.sound

theorem write_and_tail {rest : List ForItemForm}
    (bare : assignment.target.projections = [])
    (trace : PlainItems program size invocation context environment before
      (.assignBitNot assignment :: rest) finalContext outcome after) :
    (∃ reason, finalContext = context ∧ outcome = .fault reason ∧ after = before ∧
      Dynamic.SourcePlaceBitNotFaults program context invocation.evidence invocation.source environment
        before assignment.target reason before) ∨
    (∃ tailSize target updated written, tailSize < size ∧
      BareTarget environment before assignment.target target ∧
      Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
        before target updated written ∧
      PlainItems program tailSize invocation context environment written rest finalContext outcome after) := by
  cases trace with
  | done trace =>
    cases trace with
    | cons head tail =>
      obtain ⟨target, updated, rfl, rfl, snapshot, written⟩ := item_value bare head
      exact .inr ⟨_, target, updated, _, SourceExecutionSize.child_lt_stepSize (by simp), snapshot, written, .done tail⟩
  | fault trace =>
    cases trace with
    | head failed =>
      obtain ⟨sameHeap, failed⟩ := item_fault bare failed
      exact .inl ⟨_, rfl, rfl, sameHeap, failed⟩
    | tail head failed =>
      obtain ⟨target, updated, rfl, rfl, snapshot, written⟩ := item_value bare head
      exact .inr ⟨_, target, updated, _, SourceExecutionSize.child_lt_stepSize (by simp), snapshot, written, .fault failed⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsBitNotInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialInversion
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialInversion
open Frontend SourceInference
open SelectedCompilationStageForLiftBounds SelectedCompilationStageForInitialBounds

private theorem restore_twice (outcome : Dynamic.ControlOutcome) (inner outer : Dynamic.Environment) :
    Dynamic.restoreControl outer (Dynamic.restoreControl inner outcome) = Dynamic.restoreControl outer outcome := by
  cases outcome <;> rfl

variable {program : Program} {invocation : Staging.Recursive.Scope}
  {context nextContext : SourceSemantics.Context} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {items post : List ForItemForm} {test : ExpressionId} {body : List StatementId}
  {size : Nat} {outcome : Dynamic.ControlOutcome}

theorem restored
    (trace : PlainInitial program invocation context environment before items test post body size outcome after) :
    Dynamic.restoreControl environment outcome = outcome := by
  cases trace with
  | initializerFault => rfl
  | loop _ _ => exact restore_twice _ _ _

theorem head {item : ForItemForm}
    (trace : PlainInitial program invocation context environment before (item :: items) test post body size outcome after) :
    (∃ child reason, child < size ∧ outcome = .fault reason ∧
      SourceExecutionSize.ForItemFaults program child context invocation.evidence invocation.source environment before item reason after) ∨
    (∃ child tailSize middleContext nextEnvironment middle nextOutcome,
      child < size ∧ tailSize < size ∧ outcome = Dynamic.restoreControl environment nextOutcome ∧
      SourceExecutionSize.ForItemExecutes program child context invocation.evidence invocation.source environment before item
        middleContext nextEnvironment middle ∧
      PlainInitial program invocation middleContext nextEnvironment middle items test post body tailSize nextOutcome after) := by
  cases trace with
  | initializerFault initial =>
    cases initial with
    | head failed =>
      refine .inl ⟨_, _, ?_, rfl, failed⟩
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega
    | tail executed failed =>
      refine .inr ⟨_, _, _, _, _, _, ?_, ?_, rfl, executed, .initializerFault failed⟩
      all_goals simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega
  | loop initial loop =>
    cases initial with
    | cons executed tail =>
      refine .inr ⟨_, _, _, _, _, _, ?_, ?_, (restore_twice _ _ _).symm, executed, .loop tail loop⟩
      all_goals simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega

theorem absent {binder : TypedBinder} (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : PlainInitial program invocation context environment before
      (.letDecl binder none :: items) test post body size outcome after) :
    ∃ tailSize location bound nextOutcome, tailSize < size ∧ outcome = Dynamic.restoreControl environment nextOutcome ∧
      Dynamic.Heap.Allocates before binder.scheme.body none location bound ∧
      PlainInitial program invocation nextContext ((binder.id, location) :: environment)
        bound items test post body tailSize nextOutcome after := by
  rcases head trace with ⟨_, _, _, _, failed⟩ | ⟨_, _, _, _, _, _, _, strict, same, executed, tail⟩
  · cases failed; contradiction
  · cases executed with
    | letUninitialized _ extension allocated =>
      cases Dynamic.BinderExtends.functional extended extension
      exact ⟨_, _, _, _, strict, same, allocated, tail⟩

theorem initialized {binder : TypedBinder} {expression : ExpressionId} (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : PlainInitial program invocation context environment before
      (.letDecl binder (some expression) :: items) test post body size outcome after) :
    (∃ child reason, child < size ∧ outcome = .fault reason ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before expression (.fault reason) after) ∨
    (∃ child tailSize value middle location bound nextOutcome, child < size ∧ tailSize < size ∧
      outcome = Dynamic.restoreControl environment nextOutcome ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before expression (.value value) middle ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location bound ∧
      PlainInitial program invocation nextContext ((binder.id, location) :: environment)
        bound items test post body tailSize nextOutcome after) := by
  rcases head trace with ⟨_, reason, strict, same, failed⟩ |
    ⟨_, _, _, _, _, _, childStrict, tailStrict, same, executed, tail⟩
  · cases failed with
    | polymorphicLet poly => exact (poly mono).elim
    | letInitializer _ failed =>
      exact .inl ⟨_, reason, Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) strict, same, .fault failed⟩
  · cases executed with
    | letInitialized evaluated _ extension allocated =>
      cases Dynamic.BinderExtends.functional extended extension
      exact .inr ⟨_, _, _, _, _, _, _,
        Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) childStrict, tailStrict, same,
        .value evaluated, allocated, tail⟩
    | letInitializedGeneralized _ _ poly => exact (poly mono).elim

theorem discard {expression : ExpressionId}
    (trace : PlainInitial program invocation context environment before
      (.expression expression :: items) test post body size outcome after) :
    (∃ child reason, child < size ∧ outcome = .fault reason ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before expression (.fault reason) after) ∨
    (∃ child tailSize value middle, child < size ∧ tailSize < size ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before expression (.value value) middle ∧
      PlainInitial program invocation context environment middle items test post body tailSize outcome after) := by
  rcases head trace with ⟨_, reason, strict, same, failed⟩ |
    ⟨_, _, _, _, _, _, childStrict, tailStrict, same, executed, tail⟩
  · cases failed with
    | expression failed =>
      exact .inl ⟨_, reason, Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) strict, same, .fault failed⟩
  · cases executed with
    | expression evaluated =>
      rw [restored tail] at same
      subst outcome
      exact .inr ⟨_, _, _, _, Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) childStrict,
        tailStrict, .value evaluated, tail⟩

theorem assign {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {target : Dynamic.ResolvedPlace}
    (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
    (trace : PlainInitial program invocation context environment before
      (.assignValue assignment operator rhs :: items) test post body size outcome after) :
    (∃ child reason, child < size ∧ outcome = .fault reason ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before rhs (.fault reason) after) ∨
    (∃ child right currentCell initial currentSelected, child < size ∧
      outcome = .fault (.invalidAssignmentOperands operator) ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before rhs (.value right) after ∧
      Dynamic.Heap.Reads after target.location currentCell ∧ currentCell.type = target.rootType ∧
      Dynamic.RootInitialValue currentCell initial ∧ Dynamic.ProjectionsRead initial target.projections currentSelected ∧
      Dynamic.AssignmentOperandsInvalid operator target.selected right) ∨
    (∃ child tailSize value middle updated written, child < size ∧ tailSize < size ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before rhs (.value value) middle ∧
      Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected value replacement)
        middle target updated written ∧
      PlainInitial program invocation context environment written items test post body tailSize outcome after) := by
  rcases head trace with ⟨_, reason, strict, same, failed⟩ |
    ⟨_, _, _, _, _, _, childStrict, tailStrict, same, executed, tail⟩
  · rcases SelectedCompilationStageForItemsAssignmentInversion.item_fault snapshot failed with
      ⟨child, childStrict, failed⟩ |
      ⟨child, right, currentCell, initial, currentSelected, childStrict, reasonEq, evaluated,
        currentRead, rootType, initialValue, pathRead, invalid⟩
    · exact .inl ⟨child, reason, Nat.lt_trans childStrict strict, same, .fault failed⟩
    · subst reason
      exact .inr (.inl ⟨child, right, currentCell, initial, currentSelected, Nat.lt_trans childStrict strict,
        same, .value evaluated, currentRead, rootType, initialValue, pathRead, invalid⟩)
  · obtain ⟨child, value, middle, updated, strict, rfl, rfl, evaluated, written⟩ :=
      SelectedCompilationStageForItemsAssignmentInversion.item_value snapshot executed
    rw [restored tail] at same
    subst outcome
    exact .inr (.inr ⟨child, _, value, middle, updated, _, Nat.lt_trans strict childStrict, tailStrict,
      .value evaluated, written, tail⟩)

theorem bitNot {assignment : AssignmentResolution}
    (bare : assignment.target.projections = [])
    (trace : PlainInitial program invocation context environment before
      (.assignBitNot assignment :: items) test post body size outcome after) :
    (∃ reason, outcome = .fault reason ∧ after = before ∧
      Dynamic.SourcePlaceBitNotFaults program context invocation.evidence invocation.source environment
        before assignment.target reason before) ∨
    (∃ tailSize target updated written, tailSize < size ∧
      Staging.Recursive.BareTarget environment before assignment.target target ∧
      Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
        before target updated written ∧
      PlainInitial program invocation context environment written items test post body tailSize outcome after) := by
  rcases head trace with ⟨_, reason, _, same, failed⟩ |
    ⟨_, _, _, _, _, _, _, tailStrict, same, executed, tail⟩
  · obtain ⟨sameHeap, failed⟩ := SelectedCompilationStageForItemsBitNotInversion.item_fault bare failed
    exact .inl ⟨reason, same, sameHeap, failed⟩
  · obtain ⟨target, updated, rfl, rfl, snapshot, written⟩ :=
      SelectedCompilationStageForItemsBitNotInversion.item_value bare executed
    rw [restored tail] at same
    subst outcome
    exact .inr ⟨_, target, updated, _, tailStrict, snapshot, written, tail⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialBitNotLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageForLiftBounds SelectedCompilationStageForInitialBounds
open SelectedCompilationStageLiftBounds (LiftsAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {receiving : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {faults : RecursiveStageMeaning.FaultRep}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions


include bridge functions condition transport in
theorem bitNot {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {rest postItems : List ForItemForm} {test : ExpressionId} {statements : List StatementId}
    {assignment : AssignmentResolution}
    (head : CompatibleBitNotStatements.Head context scope assignment)
    (assignmentTyped : SourceBitNotAssignmentValid invocation.source context assignment)
    (remaining : InitializersLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition rest test postItems statements budget) :
    InitializersLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition (.assignBitNot assignment :: rest) test postItems statements budget := by
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  rcases SelectedCompilationStageForInitialInversion.bitNot head.bare trace with
    ⟨reason, rfl, rfl, failed⟩ |
    ⟨tailSize, target, updated, written, tailStrict, snapshot, write, tail⟩
  · exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.bitNot_fault head.bare failed,
      .completed (.fault reason)⟩
  · obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, framePreserved, metadata,
        _count, nextTyped, ⟨middleState, _related, nextAdmitted⟩, _continuation⟩ :=
      CallableIndexedOwnedAdmittedStagedBareBitNotHeads.preserves_value
        (compiled := compiled) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
        (context := context) (scope := scope) (administrative := administrative)
        bridge functions transport head environments heaps locals agrees actualTyped initial admitted assignmentTyped
        snapshot write
    obtain ⟨_, result, finalHeap, restTrace, restAdapted⟩ := remaining
      (Nat.le_trans (Nat.le_of_lt tailStrict) within)
      ⟨_, _, _, environments.extend maps worlds, middleHeaps,
        locals.mono metadata, DataPlaceChildExpressions.prefix_agrees agrees slots, nextTyped, reference,
        ((framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read),
        (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1,
        middleState, conditioned, nextAdmitted⟩ tail
    exact ⟨_, result, finalHeap,
      CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_bitNot snapshot write restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialLifting
end
