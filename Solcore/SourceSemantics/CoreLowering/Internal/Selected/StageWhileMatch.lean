import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageExpressions
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedWhileHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchSequences
import Solcore.SourceSemantics.CoreLowering.ReachableMatchContinuationMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedMatchSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchReflection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchPreservation
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedLiteralSites
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchHeadBounds

/-!
# Lifting to staged Source: while loops and matches

Inversion, lifting and sequences of `while` loops and matches.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageWhileLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageWhileLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageBodyLiftBounds Staging.Recursive.Lifting
open CallableIndexedOwnedAdmittedStagedConditionalHeads
universe u

inductive PlainWhile (program : Program) (size : Nat) (invocation : Staging.Recursive.Scope)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (test : ExpressionId) (statements : List StatementId) : Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | control {outcome after}
      (trace : SourceExecutionSize.WhileExecutes program size context invocation.evidence invocation.source
        environment before test statements context outcome after) : PlainWhile program size invocation context environment before test statements outcome after
  | fault {reason after}
      (trace : SourceExecutionSize.WhileFaults program size context invocation.evidence invocation.source
        environment before test statements reason after) : PlainWhile program size invocation context environment before test statements (.fault reason) after

def WhileLift (program : Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (test : ExpressionId) (statements : List StatementId) (outcome : Dynamic.ControlOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ staged reached, Staging.Recursive.While program stages invocation context environment before test statements staged reached ∧
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
  {test : ExpressionId} {node : ExpressionNode} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {testCode loopCode : Expr}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

def PhysicalReady (environment : Dynamic.Environment) (canonical actual : Environment)
    (actualContext : Core.Context) (ξ : Renaming) (contextLocation : Location) (native : NativeFrame)
    (heap : Dynamic.Heap) : Prop :=
  ∃ mapping world store,
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world heap store ∧
    Dynamic.EnvironmentAgrees heap context.locals environment ∧ EnvironmentsAgree ξ canonical actual ∧
    RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
    canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
    store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧ contextLocation ∉ mapping ∧
    ∃ initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩,
      condition contextLocation native ∧ Admission bridge context initial

variable {environment : Dynamic.Environment} {canonical actual : Environment}
  {actualContext : Core.Context} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}

local notation "ReadyAt" => PhysicalReady (administrative := administrative) (receiving := receiving)
  (frame := frame) (globals := globals) (context := context) (scope := scope)
  bridge functions condition environment canonical actual actualContext ξ contextLocation native

theorem test_value {budget child : Nat} {before after : Dynamic.Heap} {value : Dynamic.Value}
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (ready : ReadyAt before) (smaller : child < budget)
    (trace : SourceExecutionSize.ExpressionEvaluates program child context invocation.evidence invocation.source
      environment before test value after) :
    (∃ origin call reason reached, Staging.Recursive.Expression program stages invocation context environment before test
      (.fault (.stage origin call reason)) reached) ∨
    (Staging.Recursive.Expression program stages invocation context environment before test (.value value) after ∧
      ReadyAt after ∧ Dynamic.BooleanValue value) := by
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  obtain ⟨staged, reached, lifted, adapted⟩ := children child smaller generated found typed
    environments heaps locals agrees actualTyped initial admitted (.value trace)
  cases adapted with
  | rejected origin call reason reached => exact .inl ⟨origin, call, reason, reached, lifted⟩
  | completed =>
    obtain ⟨size, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
    obtain ⟨_, finalStore, finalMap, finalWorld, _, represented, finalHeaps, maps, worlds, preserved, metadata,
      last, _, post⟩ := preservation size generated found typed environments heaps locals agrees actualTyped initial admitted measured
    have boolean : Dynamic.BooleanValue value := by
      cases represented with
      | value payload =>
        obtain ⟨b, same, _⟩ := CompatibleExpressionPrimitives.bool_fields payload
        rw [same]
        trivial
    refine .inr ⟨lifted, ?_, boolean⟩
    exact ⟨finalMap, finalWorld, finalStore, environments.extend maps worlds, finalHeaps, locals.mono metadata,
      agrees, actualTyped.weaken worlds, reference,
      ((preserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read),
      (preserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1,
      last, conditioned, post.at_value.2⟩

private theorem body_prefix {budget size : Nat} {before after : Dynamic.Heap}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (body : FlowLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) bridge functions condition context scope false statements budget)
    (ready : ReadyAt before) (within : size ≤ budget)
    (trace : RecursiveNamedCallBounds.StatementsOutcome program size context invocation.evidence invocation.source
      environment before statements finalContext outcome after) :
    BodyLift program stages false invocation context environment before statements finalContext outcome after := by
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  exact body within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace

private theorem body_ready {before after : Dynamic.Heap} {finalContext : SourceSemantics.Context}
    {finalEnvironment : Dynamic.Environment}
    (preservation : ∀ budget, FlowPreserves (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope false statements expected type loopCode budget)
    (ready : ReadyAt before)
    (trace : Staging.Recursive.StatementsIn program stages false invocation context environment before statements
      finalContext (.fallthrough finalEnvironment) after) : ReadyAt after := by
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  obtain ⟨size, measured⟩ := Staging.Recursive.Size.StatementsIn.of_trace trace
  obtain ⟨_, finalStore, finalMap, finalWorld, _, _, finalHeaps, maps, worlds, preserved, metadata,
    last, _, post⟩ := preservation size (Nat.le_refl _) environments heaps locals agrees actualTyped
      reference read unmapped initial conditioned admitted measured
  exact ⟨finalMap, finalWorld, finalStore, environments.extend maps worlds, finalHeaps, locals.mono metadata,
    agrees, actualTyped.weaken worlds, reference,
    ((preserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read),
    (preserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1, last, conditioned, post⟩

theorem body_continue_ready {before after : Dynamic.Heap} {finalContext : SourceSemantics.Context}
    {finalEnvironment : Dynamic.Environment}
    (preservation : ∀ budget, FlowPreserves (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope false statements expected type loopCode budget)
    (ready : ReadyAt before)
    (trace : Staging.Recursive.StatementsIn program stages false invocation context environment before statements
      finalContext (.continuing finalEnvironment) after) : ReadyAt after := by
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  obtain ⟨size, measured⟩ := Staging.Recursive.Size.StatementsIn.of_trace trace
  obtain ⟨_, finalStore, finalMap, finalWorld, _, _, finalHeaps, maps, worlds, preserved, metadata,
    last, _, post⟩ := preservation size (Nat.le_refl _) environments heaps locals agrees actualTyped
      reference read unmapped initial conditioned admitted measured
  exact ⟨finalMap, finalWorld, finalStore, environments.extend maps worlds, finalHeaps, locals.mono metadata,
    agrees, actualTyped.weaken worlds, reference,
    ((preserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read),
    (preserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1, last, conditioned, post⟩

private theorem while_ready {budget : Nat}
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
    {size : Nat} {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (within : size ≤ budget) (ready : ReadyAt before)
    (trace : PlainWhile program size invocation context environment before test statements outcome after) :
    WhileLift program stages invocation context environment before test statements outcome after := by
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
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · exact ⟨_, _, .done lifted, .completed (.fallthrough environment)⟩
      | nextFallthrough testTrace bodyTrace next =>
        rcases test_value bridge functions condition children preservation found typed generated ready
          (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within) testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge functions condition body testReady
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFault liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have nextReady := body_ready bridge functions condition bodyPreservation testReady liftedBody
            obtain ⟨staged, reached, liftedNext, adaptedNext⟩ := ih _
              (SourceExecutionSize.child_lt_stepSize (by simp))
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
              nextReady (.control next)
            exact ⟨staged, reached, .next liftedTest liftedBody liftedNext, adaptedNext⟩
      | nextContinue testTrace bodyTrace next =>
        rcases test_value bridge functions condition children preservation found typed generated ready
          (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within) testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge functions condition body testReady
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFault liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have nextReady := body_continue_ready bridge functions condition bodyPreservation testReady liftedBody
            obtain ⟨staged, reached, liftedNext, adaptedNext⟩ := ih _
              (SourceExecutionSize.child_lt_stepSize (by simp))
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
              nextReady (.control next)
            exact ⟨staged, reached, .continueNext liftedTest liftedBody liftedNext, adaptedNext⟩

      | breaks testTrace bodyTrace =>
        rcases test_value bridge functions condition children preservation found typed generated ready
          (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within) testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge functions condition body testReady
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFault liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            exact ⟨_, _, .breakFromBody liftedTest liftedBody, .completed (.fallthrough environment)⟩
      | returns testTrace bodyTrace =>
        rcases test_value bridge functions condition children preservation found typed generated ready
          (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within) testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge functions condition body testReady
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
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
        obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
          initial, conditioned, admitted⟩ := ready
        obtain ⟨staged, reached, lifted, adapted⟩ := children _
          (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within) generated found typed
          environments heaps locals agrees actualTyped initial admitted (.fault failed)
        cases adapted with
        | completed => exact ⟨_, _, .conditionFault lifted, .completed (.fault _)⟩
        | rejected origin call reason reached =>
          exact ⟨_, reached, .conditionFault lifted, .rejected origin call reason context reached⟩
      | conditionType testTrace notBoolean _ =>
        rcases test_value bridge functions condition children preservation found typed generated ready
          (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within) testTrace with
          stopped | ⟨_, _, valueTyped⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · exact False.elim (notBoolean valueTyped)
      | body testTrace bodyTrace =>
        rcases test_value bridge functions condition children preservation found typed generated ready
          (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within) testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge functions condition body testReady
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
              (.fault bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFault liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            exact ⟨_, _, .bodyFault liftedTest liftedBody, .completed (.fault _)⟩
      | nextFallthrough testTrace bodyTrace next =>
        rcases test_value bridge functions condition children preservation found typed generated ready
          (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within) testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge functions condition body testReady
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFault liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have nextReady := body_ready bridge functions condition bodyPreservation testReady liftedBody
            obtain ⟨staged, reached, liftedNext, adaptedNext⟩ := ih _
              (SourceExecutionSize.child_lt_stepSize (by simp))
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
              nextReady (.fault next)
            exact ⟨staged, reached, .next liftedTest liftedBody liftedNext, adaptedNext⟩
      | nextContinue testTrace bodyTrace next =>
        rcases test_value bridge functions condition children preservation found typed generated ready
          (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within) testTrace with
          stopped | ⟨liftedTest, testReady, _⟩
        · obtain ⟨origin, call, reason, reached, stopped⟩ := stopped
          exact ⟨_, reached, .conditionFault stopped, .rejected origin call reason context reached⟩
        · obtain ⟨bodyContext, stagedBody, bodyHeap, liftedBody, adaptedBody⟩ :=
            body_prefix bridge functions condition body testReady
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
              (.control bodyTrace)
          cases adaptedBody with
          | rejected origin call reason finalContext reached =>
            exact ⟨_, _, .bodyFault liftedTest liftedBody, .rejected origin call reason context _⟩
          | completed matched =>
            cases matched
            have nextReady := body_continue_ready bridge functions condition bodyPreservation testReady liftedBody
            obtain ⟨staged, reached, liftedNext, adaptedNext⟩ := ih _
              (SourceExecutionSize.child_lt_stepSize (by simp))
              (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
              nextReady (.fault next)
            exact ⟨staged, reached, .continueNext liftedTest liftedBody liftedNext, adaptedNext⟩

theorem while_loop {budget : Nat}
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
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native) (admitted : Admission bridge context initial)
    {outcome : Dynamic.ControlOutcome}
    (trace : PlainWhile program size invocation context environment before test statements outcome after) :
    WhileLift program stages invocation context environment before test statements outcome after := by
  exact while_ready bridge functions condition children preservation found typed generated body bodyPreservation within
    ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
      initial, conditioned, admitted⟩ trace

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageWhileLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageWhileSourceInversion
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageWhileSourceInversion
open Frontend SourceInference
open SelectedCompilationStageWhileLifting

private theorem loop_fields {program : Program} {source : TypedSource}
    {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {test : ExpressionId} {body : List StatementId} {size : Nat} {outcome : Dynamic.ControlOutcome}
    (trace : SourceExecutionSize.WhileExecutes program size context evidence source environment before
      test body finalContext outcome after) :
    finalContext = context ∧ Dynamic.restoreControl environment outcome = outcome := by
  induction size using Nat.strongRecOn generalizing before after outcome finalContext with
  | ind size ih =>
    cases trace with
    | done => exact ⟨rfl, rfl⟩
    | breaks => exact ⟨rfl, rfl⟩
    | returns => exact ⟨rfl, rfl⟩
    | nextFallthrough _ _ next | nextContinue _ _ next =>
      exact ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) next

theorem control {program : Program} {invocation : Staging.Recursive.Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode}
    {test : ExpressionId} {body : List StatementId} {size : Nat} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .whileLoop test body)
    (trace : SourceExecutionSize.StatementExecutes program size context invocation.evidence invocation.source
      environment before id finalContext outcome after) :
    ∃ child, child < size ∧ finalContext = context ∧
      PlainWhile program child invocation context environment before test body outcome after := by
  have sameNode : ∀ {other}, ContainsStatement invocation.source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace <;> have same := sameNode (by assumption) <;> subst_vars <;> simp_all
  rename_i loopContext result child iterate
  obtain ⟨rfl, restored⟩ := loop_fields iterate
  rw [restored]
  refine ⟨_, ?_, .control iterate⟩
  exact SourceExecutionSize.child_lt_stepSize (by simp)

theorem fault {program : Program} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode}
    {test : ExpressionId} {body : List StatementId} {size : Nat} {reason : Dynamic.SemanticFault}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .whileLoop test body)
    (trace : SourceExecutionSize.StatementFaults program size context invocation.evidence invocation.source
      environment before id reason after) :
    ∃ child, child < size ∧ PlainWhile program child invocation context environment before test body (.fault reason) after := by
  have sameNode : ∀ {other}, ContainsStatement invocation.source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  all_goals have same := sameNode (by assumption)
  all_goals subst_vars; simp_all
  refine ⟨_, ?_, .fault (by assumption)⟩
  exact SourceExecutionSize.child_lt_stepSize (by simp)

theorem fallthrough_environment {program : Program} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment innerEnvironment : Dynamic.Environment}
    {before after : Dynamic.Heap} {test : ExpressionId} {body : List StatementId} {size : Nat}
    (trace : PlainWhile program size invocation context environment before test body (.fallthrough innerEnvironment) after) :
    innerEnvironment = environment := by
  cases trace with
  | control evaluated =>
    have same := (loop_fields evaluated).2
    exact (Dynamic.ControlOutcome.fallthrough.inj same).symm

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageWhileSourceInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageWhileSequenceLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageWhileSequenceLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageWhileLifting
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
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {certificate : GenericExpressionMeaning.Certificate}
  {test : ExpressionId} {node : ExpressionNode} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {testCode loopCode : Expr}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions


variable {mode : Bool} {id : StatementId} {statement : StatementNode}
  {rest : List StatementId} {selfReason : Word}

include transport in
/-- Lift the actual while head and precisely the suffix reached after normal
completion. Earlier returns and genuine failures retain their original scope. -/
theorem lifts {budget : Nat}
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node) (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type testCode loopCode selfReason) (LocalLoop.resultType type)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (body : FlowLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) bridge functions condition context scope false statements budget)
    (bodyPreservation : ∀ n, FlowPreserves (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope false statements expected type loopCode n)
    (unique : NodeOccurrencesUnique invocation.source)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .whileLoop test statements)
    (remaining : FlowLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) bridge functions condition context scope mode rest budget) :
    FlowLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) bridge functions condition context scope mode (id :: rest) budget := by
  intro size within mapping world actualContext environment canonical actual before store ξ contextLocation native
    environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
    finalContext outcome after trace
  have lift {n : Nat} {plain : Dynamic.ControlOutcome} {reached : Dynamic.Heap}
      (small : n ≤ budget)
      (loop : PlainWhile program n invocation context environment before test statements plain reached) :
      WhileLift program stages invocation context environment before test statements plain reached :=
    while_loop bridge functions condition children preservation found typed generated body bodyPreservation small
      environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted loop
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique statementFound
    (by intro expression equal; rw [form] at equal; cases equal) trace with
    ⟨headSize, reason, headSmaller, rfl, rfl, failed⟩ |
    ⟨headSize, headSmaller, terminal, executed⟩ |
    ⟨headSize, tailSize, middleContext, nextEnvironment, middle, headSmaller, tailSmaller, executed, tail⟩
  · obtain ⟨loopSize, loopSmaller, loop⟩ := SelectedCompilationStageWhileSourceInversion.fault unique statementFound form failed
    obtain ⟨staged, reached, lifted, adapted⟩ := lift
      (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans loopSmaller headSmaller)) within) loop
    cases adapted with
    | completed matched =>
      cases matched
      exact ⟨_, _, _, .whileFault (lookupStatement?_sound statementFound) form lifted, .completed (.fault reason)⟩
    | rejected origin call reason finalContext reached =>
      exact ⟨_, _, _, .whileFault (lookupStatement?_sound statementFound) form lifted,
        .rejected origin call reason _ _⟩
  · obtain ⟨loopSize, loopSmaller, rfl, loop⟩ := SelectedCompilationStageWhileSourceInversion.control unique statementFound form executed
    obtain ⟨staged, reached, lifted, adapted⟩ := lift
      (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans loopSmaller headSmaller)) within) loop
    cases adapted with
    | rejected origin call reason finalContext reached =>
      exact ⟨_, _, _, .whileFault (lookupStatement?_sound statementFound) form lifted,
        .rejected origin call reason _ _⟩
    | completed matched =>
      cases matched with
      | breaking innerEnvironment => exact ((SelectedCompilationStageLoopOutcomes.while_closed_of_trace lifted).1 innerEnvironment rfl).elim
      | continuing innerEnvironment => exact ((SelectedCompilationStageLoopOutcomes.while_closed_of_trace lifted).2 innerEnvironment rfl).elim
      | returned value =>
        exact ⟨_, _, _, .whileReturned (lookupStatement?_sound statementFound) form lifted, .completed (.returned value)⟩
      | fault reason =>
        exact ⟨_, _, _, .whileFault (lookupStatement?_sound statementFound) form lifted, .completed (.fault reason)⟩
      | fallthrough innerEnvironment =>
        cases SelectedCompilationStageWhileSourceInversion.fallthrough_environment loop
        rcases terminal with terminal | rfl
        · cases terminal
        · exact ⟨_, _, _, .whileFallthrough (lookupStatement?_sound statementFound) form lifted .nil,
            .completed (.fallthrough environment)⟩
  · obtain ⟨loopSize, loopSmaller, rfl, loop⟩ := SelectedCompilationStageWhileSourceInversion.control unique statementFound form executed
    cases SelectedCompilationStageWhileSourceInversion.fallthrough_environment loop
    obtain ⟨staged, reached, lifted, adapted⟩ := lift
      (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans loopSmaller headSmaller)) within) loop
    cases adapted with
    | rejected origin call reason finalContext reached =>
      exact ⟨_, _, _, .whileFault (lookupStatement?_sound statementFound) form lifted,
        .rejected origin call reason _ _⟩
    | completed matched =>
      cases matched
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.While.of_trace lifted
      obtain ⟨_, finalStore, finalMap, finalWorld, _, _, finalHeaps, maps, worlds, preserved, metadata,
        last, _, post⟩ := CallableIndexedOwnedAdmittedStagedWhileHeads.preserves bridge functions condition transport
          (fun n _ => preservation n) found nodeType typed generated nativeTyped (bodyPreservation stagedSize)
          (Nat.le_refl _) environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted measured
      obtain ⟨tailContext, tailOutcome, tailHeap, liftedTail, adaptedTail⟩ := remaining
        (Nat.le_trans (Nat.le_of_lt tailSmaller) within)
        (environments.extend maps worlds) finalHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
        reference ((preserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
        (preserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 last conditioned post tail
      exact ⟨tailContext, tailOutcome, tailHeap,
        .whileFallthrough (lookupStatement?_sound statementFound) form lifted liftedTail, adaptedTail⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageWhileSequenceLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMatchSourceInversion
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMatchSourceInversion
open Frontend SourceInference
open Solcore.SourceSemantics.Dynamic
open SelectedCompilationStageScopedLiftBounds

/-- A view of the actual ordinary match trace, including allocated hidden and
pattern cells. Every child keeps its original execution grade. -/
inductive PlainMatch (program : Program) : Nat →
      Staging.Recursive.Scope → Context → Dynamic.Environment → Dynamic.Heap → MatchResolution → Dynamic.ControlOutcome → Dynamic.Heap → Prop where
    | scrutineeFault {size : Nat} {scope context environment before after resolution failure}
        (scrutinee : SourceExecutionSize.ExpressionFaults program size context scope.evidence scope.source environment before resolution.scrutinee failure after) :
        PlainMatch program (SourceExecutionSize.stepSize [size]) scope context environment before resolution (.fault failure) after
    | patternFault {size : Nat} {scope context environment before middle hidden resolution node value location}
        (contains : ContainsExpression scope.source resolution.scrutinee node)
        (scrutinee : SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before resolution.scrutinee value middle)
        (allocated : Heap.Allocates middle node.type (some value) location hidden)
        (invalid : MatchCasesPatternFault context value resolution.cases) :
        PlainMatch program (SourceExecutionSize.stepSize [size]) scope context environment before resolution (.fault .invalidPattern) hidden
    | arm {size bodySize : Nat} {scope context armContext finalContext environment armEnvironment before middle hidden bound after
          resolution node value location statements bindings outcome}
        (contains : ContainsExpression scope.source resolution.scrutinee node)
        (scrutinee : SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before resolution.scrutinee value middle)
        (hiddenAllocated : Heap.Allocates middle node.type (some value) location hidden)
        (selected : MatchCasesSelect context value resolution.cases resolution.defaultBody (.arm statements bindings))
        (extended : BindersExtend scope.source.owner context (bindings.map Prod.fst) armContext)
        (allocated : BindersAllocate environment hidden (bindings.map Prod.fst) (bindings.map Prod.snd) armEnvironment bound)
        (body : PlainStatements program false bodySize scope armContext armEnvironment bound statements finalContext outcome after) :
        PlainMatch program (SourceExecutionSize.stepSize [size, bodySize]) scope context environment before resolution (Dynamic.restoreControl environment outcome) after
    | default {size bodySize : Nat} {scope context finalContext environment before middle hidden after resolution node value location statements outcome}
        (contains : ContainsExpression scope.source resolution.scrutinee node)
        (scrutinee : SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before resolution.scrutinee value middle)
        (hiddenAllocated : Heap.Allocates middle node.type (some value) location hidden)
        (selected : MatchCasesSelect context value resolution.cases resolution.defaultBody (.default statements))
        (body : PlainStatements program false bodySize scope context environment hidden statements finalContext outcome after) :
        PlainMatch program (SourceExecutionSize.stepSize [size, bodySize]) scope context environment before resolution (Dynamic.restoreControl environment outcome) after
    | noBranch {size : Nat} {scope context environment before middle hidden resolution node value location}
        (contains : ContainsExpression scope.source resolution.scrutinee node)
        (scrutinee : SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before resolution.scrutinee value middle)
        (hiddenAllocated : Heap.Allocates middle node.type (some value) location hidden)
        (selected : MatchCasesSelect context value resolution.cases resolution.defaultBody .noBranch) :
        PlainMatch program (SourceExecutionSize.stepSize [size]) scope context environment before resolution (.fallthrough environment) hidden



/-- Ordinary completion restores the outer context after the selected arm. -/
theorem control
    {program : Program} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode}
    {resolution : MatchResolution} {size : Nat}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution)
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (trace : SourceExecutionSize.StatementExecutes program size context invocation.evidence invocation.source
      environment before id finalContext outcome after) :
    finalContext = context ∧ PlainMatch program size invocation context environment before resolution outcome after := by
  have sameNode : ∀ {other}, ContainsStatement invocation.source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case matchArm same contains evaluated hidden selected bindersEq valuesEq extended allocated actual body =>
    cases sameNode actual
    rw [form] at same
    cases same
    subst_vars
    exact ⟨rfl, .arm (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (.control (by assumption))⟩
  case matchDefault same contains evaluated hidden selected actual body =>
    cases sameNode actual
    rw [form] at same
    cases same
    exact ⟨rfl, .default (by assumption) (by assumption) (by assumption) (by assumption) (.control (by assumption))⟩
  case matchNoBranch same contains evaluated hidden actual selected =>
    cases sameNode actual
    rw [form] at same
    cases same
    exact ⟨rfl, .noBranch (by assumption) (by assumption) (by assumption) (by assumption)⟩
  all_goals
    have same := sameNode (by assumption)
    subst_vars
    simp_all

/-- Ordinary failure retains scrutinee, pattern and selected-body failures. -/
theorem fault
    {program : Program} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode}
    {resolution : MatchResolution} {size : Nat}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution)
    {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.StatementFaults program size context invocation.evidence invocation.source
      environment before id reason after) :
    PlainMatch program size invocation context environment before resolution (.fault reason) after := by
  have sameNode : ∀ {other}, ContainsStatement invocation.source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  case matchScrutinee same actual failed =>
    cases sameNode actual
    rw [form] at same
    cases same
    exact .scrutineeFault failed
  case matchPattern same contains evaluated hidden actual failed =>
    cases sameNode actual
    rw [form] at same
    cases same
    exact .patternFault (by assumption) (by assumption) (by assumption) (by assumption)
  case matchArmBody same contains evaluated hidden selected bindersEq valuesEq extended allocated actual body =>
    cases sameNode actual
    rw [form] at same
    cases same
    subst_vars
    exact .arm (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (.fault (by assumption))
  case matchDefaultBody same contains evaluated hidden selected actual body =>
    cases sameNode actual
    rw [form] at same
    cases same
    exact .default (by assumption) (by assumption) (by assumption) (by assumption) (.fault (by assumption))
  all_goals
    have same := sameNode (by assumption)
    subst_vars
    simp_all

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMatchSourceInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMatchLifting
/-! Ordinary match traces lift through the actual allocation prefix. The
selected branch receives its captured cells at the genuine reached state. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMatchLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchMeaning
open DataMatchBranchPrefix GenericLexicalContext CallableIndexedHistory
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedMatchHeads
open SelectedCompilationStageScopedLiftBounds SelectedCompilationStageBodyLiftBounds
open SelectedCompilationStageLiftBounds (LiftsAt)
open SelectedCompilationStageMatchSourceInversion (PlainMatch)
universe u
private theorem default_selected {context : SourceSemantics.Context} {value : Dynamic.Value}
    {cases : List TypedMatchCase} {fallback : Option (List StatementId)} {statements : List StatementId}
    (selected : Dynamic.MatchCasesSelect context value cases fallback (.default statements)) :
    fallback = some statements := by
  cases selected with
  | default => rfl
  | tail _ next => exact default_selected next
termination_by cases.length
decreasing_by simp_all

private theorem allocations_same {before left right : Dynamic.Heap} {type : TypeSystem.Ty} {value : Option Dynamic.Value}
    {a b : Dynamic.Location} (first : Dynamic.Heap.Allocates before type value a left)
    (second : Dynamic.Heap.Allocates before type value b right) : left = right := by
  cases first; cases second; rfl

private theorem binders_same {environment a b : Dynamic.Environment} {before left right : Dynamic.Heap}
    {binders : List TypedBinder} {values : List Dynamic.Value}
    (first : Dynamic.BindersAllocate environment before binders values a left)
    (second : Dynamic.BindersAllocate environment before binders values b right) : a = b ∧ left = right := by
  induction first generalizing b right with
  | nil => cases second; exact ⟨rfl, rfl⟩
  | cons allocation rest ih =>
    cases second with
    | cons allocation' rest' =>
      cases allocation
      cases allocation'
      exact ih rest'

private theorem extensions_same {owner : Resolved.DeclarationId} {context a b : SourceSemantics.Context}
    {binders : List TypedBinder} (first : BindersExtend owner context binders a)
    (second : BindersExtend owner context binders b) : a = b := by
  induction first generalizing b with
  | nil => cases second; rfl
  | cons head tail ih =>
    cases second with
    | cons head' tail' =>
      cases head
      cases head'
      exact ih tail'


variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} {administrative : Core.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {solved : List SolvedRequirement} {sourceCells : Option SourceCoreSourceCells.Allocator}
  {ambientDefinitions : Option Core.DataEnvironment}
local notation "compilation" => (SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions)
local notation "ambient" => CallableIndexedAmbient.ambientDefinitions compiled.indexed
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions


section Ports
variable {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  (condition : Location → NativeFrame → Prop)
  (parent : SourceSemantics.Context) (control : ControlContext) (resolution : MatchResolution)
  (bodyCertificate : BodyCertificate) (type : Ty) (budget : Nat)
def ArmLiftsBelow (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.arm statements bindings) →
    SelectedBody bodyCertificate scope environment heap type (.arm statements bindings)
      finalScope finalEnvironment finalHeap body →
    ∀ {armContext staticFinal facts},
    BindersExtend invocation.source.owner parent (bindings.map Prod.fst) armContext →
    StatementsHaveType invocation.source control armContext statements staticFinal facts →
    FlowLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation)
      bridge functions condition armContext finalScope false statements budget

def DefaultLiftsBelow (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.default statements) →
    SelectedBody bodyCertificate scope environment heap type (.default statements)
      finalScope finalEnvironment finalHeap body →
    ∀ {staticFinal facts}, StatementsHaveType invocation.source control parent statements staticFinal facts →
    FlowLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation)
      bridge functions condition parent finalScope false statements budget

end Ports

/-- Restoring lexical scope retains the exact ordinary completion or the
same authentic earlier stage failure. -/
theorem restore_adapted {plainFinal finalContext outer : SourceSemantics.Context}
    {plain : Dynamic.ControlOutcome} {staged : Staging.Recursive.BodyOutcome}
    {after reached : Dynamic.Heap} (environment : Dynamic.Environment)
    (adapted : BodyAdapted plainFinal plain after finalContext staged reached) :
    BodyAdapted outer (Dynamic.restoreControl environment plain) after outer (staged.restore environment) reached := by
  cases adapted with
  | completed matched => cases matched with
    | returned value => exact .completed (.returned value)
    | breaking _ => exact .completed (.breaking environment)
    | continuing _ => exact .completed (.continuing environment)
    | fallthrough inner => exact .completed (.fallthrough environment)
    | fault reason => exact .completed (.fault reason)
  | rejected origin call reason finalContext reached => exact .rejected origin call reason outer reached

def MatchLift (program : Program) (stages : Staging.Recursive.Registry)
    (invocation : Staging.Recursive.Scope) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (resolution : MatchResolution)
    (plain : Dynamic.ControlOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ staged reached, Staging.Recursive.Match program stages invocation context environment before resolution staged reached ∧
    BodyAdapted context plain after context staged reached

include bridge functions in
theorem lifts
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : (compilation).sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (definitions : layouts.definitions = (ambient).definitions) (registered : frame.Registered (ambient).definitions)
    (extended : SourceCoreRawMetadata.Extends (compilation).values.registry receiving)
    {context : SourceSemantics.Context} {control : ControlContext} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {type : Ty} {reason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation invocation.source scope id resolution type reason
      expressionCertificate bodyCertificate code)
    (ordinary : CompatibleMatchSelectionPrefix.Ordinary certificate)
    (unique : NodeOccurrencesUnique invocation.source)
    (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = (compilation).signatures)
    (numericRequirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : CompatibleMatchDecision.Certificate.LiteralSites literals certificate)
    (catalogValid : SignatureCatalogWellFormed (compilation).checked.signatures)
    {node : ExpressionNode} (found : invocation.source.lookupExpression? resolution.scrutinee = some node)
    (typed : ExpressionHasType invocation.source context resolution.scrutinee node.type)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ other, expressionCertificate scope resolution.scrutinee other → other = lowered)
    {caseFacts : List BodyFacts}
    (casesTyped : MatchCasesHaveType invocation.source control context node.type resolution.cases caseFacts)
    (defaultTyped : ∀ {statements}, resolution.defaultBody = some statements →
      ∃ finalContext facts, StatementsHaveType invocation.source control context statements finalContext facts)
    (budget : Nat)
    (condition : Location → NativeFrame → Prop)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer callerProtocol layouts frame model)
    (stateBindings : ProtectedStateTransition.Bindings callerProtocol)
    (acquire : ∀ location native, condition location native →
      ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
    (children : ∀ child, child < budget → LiftsAt bridge context model stages invocation expressionCertificate child)
    (preservation : ∀ child, PreservesAt bridge context model stages invocation expressionCertificate faults child)
    (armMeaning : ArmLiftsBelow (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context control resolution bodyCertificate type budget scope)
    (defaultMeaning : DefaultLiftsBelow (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context control resolution bodyCertificate type budget scope)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (ambient).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (ambient).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (admitted : Admission bridge context initial)
    (trace : PlainMatch program size invocation context environment before resolution outcome after) :
    MatchLift program stages invocation context environment before resolution outcome after := by
  have expression : expressionCertificate scope resolution.scrutinee lowered := by
    cases certificate with
    | matchWith _ _ _ _ _ _ _ _ _ certified => exact (uniqueExpression _ certified) ▸ certified
  cases trace with
  | scrutineeFault failed =>
    obtain ⟨staged, reached, lifted, adapted⟩ := children _
      (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
      expression found typed environments heaps locals agrees actualTyped initial admitted (.fault failed)
    cases adapted with
    | completed => exact ⟨_, _, .scrutineeFault lifted, .completed (.fault _)⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .scrutineeFault lifted, .rejected origin call reason context reached⟩
  | patternFault contains evaluated allocated failed =>
    obtain ⟨staged, reached, lifted, adapted⟩ := children _
      (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
      expression found typed environments heaps locals agrees actualTyped initial admitted (.value evaluated)
    cases adapted with
    | completed => exact ⟨_, _, .patternFault contains lifted allocated failed, .completed (.fault _)⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .scrutineeFault lifted, .rejected origin call reason context reached⟩
  | @arm exprSize bodySize _ _ armContext innerFinal _ armEnvironment _ middle hidden bound _ _ sourceNode sourceValue
      location statements bindings innerOutcome contains sourceEval sourceHidden selected sourceExtended sourceAllocated sourceBody =>
    have exprSmaller : exprSize < budget := Nat.lt_of_lt_of_le
      (SourceExecutionSize.child_lt_stepSize (by simp)) within
    have bodyWithin : bodySize ≤ budget := Nat.le_trans
      (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within
    have nodeEq : sourceNode = node := Option.some.inj
      ((lookupExpression?_complete unique contains).symm.trans found)
    subst sourceNode
    obtain ⟨staged, reached, lifted, adapted⟩ := children _ exprSmaller
      expression found typed environments heaps locals agrees actualTyped initial admitted (.value sourceEval)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, .scrutineeFault lifted, .rejected origin call reason context reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨value, middleStore, middleMap, middleWorld, coreEval, represented, middleRelated,
        firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
        preservation stagedSize expression found typed environments heaps locals agrees actualTyped initial admitted measured
      cases represented with
      | value represented =>
        obtain ⟨valueFacts, middleReady⟩ := firstPost.at_value
        obtain ⟨stillUnmapped, stillRead⟩ := firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1
        obtain ⟨hiddenHeap, hiddenLocation, finalScope, selectedEnvironment, selectedHeap, selectedCanonical,
          selectedActual, selectedStore, selectedMap, selectedWorld, selectedEmbedding, selectedContext, body,
          hiddenAllocated, selectedAgain, selectedBody, selectedEnv, selectedRelated, secondMaps, secondWorlds,
          secondFrame, selectedLayout, selectedTyped, selectedReference, selectedRead, selectedUnmapped, spine, agreement, selectedState, selectionRelated, ⟨returnTo⟩⟩ :=
          CompatibleMatchTypedSelectionPrefix.Stateful.Certificate.selected_prefix_sized_with_literals certificate ordinary onError allocator literals signatures numericRequirements sites
            catalogValid callerProtocol producer stateBindings definitions registered extended found uniqueExpression represented (environments.extend firstMaps firstWorlds)
            middleRelated agrees (actualTyped.weaken firstWorlds) reference (stillRead.trans read) stillUnmapped coreEval middleState (acquire contextLocation native conditioned) selected
        have hiddenEq := allocations_same hiddenAllocated sourceHidden
        subst hiddenHeap
        cases selectedBody with
        | arm binders allocated bodyCertified =>
          obtain ⟨sameEnvironment, sameHeap⟩ := binders_same allocated sourceAllocated
          subst selectedEnvironment
          subst selectedHeap
          obtain ⟨staticContext, staticFinal, facts, extended, typed, _⟩ :=
            DataMatchSourceScopes.MatchCasesSelect.arm_scope casesTyped selected
          have sameContext := extensions_same extended sourceExtended
          subst staticContext
          have selectedReady := (CallableIndexedOwnedMatchPrefixAdmission.after_arm_prefix bridge middleState selectedState middleReady valueFacts sourceHidden
            casesTyped selected sourceExtended sourceAllocated secondFrame).1
          obtain ⟨finalContext, result, finalHeap, bodyTrace, bodyAdapted⟩ :=
            armMeaning rfl selected (.arm binders allocated bodyCertified) sourceExtended typed bodyWithin selectedEnv selectedRelated
              (binders_agree sourceExtended (arm_monomorphic casesTyped selected)
                (locals.mono (firstMetadata.trans (.of_allocation sourceHidden))) sourceAllocated)
              selectedLayout selectedTyped selectedReference selectedRead selectedUnmapped selectedState conditioned selectedReady sourceBody
          exact ⟨_, finalHeap, .arm contains lifted sourceHidden selected sourceExtended sourceAllocated bodyTrace,
            restore_adapted environment bodyAdapted⟩
  | @default exprSize bodySize _ _ innerFinal _ _ middle hidden _ _ sourceNode sourceValue location statements innerOutcome
      contains sourceEval sourceHidden selected sourceBody =>
    have exprSmaller : exprSize < budget := Nat.lt_of_lt_of_le
      (SourceExecutionSize.child_lt_stepSize (by simp)) within
    have bodyWithin : bodySize ≤ budget := Nat.le_trans
      (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within
    have nodeEq : sourceNode = node := Option.some.inj
      ((lookupExpression?_complete unique contains).symm.trans found)
    subst sourceNode
    obtain ⟨staged, reached, lifted, adapted⟩ := children _ exprSmaller
      expression found typed environments heaps locals agrees actualTyped initial admitted (.value sourceEval)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, .scrutineeFault lifted, .rejected origin call reason context reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨value, middleStore, middleMap, middleWorld, coreEval, represented, middleRelated,
        firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
        preservation stagedSize expression found typed environments heaps locals agrees actualTyped initial admitted measured
      cases represented with
      | value represented =>
        obtain ⟨valueFacts, middleReady⟩ := firstPost.at_value
        obtain ⟨stillUnmapped, stillRead⟩ := firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1
        obtain ⟨hiddenHeap, hiddenLocation, finalScope, selectedEnvironment, selectedHeap, selectedCanonical,
          selectedActual, selectedStore, selectedMap, selectedWorld, selectedEmbedding, selectedContext, body,
          hiddenAllocated, selectedAgain, selectedBody, selectedEnv, selectedRelated, secondMaps, secondWorlds,
          secondFrame, selectedLayout, selectedTyped, selectedReference, selectedRead, selectedUnmapped, spine, agreement, selectedState, selectionRelated, ⟨returnTo⟩⟩ :=
          CompatibleMatchTypedSelectionPrefix.Stateful.Certificate.selected_prefix_sized_with_literals certificate ordinary onError allocator literals signatures numericRequirements sites
            catalogValid callerProtocol producer stateBindings definitions registered extended found uniqueExpression represented (environments.extend firstMaps firstWorlds)
            middleRelated agrees (actualTyped.weaken firstWorlds) reference (stillRead.trans read) stillUnmapped coreEval middleState (acquire contextLocation native conditioned) selected
        have hiddenEq := allocations_same hiddenAllocated sourceHidden
        subst hiddenHeap
        cases selectedBody with
        | default bodyCertified =>
          have selectedReady := CallableIndexedOwnedMatchAdmission.after_hidden bridge middleState selectedState middleReady valueFacts sourceHidden secondFrame
          obtain ⟨staticFinal, facts, typed⟩ := defaultTyped (default_selected selected)
          obtain ⟨finalContext, result, finalHeap, bodyTrace, bodyAdapted⟩ :=
            defaultMeaning (environment := environment) (heap := hidden) rfl selected (.default bodyCertified) typed bodyWithin selectedEnv selectedRelated
              (locals.mono (firstMetadata.trans (.of_allocation sourceHidden))) selectedLayout selectedTyped selectedReference selectedRead selectedUnmapped selectedState conditioned selectedReady sourceBody
          exact ⟨_, finalHeap, .default contains lifted sourceHidden selected bodyTrace,
            restore_adapted environment bodyAdapted⟩
  | noBranch contains evaluated allocated selected =>
    obtain ⟨staged, reached, lifted, adapted⟩ := children _
      (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
      expression found typed environments heaps locals agrees actualTyped initial admitted (.value evaluated)
    cases adapted with
    | completed => exact ⟨_, _, .noBranch contains lifted allocated selected, .completed (.fallthrough _)⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .scrutineeFault lifted, .rejected origin call reason context reached⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMatchLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMatchSequences
/-! Match heads restore the selected lexical scope before the actual suffix.
Returning and failing bypass that suffix; a genuine default-stopping receipt
justifies the compiler's unreachable continuation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMatchSequences
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

open CallableIndexedOwnedAdmittedStagedConditionalHeads
open CallableIndexedOwnedAdmittedStagedMatchSequences (MatchPreserves)
open SelectedCompilationStageScopedLiftBounds SelectedCompilationStageBodyLiftBounds
open SelectedCompilationStageMatchSourceInversion (PlainMatch)
open SelectedCompilationStageMatchLifting (MatchLift)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

def MatchLifts (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (resolution : MatchResolution) (budget : Nat) : Prop :=
  ∀ {size : Nat}, size ≤ budget →
  ∀ {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_conditioned : condition contextLocation native)
    (_admitted : Admission bridge context initial),
    ∀ {outcome : Dynamic.ControlOutcome} {after : Dynamic.Heap},
      PlainMatch program size invocation context environment before
        resolution outcome after →
    MatchLift program stages invocation context environment before resolution outcome after
private theorem fallthrough_environment {program registry size invocation context before after resolution outer inner}
    (trace : Staging.Recursive.Size.Match program registry size invocation context outer before
      resolution (.fallthrough inner) after) : inner = outer := by
  generalize outcomeEq : (Staging.Recursive.BodyOutcome.fallthrough inner) = outcome at trace
  cases trace with
  | scrutineeFault => cases outcomeEq
  | patternFault => cases outcomeEq
  | @arm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outcome _ _ _ _ _ _ _ =>
      cases outcome <;> simp_all [Staging.Recursive.BodyOutcome.restore]
  | @default _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outcome _ _ _ _ _ =>
      cases outcome <;> simp_all [Staging.Recursive.BodyOutcome.restore]
  | noBranch => exact Staging.Recursive.BodyOutcome.fallthrough.inj outcomeEq

private theorem breaking_environment {program registry size invocation context before after resolution outer inner}
    (trace : Staging.Recursive.Size.Match program registry size invocation context outer before
      resolution (.breaking inner) after) : inner = outer := by
  generalize outcomeEq : (Staging.Recursive.BodyOutcome.breaking inner) = outcome at trace
  cases trace with
  | scrutineeFault => cases outcomeEq
  | patternFault => cases outcomeEq
  | @arm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outcome _ _ _ _ _ _ _ =>
      cases outcome <;> simp_all [Staging.Recursive.BodyOutcome.restore]
  | @default _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outcome _ _ _ _ _ =>
      cases outcome <;> simp_all [Staging.Recursive.BodyOutcome.restore]
  | noBranch => cases outcomeEq

private theorem continuing_environment {program registry size invocation context before after resolution outer inner}
    (trace : Staging.Recursive.Size.Match program registry size invocation context outer before
      resolution (.continuing inner) after) : inner = outer := by
  generalize outcomeEq : (Staging.Recursive.BodyOutcome.continuing inner) = outcome at trace
  cases trace with
  | scrutineeFault => cases outcomeEq
  | patternFault => cases outcomeEq
  | @arm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outcome _ _ _ _ _ _ _ =>
      cases outcome <;> simp_all [Staging.Recursive.BodyOutcome.restore]
  | @default _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outcome _ _ _ _ _ =>
      cases outcome <;> simp_all [Staging.Recursive.BodyOutcome.restore]
  | noBranch => cases outcomeEq

private theorem stopped_not_fallthrough {program registry size invocation context before after resolution environment inner id statement}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .matchWith resolution)
    (stopped : ReachableMatchContinuations.DefaultStopped invocation.source id resolution)
    (trace : Staging.Recursive.Size.Match program registry size invocation context environment before
      resolution (.fallthrough inner) after) : False := by
  have executed := trace.sound.plain id statement (lookupStatement?_sound found) form
  cases stopped.terminates unique executed


include bridge functions condition in
/-- The lifted match restores outer bindings before its actual suffix. -/
theorem lifts {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {id : StatementId} {rest : List StatementId} {statement : StatementNode}
    {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .matchWith resolution)
    (inner : MatchLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope resolution budget)
    (preservation : ∀ n, MatchPreserves (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope resolution expected type code n)
    (remaining : FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode rest budget ∨
      ReachableMatchContinuations.DefaultStopped invocation.source id resolution) :
    FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode (id :: rest) budget := by
  intro size within mapping world actualContext environment canonical actual before store ξ
    contextLocation native environments heaps locals agrees actualTyped reference read unmapped
    initial conditioned admitted finalContext outcome after trace
  have notTail : ∀ expression, statement.form ≠ .expression expression false := by
    intro expression same
    rw [form] at same
    cases same
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found notTail trace with
    ⟨headSize, reason, strict, contextEq, outcomeEq, failed⟩ |
    ⟨headSize, strict, stopped, executed⟩ |
    ⟨headSize, tailSize, middleContext, nextEnvironment, middle, strict, tailStrict, executed, tail⟩
  · subst finalContext
    subst outcome
    have plain := SelectedCompilationStageMatchSourceInversion.fault unique found form failed
    obtain ⟨staged, reached, lifted, adapted⟩ := inner (Nat.le_trans (Nat.le_of_lt strict) within)
      environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted plain
    cases adapted with
    | completed matched =>
      cases matched
      exact ⟨context, _, _, .matchFault (lookupStatement?_sound found) form lifted, .completed (.fault reason)⟩
    | rejected origin call reason reachedContext reached =>
      exact ⟨context, _, _, .matchFault (lookupStatement?_sound found) form lifted, .rejected origin call reason context reached⟩
  · obtain ⟨contextEq, plain⟩ := SelectedCompilationStageMatchSourceInversion.control unique found form executed
    subst finalContext
    obtain ⟨staged, reached, lifted, adapted⟩ := inner (Nat.le_trans (Nat.le_of_lt strict) within)
      environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted plain
    cases adapted with
    | rejected origin call reason reachedContext reached =>
      exact ⟨context, _, _, .matchFault (lookupStatement?_sound found) form lifted, .rejected origin call reason context reached⟩
    | completed matched =>
      cases matched with
      | returned value =>
        exact ⟨context, _, _, .matchReturned (lookupStatement?_sound found) form lifted, .completed (.returned value)⟩
      | breaking innerEnvironment =>
        obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Match.of_trace lifted
        have same := breaking_environment measured
        subst innerEnvironment
        exact ⟨context, _, _, .matchBreaking (lookupStatement?_sound found) form lifted, .completed (.breaking environment)⟩
      | continuing innerEnvironment =>
        obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Match.of_trace lifted
        have same := continuing_environment measured
        subst innerEnvironment
        exact ⟨context, _, _, .matchContinuing (lookupStatement?_sound found) form lifted, .completed (.continuing environment)⟩
      | fault reason =>
        exact ⟨context, _, _, .matchFault (lookupStatement?_sound found) form lifted, .completed (.fault reason)⟩
      | fallthrough innerEnvironment =>
        obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Match.of_trace lifted
        have same := fallthrough_environment measured
        subst innerEnvironment
        rcases stopped with impossible | rfl
        · cases impossible
        · exact ⟨context, _, _, .matchFallthrough (lookupStatement?_sound found) form lifted .nil,
            .completed (.fallthrough environment)⟩
  · obtain ⟨contextEq, plain⟩ := SelectedCompilationStageMatchSourceInversion.control unique found form executed
    subst middleContext
    obtain ⟨staged, reached, lifted, adapted⟩ := inner (Nat.le_trans (Nat.le_of_lt strict) within)
      environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted plain
    cases adapted with
    | rejected origin call reason reachedContext reached =>
      exact ⟨context, _, _, .matchFault (lookupStatement?_sound found) form lifted, .rejected origin call reason context reached⟩
    | completed matched =>
      cases matched
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Match.of_trace lifted
      have same := fallthrough_environment measured
      subst nextEnvironment
      rcases remaining with remaining | stopped
      · obtain ⟨_, middleStore, middleMap, middleWorld, _, _, middleHeaps, maps, worlds, preserved, metadata,
          reached, _, post⟩ := preservation stagedSize (Nat.le_refl _) environments heaps locals agrees actualTyped
          reference read unmapped initial conditioned admitted measured
        obtain ⟨lastContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
          (Nat.le_trans (Nat.le_of_lt tailStrict) within) (environments.extend maps worlds)
          middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference
          ((preserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (preserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          reached conditioned post tail
        exact ⟨lastContext, result, finalHeap,
          .matchFallthrough (lookupStatement?_sound found) form lifted restTrace, restAdapted⟩
      · exact False.elim (stopped_not_fallthrough unique found form stopped measured)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMatchSequences
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMatchTreeHeads
/-! The actual finite compiler requests close the match head's selected branch
ports. Source contexts and numeric pattern evidence come from original pattern
typing; the genuine marked allocator supplies the actual hidden and arm cells. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMatchTreeHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates GenericMatchChildren
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedConditionalHeads
open CallableIndexedOwnedAdmittedStagedMatchSequences
open SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageLiftBounds (LiftsAt)
open SelectedCompilationStageMatchSequences (MatchLifts)
universe u

theorem lifts {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} {administrative : Core.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {solved : List SolvedRequirement} {sourceCells : Option SourceCoreSourceCells.Allocator}
  {ambientDefinitions : Option Core.DataEnvironment}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (allocator : (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError)))
  (definitions : layouts.definitions = ((CallableIndexedAmbient.ambientDefinitions compiled.indexed)).definitions) (registered : frame.Registered ((CallableIndexedAmbient.ambientDefinitions compiled.indexed)).definitions)
  (extension : SourceCoreRawMetadata.Extends (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).values.registry receiving)
  {context : SourceSemantics.Context} {control : ControlContext} {scope : Scope}
  {id : StatementId} {resolution : MatchResolution} {type : Ty} {reason : Word}
  {expressionCertificate : ExpressionCertificate} {requests : List Request} {code : Expr}
  (receipt : CompatibleMatchCertificates.Certificate ((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions)) invocation.source scope id resolution type reason
    expressionCertificate (Occurs requests) code)
  (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt)
  (signatures : context.signatures = (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).signatures)
  (catalog : SignatureCatalogWellFormed (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).checked.signatures)
  {node : ExpressionNode} (found : invocation.source.lookupExpression? resolution.scrutinee = some node)
  (typed : ExpressionHasType invocation.source context resolution.scrutinee node.type)
  {caseFacts : List BodyFacts}
  (casesTyped : MatchCasesHaveType invocation.source control context node.type resolution.cases caseFacts)
  (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
    ∃ finalContext facts, StatementsHaveType invocation.source control context statements finalContext facts)
  (budget : Nat) (condition : Location → NativeFrame → Prop)
  (producer : ProtectedStateTransition.MarkedAllocation.Producer callerProtocol layouts frame (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions))
  (bindings : ProtectedStateTransition.Bindings callerProtocol)
  (acquire : ∀ location native, condition location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)

    (_unique : NodeOccurrencesUnique invocation.source)
    (_children : ∀ childSize, childSize < budget →
      LiftsAt bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions) stages invocation expressionCertificate childSize)
    (_preservation : ∀ childSize, PreservesAt bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions) stages invocation expressionCertificate faults childSize)
    (_bodies : ∀ request, request ∈ requests → ∀ childContext,
      ScopedContextFor invocation.source context (resolution.hiddenScrutinee :: scope.map Prod.fst)
        node.type resolution.cases resolution.defaultBody request childContext →
      ProtectedStateImperativeTypedSourceSites.Statements invocation.source childContext request.statements →
      FlowLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
        (stages := stages) (invocation := invocation)
        bridge functions condition childContext request.scope false request.statements budget) :
    MatchLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation)
      bridge functions condition context scope resolution budget := by
  obtain ⟨lowered, child, restricted⟩ := GenericImperativeMatch.Certificate.singleton receipt
  intro size within mapping world actualContext environment canonical actual before store ξ contextLocation native
    environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted outcome after trace
  refine SelectedCompilationStageMatchLifting.lifts (faults := faults)
    (expressionCertificate := GenericImperativeMatch.Singleton scope resolution.scrutinee lowered) (lowered := lowered) bridge functions onError allocator definitions registered extension
    restricted (show CompatibleMatchSelectionPrefix.Ordinary restricted from ordinary) _unique
    (fun numeric => RequirementProves context numeric.requirement numeric.predicate) signatures (fun _ proof => proof)
    (CompatibleMatchTypedLiteralSites.Certificate.sites restricted signatures found casesTyped) catalog found typed
    (by intro other actual; exact actual.2.2) casesTyped (fun same => defaultTyped _ same) budget condition producer bindings acquire
    ?_ ?_ ?_ ?_ within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  · intro childSize smaller actualScope actualId actualCode singleton
    rcases singleton with ⟨rfl, rfl, rfl⟩
    exact _children childSize smaller child
  · intro childSize actualScope actualId actualCode singleton
    rcases singleton with ⟨rfl, rfl, rfl⟩
    exact _preservation childSize child
  · intro sourceValue hiddenScope environment heap statements bindings finalScope finalEnvironment finalHeap body sameScope selected bodySelected
      armContext staticFinal facts extended bodyTyped
    have scopeIds := selected_arm_ids bodySelected
    rw [sameScope] at scopeIds
    cases bodySelected with
    | arm binders allocated certified =>
      exact @_bodies ⟨_, statements, body⟩ certified armContext
        (ScopedContextFor.selected_arm_at ⟨_, statements, body⟩ rfl scopeIds casesTyped selected extended)
        ⟨control, staticFinal, facts, bodyTyped⟩
  · intro sourceValue hiddenScope environment heap statements finalScope finalEnvironment finalHeap body sameScope selected bodySelected
      staticFinal facts bodyTyped
    have scopeIds := (selected_default_ids bodySelected).trans sameScope
    cases bodySelected with
    | default certified =>
      exact @_bodies ⟨_, statements, body⟩ certified context (.default selected.defaultBody_eq scopeIds) ⟨control, staticFinal, facts, bodyTyped⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMatchTreeHeads
end
