import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedLiftBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedWhileHeads

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
