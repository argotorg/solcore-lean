import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftSequence
import Solcore.SourceSemantics.CoreLowering.CallablePreparedOperatorSourceBounds

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageOperatorArgumentsLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open DataExpressionSequence
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState (Records)
open CallableIndexedOwnedSourceAdmission (Admission)
open SelectedCompilationStageLiftBounds (LiftsAt)
open SelectedCompilationStageLiftSequence (SequenceLift)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (Header compiled program)} {keys : List (Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {certificate : GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

private def MemberTyping (ids : List ExpressionId) : Prop :=
  ∀ id, id ∈ ids → ∀ node, invocation.source.lookupExpression? id = some node →
    ExpressionHasType invocation.source context id node.type

private theorem values_members (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
    {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : ∀ size, size < budget → LiftsAt bridge context model registry invocation certificate size)
    (preservation : ∀ size, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model registry invocation certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (execution : CallablePreparedOperatorSourceBounds.ArgumentsAt program budget context invocation.evidence
      invocation.source environment before ids sources after) :
    SequenceLift program registry invocation context environment before ids (.ok sources) after := by
  induction tree generalizing mapping world actual actualContext before store ξ sources after with
  | nil =>
    cases execution
    exact ⟨_, _, .nil, .completed⟩
  | single found generated =>
    cases execution with
    | cons head strict tail =>
      cases tail
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        strict
        generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
        initial admitted (.value head)
      cases adapted with
      | completed => exact ⟨_, _, .cons trace .nil, .completed⟩
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | cons head strict rest =>
      have typed := sourceTyped _ (by simp) _ found
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        strict
        generated found typed environments heaps locals layout actualTyped initial admitted (.value head)
      cases adapted with
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
      | completed =>
        obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace trace
        obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
            maps, worlds, _frame, metadata, middleState, _related, post⟩ := preservation stagedSize
          generated found typed environments heaps locals layout actualTyped initial admitted measured
        obtain ⟨outcome, finalHeap, restTrace, restAdapted⟩ := ih
          (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
          (environments.extend maps worlds) middleHeaps (locals.mono metadata) layout
          (actualTyped.weaken worlds) middleState post.at_value.2 rest
        cases restAdapted with
        | completed => exact ⟨_, _, .cons trace restTrace, .completed⟩
        | rejected origin call reason reached =>
          exact ⟨_, _, .tailFault trace restTrace, .rejected origin call reason _⟩

theorem values (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
    {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (unique : NodeOccurrencesUnique invocation.source)
    (sourceTyped : ExpressionsHaveTypes invocation.source context ids sourceTypes)
    (children : ∀ size, size < budget → LiftsAt bridge context model registry invocation certificate size)
    (preservation : ∀ size, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model registry invocation certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (execution : CallablePreparedOperatorSourceBounds.ArgumentsAt program budget context invocation.evidence
      invocation.source environment before ids sources after) :
    SequenceLift program registry invocation context environment before ids (.ok sources) after := by
  apply values_members bridge budget tree _ children preservation environments heaps locals layout actualTyped
    initial admitted execution
  intro id member node found
  exact CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique sourceTyped member found

private theorem fault_members (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
    {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : ∀ size, size < budget → LiftsAt bridge context model registry invocation certificate size)
    (preservation : ∀ size, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model registry invocation certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (execution : CallablePreparedOperatorSourceBounds.ArgumentsFaultAt program budget context invocation.evidence
      invocation.source environment before ids reason after) :
    SequenceLift program registry invocation context environment before ids (.error reason) after := by
  induction tree generalizing mapping world actual actualContext before store ξ reason after with
  | nil => cases execution
  | single found generated =>
    cases execution with
    | head failed strict =>
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        strict
        generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
        initial admitted (.fault failed)
      cases adapted with
      | completed => exact ⟨_, _, .headFault trace, .completed⟩
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
    | tail _ _ failed => cases failed
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | head failed strict =>
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        strict
        generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
        initial admitted (.fault failed)
      cases adapted with
      | completed => exact ⟨_, _, .headFault trace, .completed⟩
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
    | tail head strict rest =>
      have typed := sourceTyped _ (by simp) _ found
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        strict
        generated found typed environments heaps locals layout actualTyped initial admitted (.value head)
      cases adapted with
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
      | completed =>
        obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace trace
        obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
            maps, worlds, _frame, metadata, middleState, _related, post⟩ := preservation stagedSize
          generated found typed environments heaps locals layout actualTyped initial admitted measured
        obtain ⟨outcome, finalHeap, restTrace, restAdapted⟩ := ih
          (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
          (environments.extend maps worlds) middleHeaps (locals.mono metadata) layout
          (actualTyped.weaken worlds) middleState post.at_value.2 rest
        cases restAdapted with
        | completed => exact ⟨_, _, .tailFault trace restTrace, .completed⟩
        | rejected origin call reason reached =>
          exact ⟨_, _, .tailFault trace restTrace, .rejected origin call reason _⟩

theorem fault (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
    {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (unique : NodeOccurrencesUnique invocation.source)
    (sourceTyped : ExpressionsHaveTypes invocation.source context ids sourceTypes)
    (children : ∀ size, size < budget → LiftsAt bridge context model registry invocation certificate size)
    (preservation : ∀ size, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model registry invocation certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (execution : CallablePreparedOperatorSourceBounds.ArgumentsFaultAt program budget context invocation.evidence
      invocation.source environment before ids reason after) :
    SequenceLift program registry invocation context environment before ids (.error reason) after := by
  apply fault_members bridge budget tree _ children preservation environments heaps locals layout actualTyped
    initial admitted execution
  intro id member node found
  exact CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique sourceTyped member found

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageOperatorArgumentsLifting
