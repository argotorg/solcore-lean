import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftSequence
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceLiftBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionSequence

/-! Lift ordered ordinary arguments at their actual intervening states.
A completed staged child is passed through the closed preservation family
before the next child is lifted. A rejection keeps that child's exact prefix
heap and does not require an argument-tail execution. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceSequenceLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open DataExpressionSequence
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState (Records)
open CallableIndexedOwnedSourceAdmission (Admission)
open CellAwareScopeSourceLiftBounds (LiftsAt)
open SelectedCompilationStageLiftSequence (SequenceLift)
open Staging.Recursive.Lifting (ExpressionLift Adapted embed)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (Header compiled program)} {keys : List (Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
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
    (children : ∀ size, size < budget → LiftsAt bridge context model named registry invocation certificate size)
    (preservation : ∀ size, CellAwareScopeExpressionBounds.PreservesAt
      bridge context model named registry invocation certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerFrame : owner.key.frameLocation = physical.location) {size : Nat}
    (execution : SourceExecutionSize.ExpressionsEvaluate program size context invocation.evidence
      invocation.source environment before ids sources after) (within : size ≤ budget) :
    SequenceLift program registry invocation context environment before ids (.ok sources) after := by
  induction tree generalizing size mapping world actual actualContext before store ξ sources after with
  | nil =>
    cases execution
    exact ⟨_, _, .nil, .completed⟩
  | single found generated =>
    cases execution with
    | cons head tail =>
      cases tail
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
        generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
        initial admitted authority physical owner ownerFrame (.value head)
      cases adapted with
      | completed => exact ⟨_, _, .cons trace .nil, .completed⟩
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | cons head rest =>
      have typed := sourceTyped _ (by simp) _ found
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
        generated found typed environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame (.value head)
      cases adapted with
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
      | completed =>
        obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace trace
        obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
            maps, worlds, frame, metadata, effect, middleState, _related, post⟩ := preservation stagedSize
          generated found typed environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame measured
        obtain ⟨outcome, finalHeap, restTrace, restAdapted⟩ := ih
          (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
          (environments.extend maps worlds) middleHeaps (locals.mono metadata) layout
          (actualTyped.weaken worlds) middleState post.at_value.2 (authority.transport effect)
          (physical.transport effect frame) ownerFrame rest
          (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
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
    (children : ∀ size, size < budget → LiftsAt bridge context model named registry invocation certificate size)
    (preservation : ∀ size, CellAwareScopeExpressionBounds.PreservesAt
      bridge context model named registry invocation certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerFrame : owner.key.frameLocation = physical.location) {size : Nat}
    (execution : SourceExecutionSize.ExpressionsEvaluate program size context invocation.evidence
      invocation.source environment before ids sources after) (within : size ≤ budget) :
    SequenceLift program registry invocation context environment before ids (.ok sources) after := by
  apply values_members bridge budget tree _ children preservation environments heaps locals layout actualTyped
    initial admitted authority physical owner ownerFrame execution within
  intro id member node found
  exact CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique sourceTyped member found

private theorem fault_members (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
    {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : ∀ size, size < budget → LiftsAt bridge context model named registry invocation certificate size)
    (preservation : ∀ size, CellAwareScopeExpressionBounds.PreservesAt
      bridge context model named registry invocation certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerFrame : owner.key.frameLocation = physical.location) {size : Nat}
    (execution : SourceExecutionSize.ExpressionsFault program size context invocation.evidence
      invocation.source environment before ids reason after) (within : size ≤ budget) :
    SequenceLift program registry invocation context environment before ids (.error reason) after := by
  induction tree generalizing size mapping world actual actualContext before store ξ reason after with
  | nil => cases execution
  | single found generated =>
    cases execution with
    | head failed =>
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
        generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
        initial admitted authority physical owner ownerFrame (.fault failed)
      cases adapted with
      | completed => exact ⟨_, _, .headFault trace, .completed⟩
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
    | tail _ failed => cases failed
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | head failed =>
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
        generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
        initial admitted authority physical owner ownerFrame (.fault failed)
      cases adapted with
      | completed => exact ⟨_, _, .headFault trace, .completed⟩
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
    | tail head rest =>
      have typed := sourceTyped _ (by simp) _ found
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
        generated found typed environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame (.value head)
      cases adapted with
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
      | completed =>
        obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace trace
        obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
            maps, worlds, frame, metadata, effect, middleState, _related, post⟩ := preservation stagedSize
          generated found typed environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame measured
        obtain ⟨outcome, finalHeap, restTrace, restAdapted⟩ := ih
          (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
          (environments.extend maps worlds) middleHeaps (locals.mono metadata) layout
          (actualTyped.weaken worlds) middleState post.at_value.2 (authority.transport effect)
          (physical.transport effect frame) ownerFrame rest
          (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
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
    (children : ∀ size, size < budget → LiftsAt bridge context model named registry invocation certificate size)
    (preservation : ∀ size, CellAwareScopeExpressionBounds.PreservesAt
      bridge context model named registry invocation certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerFrame : owner.key.frameLocation = physical.location) {size : Nat}
    (execution : SourceExecutionSize.ExpressionsFault program size context invocation.evidence
      invocation.source environment before ids reason after) (within : size ≤ budget) :
    SequenceLift program registry invocation context environment before ids (.error reason) after := by
  apply fault_members bridge budget tree _ children preservation environments heaps locals layout actualTyped
    initial admitted authority physical owner ownerFrame execution within
  intro id member node found
  exact CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique sourceTyped member found

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceSequenceLifting
