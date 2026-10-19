import Solcore.SourceSemantics.CoreLowering.CellAwareScopeExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceLiftBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionSourceBounds

/-! Ordinary conditionals lift only the selected branch. The actual staged
condition supplies the physical state of that branch; a rejected condition
stops at its reached heap. Source Bool typing excludes the malformed ordinary
condition alternative using the genuine successful prefix receipt. -/

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceConditionalLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState (Records)
open CellAwareScopeSourceLiftBounds (LiftsAt)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CompatibleExpressionPrimitives (Metadata)
open Staging.Recursive.Lifting (ExpressionLift Adapted embed)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (Header compiled program)} {keys : List (Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {named : SourceCoreGeneralFunctions.Function}
  {receiving : SourceCoreRawMetadata.Registry}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {children : GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep} {checked : SourceCoreCompatibleCatalog.Checked}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

theorem conditional (size : Nat)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {lowered conditionCode thenCode elseCode : SourceCoreBasic.LoweredExpr}
    {condition thenId elseId : ExpressionId}
    (metadata : Metadata checked invocation.source id node lowered.type)
    (form : node.form = .conditional condition thenId elseId)
    (unique : NodeOccurrencesUnique invocation.source)
    (conditionNativeType : conditionCode.type = .bool)
    (conditionGenerated : children scope condition conditionCode)
    (thenGenerated : children scope thenId thenCode)
    (elseGenerated : children scope elseId elseCode)
    (childLift : ∀ child, child < size → LiftsAt bridge context model named registry invocation children child)
    (preservation : ∀ child, CellAwareScopeExpressionBounds.PreservesAt
      bridge context model named registry invocation children faults child) :
    LiftsAt bridge context model named registry invocation (Point scope id lowered) size := by
  intro current expression code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame execution
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨conditionNode, thenNode, elseNode, conditionFound, thenFound, elseFound,
      _conditionType, _thenType, _elseType, conditionTyped, thenTyped, elseTyped⟩ :=
    CompatibleExpressionConditionals.conditional_source_types unique metadata.found form metadata.coercions typed
  have occurrence : Staging.Recursive.Occurrence invocation expression (.conditional condition thenId elseId) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  cases RecursiveNamedExpressionSourceBounds.conditional_inv metadata form unique execution with
  | fault failed smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := childLift _ smaller conditionGenerated conditionFound
      conditionTyped environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame (.fault failed)
    cases adapted with
    | completed => exact ⟨_, _, .conditionalFault occurrence trace, .completed⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .conditionalFault occurrence trace, .rejected origin call reason _⟩
  | @branch childSize branchSize flag middle outcome after conditionTrace branchTrace smaller branchSmaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := childLift _ smaller conditionGenerated conditionFound
      conditionTyped environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame (.value conditionTrace)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, .conditionalFault occurrence trace, .rejected origin call reason _⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace trace
      obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
          maps, worlds, frame, heapMetadata, effect, middleState, _related, post⟩ := preservation stagedSize
        conditionGenerated conditionFound conditionTyped environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame measured
      cases flag with
      | false =>
        obtain ⟨result, finalHeap, branch, adapted⟩ := childLift _ branchSmaller elseGenerated elseFound elseTyped
          (environments.extend maps worlds) middleHeaps (locals.mono heapMetadata) layout
          (actualTyped.weaken worlds) middleState post.at_value.2 (authority.transport effect) (physical.transport effect frame) owner ownerFrame branchTrace
        exact ⟨result, finalHeap, .conditional occurrence trace branch, adapted⟩
      | true =>
        obtain ⟨result, finalHeap, branch, adapted⟩ := childLift _ branchSmaller thenGenerated thenFound thenTyped
          (environments.extend maps worlds) middleHeaps (locals.mono heapMetadata) layout
          (actualTyped.weaken worlds) middleState post.at_value.2 (authority.transport effect) (physical.transport effect frame) owner ownerFrame branchTrace
        exact ⟨result, finalHeap, .conditional occurrence trace branch, adapted⟩
  | invalid child invalid _runtimeType smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := childLift _ smaller conditionGenerated conditionFound
      conditionTyped environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame (.value child)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, .conditionalFault occurrence trace, .rejected origin call reason _⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace trace
      obtain ⟨_value, _store, _mapping, _world, _evaluated, represented, _heaps,
          _maps, _worlds, _frame, _metadata, _effect, _state, _related, _post⟩ := preservation stagedSize
        conditionGenerated conditionFound conditionTyped environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame measured
      cases represented with
      | value payload =>
        rw [conditionNativeType] at payload
        obtain ⟨flag, sourceEq, _coreEq⟩ := CompatibleExpressionPrimitives.bool_fields payload
        cases sourceEq
        exact False.elim (invalid trivial)

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceConditionalLifting
