import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsSourceInversion

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsDiscardLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageForLiftBounds
open SelectedCompilationStageLiftBounds (LiftsAt)
universe u

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
  {faults : RecursiveStageMeaning.FaultRep}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions


theorem nil {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} :
    ItemsLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition [] budget := by
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready finalContext outcome trace
  obtain ⟨rfl, rfl, rfl⟩ := SelectedCompilationStageForItemsSourceInversion.nil trace
  exact ⟨_, .done environment, _, .empty, .completed (.fallthrough _)⟩

include bridge functions condition in
/-- A completed expression supplies the real next physical state before the
suffix is lifted. A rejected expression stops at its own reached heap. -/
theorem lifts {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {rest : List ForItemForm}
    {expression : ExpressionId} {expressionNode : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr} {certificate : GenericExpressionMeaning.Certificate}
    (expressionFound : invocation.source.lookupExpression? expression = some expressionNode)
    (typed : ExpressionHasType invocation.source context expression expressionNode.type)
    (generated : certificate scope expression lowered)
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults childSize)
    (remaining : ItemsLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition rest budget) :
    ItemsLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition (.expression expression :: rest) budget := by
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready finalContext outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  rcases SelectedCompilationStageForItemsSourceInversion.discard trace with
    ⟨childSize, reason, strict, rfl, rfl, evaluated⟩ |
    ⟨childSize, tailSize, sourceValue, middle, strict, tailStrict, evaluated, tail⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | completed => exact ⟨_, _, _, .expressionFailure lifted,
        .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .expressionFailure lifted,
        .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .expressionFailure lifted,
        .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
          maps, worlds, framePreserved, metadata, middleState, _related, post⟩ :=
        preservation stagedSize generated expressionFound typed environments heaps locals agrees actualTyped
          initial admitted measured
      have frameRead := (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
      have stillUnmapped := (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
      obtain ⟨nextContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
        (Nat.le_trans (Nat.le_of_lt tailStrict) within)
        ⟨_, _, _, environments.extend maps worlds, middleHeaps, locals.mono metadata, agrees,
          actualTyped.weaken worlds, reference, frameRead, stillUnmapped, middleState, conditioned, post.at_value.2⟩ tail
      exact ⟨nextContext, result, finalHeap, .expression lifted restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsDiscardLifting
