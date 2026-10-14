import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsLexicalLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds (LiftsAt)
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageForLiftBounds
open GenericLexicalStatements
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (definitions : layouts.definitions = (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (registered : frame.Registered (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (producer : ProtectedStateTransition.OrdinaryAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions))
  (condition : Location → NativeFrame → Prop)
  (acquire : ∀ location native, condition location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer location native)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions


include bridge functions definitions registered producer acquire in
/-- The original absent allocation constructs the actual extended physical
state before the body suffix is lifted. -/
theorem absent {budget : Nat} {context nextContext : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {rest : List ForItemForm}
    {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (ordinary : invocation.source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projection : compiled.compatible.checked.catalog.project binder.scheme.body = .ok payload)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest invocation.source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (absentRequest invocation.source scope binder payload))
    (same : annotation.original = allocation.expression)
    {administrative : Core.Context}
    (remaining : ItemsLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := nextContext) (scope := ((binder.id, payload) :: scope)) bridge functions condition rest budget) :
    ItemsLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition (.letDecl binder none :: rest) budget := by
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready finalContext outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  obtain ⟨tailSize, location, bound, strict, allocated, tail⟩ :=
    SelectedCompilationStageForItemsSourceInversion.absent mono extended trace
  obtain ⟨_captured, _captures, _capturedTyped, _allocationEval, nextEnvironments, nextHeaps, nextLocals,
      nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, _allocatedRelated, nextAdmitted⟩ :=
    CallableIndexedOwnedAdmittedLexicalAllocation.allocate_absent bridge functions definitions registered producer
      mono extended ordinary projection allocation annotation same environments heaps locals agrees actualTyped
      reference read allocated initial ((acquire _ _ conditioned) initial read) admitted
  obtain ⟨resultContext, result, resultHeap, restTrace, restAdapted⟩ := remaining
    (Nat.le_trans (Nat.le_of_lt strict) within)
    ⟨_, _, _, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
      nextReference, nextRead, (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1,
      reached, conditioned, nextAdmitted⟩ tail
  exact ⟨resultContext, result, resultHeap,
    .absent mono extended allocated restTrace, restAdapted⟩

include bridge functions definitions registered producer acquire in
/-- The initializer reaches its own heap first. Its real represented value
then initializes the original binder before the suffix executes. -/
theorem initialized {budget : Nat} {context nextContext : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {rest : List ForItemForm}
    {binder : TypedBinder} {expression : ExpressionId}
    {expressionNode : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (ordinary : invocation.source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (expressionFound : invocation.source.lookupExpression? expression = some expressionNode)
    (sourceType : expressionNode.type = binder.scheme.body)
    (typed : ExpressionHasType invocation.source context expression expressionNode.type)
    (generated : certificates context scope expression lowered)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest invocation.source scope binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (initializedRequest invocation.source scope binder lowered.type))
    (same : annotation.original = allocation.expression)
    (children : ∀ childSize, childSize < budget →
      LiftsAt bridge context model stages invocation (certificates context) childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation (certificates context) faults childSize)
    {administrative : Core.Context}
    (remaining : ItemsLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := nextContext) (scope := ((binder.id, lowered.type) :: scope)) bridge functions condition rest budget) :
    ItemsLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition (.letDecl binder (some expression) :: rest) budget := by
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready finalContext outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  rcases SelectedCompilationStageForItemsSourceInversion.initialized mono extended trace with
    ⟨childSize, reason, strict, rfl, rfl, evaluated⟩ |
    ⟨childSize, tailSize, sourceValue, middle, location, bound, strict, tailStrict, evaluated, allocated, tail⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | completed => exact ⟨_, _, _, .initializerFault mono lifted,
        .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .initializerFault mono lifted,
        .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .initializerFault mono lifted,
        .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨value, middleStore, middleMap, middleWorld, _evaluated, represented, middleHeaps,
          maps, worlds, framePreserved, metadata, middleState, _related, post⟩ :=
        preservation stagedSize generated expressionFound typed environments heaps locals agrees actualTyped
          initial admitted measured
      cases represented with
      | value payload =>
        have frameRead := (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        have stillUnmapped := (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        obtain ⟨_captured, _captures, _capturedTyped, _allocationEval, nextEnvironments, nextHeaps, nextLocals,
            nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, nextState, _allocatedRelated, nextAdmitted⟩ :=
          CallableIndexedOwnedAdmittedLexicalAllocation.allocate_initialized bridge functions definitions registered producer
            mono extended ordinary allocation annotation same (sourceType ▸ post.at_value.1) (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
            reference frameRead allocated middleState ((acquire _ _ conditioned) middleState frameRead) post.at_value.2
        obtain ⟨resultContext, result, resultHeap, restTrace, restAdapted⟩ := remaining
          (Nat.le_trans (Nat.le_of_lt tailStrict) within)
          ⟨_, _, _, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
            nextReference, nextRead, (allocationFrame contextLocation stillUnmapped (List.getElem?_eq_some_iff.mp frameRead).1).1,
            nextState, conditioned, nextAdmitted⟩ tail
        exact ⟨resultContext, result, resultHeap,
          .initialized mono extended lifted allocated restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsLexicalLifting
