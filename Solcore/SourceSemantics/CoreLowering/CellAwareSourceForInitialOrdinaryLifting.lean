import Solcore.SourceSemantics.CoreLowering.CellAwareScopeExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedOrdinaryPrefix
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialInversion
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping

/-! A real ordinary Source initializer is lifted before allocation. A failed
or rejected child keeps its reached heap, and successful allocation retains
all earlier generalized descriptors for the actual Source suffix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialOrdinaryLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open CellAwareSourceForInitialBounds (InitializersLifts)
open CallableIndexedOwnedAdmittedStagedForInitializerSource
open TypedLexicalWhile (initializedRequest sequence)

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
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}


private theorem restore_adapted {outer inner : SourceSemantics.Context}
    (environment : Dynamic.Environment) {plain : Dynamic.ControlOutcome} {staged : Staging.Recursive.BodyOutcome}
    {after reached : Dynamic.Heap}
    (adapted : SelectedCompilationStageBodyLiftBounds.BodyAdapted inner plain after inner staged reached) :
    SelectedCompilationStageBodyLiftBounds.BodyAdapted outer (Dynamic.restoreControl environment plain) after
      outer (staged.restore environment) reached := by
  cases adapted with
  | completed matched => cases matched <;> exact .completed (by constructor)
  | rejected origin call reason finalContext reached => exact .rejected origin call reason _ _

variable {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}

include registered in
theorem initialized {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {binder : TypedBinder} {initializer : ExpressionId}
    {initializerNode : ExpressionNode} {rest : List ForItemForm} {type : Ty}
    {lowered : SourceCoreBasic.LoweredExpr} {body : Expr} {administrative : Core.Context}
      (member : binder ∈ SourceCoreDataPlaces.declaredBinders (source named))
      (mono : binder.scheme.quantified = [])
      (extended : BinderExtends (source named).owner context binder nextContext)
      (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : (source named).lookupExpression? initializer = some initializerNode)
      (valueType : initializerNode.type = binder.scheme.body)
      (typed : ExpressionHasType (source named) context initializer initializerNode.type)
      (value : certificates context scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts named.signature.key []
        (initializedRequest (source named) scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
        whole.indexed.base.globals.length
        (whole.indexed.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
        (initializedRequest (source named) scope binder lowered.type))
      (same : annotation.original = allocation.expression)
    (sourceEq : invocation.source = source named)
    (childLift : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation (certificates context) size)
    (preservation : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context model named registry invocation (certificates context) faults size)
    (remaining : InitializersLifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) (context := nextContext) (scope := ((binder.id, lowered.type) :: scope)) bridge producer rest test postItems statements) :
    InitializersLifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) (context := context) (scope := scope) bridge producer (.letDecl binder (some initializer) :: rest) test postItems statements := by
  intro size environment canonical actual actualContext embedding before after reachedReady outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, runtime, covers, sameLedger,
    current, admitted, authority, physical, owner, sameLocation, ready⟩ := reachedReady
  rcases SelectedCompilationStageForInitialInversion.initialized mono
      (by simpa only [sourceEq] using extended) trace with
    ⟨childSize, reason, _strict, outcomeEq, child⟩ |
    ⟨childSize, tailSize, sourceValue, middle, location, bound, nextOutcome, _childStrict, _tailStrict, sameOutcome, child, allocated, tail⟩
  · subst outcome
    obtain ⟨staged, reached, lifted, adapted⟩ := childLift runtime covers sameLedger childSize value
      (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
      environments heaps locals agrees actualTyped current admitted authority physical owner sameLocation child
    obtain ⟨measuredSize, measuredChild⟩ := Staging.Recursive.Size.Expression.of_trace lifted
    cases adapted with
    | completed => exact ⟨_, _, _, initializer_fault mono measuredChild, .completed (.fault reason)⟩
    | rejected origin call reason reached => exact ⟨_, _, _, initializer_fault mono measuredChild, .rejected origin call reason _ reached⟩
  · subst outcome
    obtain ⟨staged, reached, lifted, adapted⟩ := childLift runtime covers sameLedger childSize value
      (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
      environments heaps locals agrees actualTyped current admitted authority physical owner sameLocation child
    obtain ⟨measuredSize, measuredChild⟩ := Staging.Recursive.Size.Expression.of_trace lifted
    cases adapted with
    | rejected origin call reason reached => exact ⟨_, _, _, initializer_fault mono measuredChild, .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stageSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨native, middleStore, middleMap, middleWorld, evaluated, represented, middleHeaps,
          maps, worlds, frame, metadata, effect, middleState, _expressionRelated, post⟩ :=
        preservation runtime covers sameLedger stageSize value
          (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
          environments heaps locals agrees actualTyped current admitted authority physical owner sameLocation measured
      cases represented with
      | value payload =>
        let middlePhysical := physical.transport effect frame
        obtain ⟨marker, _agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
            _preserved, _allocationEffect, nextAuthority, reachedState, _related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
          CellAwareNamedOrdinaryPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
            evaluated (valueType ▸ payload) (valueType ▸ post.at_value.1)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
            middleState post.at_value.2 (authority.transport effect) middlePhysical
            (ready middleState middlePhysical.read) allocated type body
        have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
          intro index current stored
          have previous := ready current (by simpa only [locationEq, nativeEq, middlePhysical,
            CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using stored)
          simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location,
            CellAwareScopePhysical.Physical.transport_native] using previous
        obtain ⟨resultContext, resultOutcome, resultHeap, stagedTail, tailAdapted⟩ :=
          remaining ⟨_, _, _, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
      runtime.transport (.ofBinderExtends extended),
      (Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers,
      (Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger,
      reachedState, nextAdmitted, nextAuthority, nextPhysical, owner, sameLocation.trans locationEq.symm, nextReady⟩ tail
        exact ⟨_, _, resultHeap,
          prepend_initialized mono (by simpa only [sourceEq] using extended) measuredChild allocated stagedTail, restore_adapted environment tailAdapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialOrdinaryLifting
