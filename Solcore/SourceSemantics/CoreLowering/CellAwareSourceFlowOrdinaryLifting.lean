import Solcore.SourceSemantics.CoreLowering.CellAwareScopeExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowLiftBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedOrdinaryPrefix
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLexicalInversion
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping

/-! A real ordinary Source initializer is lifted before allocation. A failed
or rejected child keeps its reached heap, and successful allocation retains
all earlier generalized descriptors for the actual Source suffix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowOrdinaryLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
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


include registered in
theorem initialized {mode : Bool} {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : StatementId} {node : StatementNode} {binder : TypedBinder} {initializer : ExpressionId}
    {initializerNode : ExpressionNode} {rest : List StatementId} {type : Ty}
    {lowered : SourceCoreBasic.LoweredExpr} {body : Expr} {administrative : Core.Context}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
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
    (remaining : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer nextContext ((binder.id, lowered.type) :: scope) mode rest) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped current admitted authority physical owner sameLocation ready
    finalContext outcome after trace
  have unique := runtime.graph.nodeOccurrencesUnique
  have contains : ContainsStatement invocation.source id node := by simpa only [sourceEq] using lookupStatement?_sound found
  rcases SelectedCompilationStageLexicalInversion.initialized (mode := mode) (invocation := invocation)
      (by simpa only [sourceEq] using unique) (by simpa only [sourceEq] using found) form mono
      (by simpa only [sourceEq] using extended) trace with
    ⟨childSize, reason, _strict, contextEq, outcomeEq, child⟩ |
    ⟨childSize, tailSize, sourceValue, middle, location, bound, _childStrict, _tailStrict, child, allocated, tail⟩
  · subst finalContext
    subst outcome
    obtain ⟨staged, reached, lifted, adapted⟩ := childLift runtime covers sameLedger childSize value
      (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
      environments heaps locals agrees actualTyped current admitted authority physical owner sameLocation child
    cases adapted with
    | completed => exact ⟨_, _, _, .letFault contains form mono lifted, .completed (.fault reason)⟩
    | rejected origin call reason reached => exact ⟨_, _, _, .letFault contains form mono lifted, .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ := childLift runtime covers sameLedger childSize value
      (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
      environments heaps locals agrees actualTyped current admitted authority physical owner sameLocation child
    cases adapted with
    | rejected origin call reason reached => exact ⟨_, _, _, .letFault contains form mono lifted, .rejected origin call reason _ reached⟩
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
          remaining nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
            (runtime.transport (.ofBinderExtends extended))
            ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
            ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
            (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended)
            reachedState nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tail
        exact ⟨resultContext, resultOutcome, resultHeap,
          .letInitialized contains form lifted mono (by simpa only [sourceEq] using extended) allocated stagedTail, tailAdapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowOrdinaryLifting
