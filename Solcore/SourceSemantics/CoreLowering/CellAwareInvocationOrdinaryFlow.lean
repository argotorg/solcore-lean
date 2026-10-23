import Solcore.SourceSemantics.CoreLowering.SourceLetDeclarationFacts
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationFlowBounds
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationReachedReads
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationOrdinaryPrefix
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAbsentPrefix

/-! Actual local declaration allocation and its remaining flow retain the same
invocation, descriptor attachment and physical frame in both directions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationOrdinaryFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open TypedLexicalControl (absentRequest)
open TypedLexicalWhile (initializedRequest sequence)
section RequestSource

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions)
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  (index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame (GeneralizedLocalDescriptorHeap.cellModel model
      (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep)
  {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {mode : Bool} {id : StatementId} {node : StatementNode}
  {binder : TypedBinder} {initializer : ExpressionId} {rest : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {lowered : SourceCoreBasic.LoweredExpr} {body : Expr}
  {stored payload : Ty}
  (reached : index.Reached (.statement id))
  (read : index.policy.readStatement index.compilerSource id = .ok (node, stored))
  (form : node.form = .letDecl binder (some initializer))
  (mono : binder.scheme.quantified = [])
  (extended : BinderExtends index.source.owner context binder nextContext)
  {allocationSource : TypedSource}
  (allocationInputs : allocationSource.inputs.map (·.id) = index.source.inputs.map (·.id))
  (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts index.owner index.active
    (initializedRequest allocationSource scope binder lowered.type))
  (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
    whole.indexed.base.globals.length
    (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))
    (initializedRequest allocationSource scope binder lowered.type))
  (same : annotation.original = allocation.expression)
  (sourceEq : invocation.source = index.source)
  {initializerNode : ExpressionNode} {certificate : GenericExpressionMeaning.Certificate}
  (initializerFound : index.source.lookupExpression? initializer = some initializerNode)
  (valueType : initializerNode.type = binder.scheme.body)
  (typed : ExpressionHasType index.source context initializer initializerNode.type)
  (certified : certificate scope initializer lowered)

include allocationInputs reached read form mono extended allocation annotation same sourceEq registered bindings initializerFound valueType typed certified in
theorem preserves_at_source (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment)
      bridge context model index registry invocation certificate faults budget)
    (tail : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, lowered.type) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type (sequence type lowered.expression annotation.expression body) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
    finalContext outcome after trace
  have found := index.statement_read_reached reached read
  obtain ⟨member, _declaration, ordinary⟩ := SourceLetDeclarationFacts.of_lookup physical.ownership found form
  have requestOrdinary : allocationSource.inputs.any (fun input => decide (input.id = binder.id)) = false := by
    have ids := congrArg (fun inputs : List Resolved.LocalId => inputs.any (fun input => decide (input = binder.id))) allocationInputs
    simp only [List.any_map, Function.comp_def] at ids
    exact ids.trans ordinary
  have unique := runtime.graph.nodeOccurrencesUnique
  rcases CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.initialized
      (by simpa only [sourceEq] using unique) (by simpa only [sourceEq] using found) form mono
      (by simpa only [sourceEq] using extended) trace with
    ⟨childSize, failure, sameSize, contextEq, outcomeEq, child⟩ |
    ⟨childSize, tailSize, sourceValue, location, middle, bound, sameSize, child, allocated, remainingTrace⟩
  · subst finalContext
    subst outcome
    have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
      children childSize childStrict certified
        (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation child
    cases represented with
    | fault matched =>
      exact ⟨_, finalStore, finalMap, finalWorld, CellAwareOrdinaryContinuation.failure evaluated,
        .fault matched, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post.at_fault_type⟩
  · have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    obtain ⟨value, middleStore, middleMap, middleWorld, evaluated, represented, middleHeaps,
        maps, worlds, frame, metadata, effect, middleState, expressionRelated, post⟩ :=
      children childSize childStrict certified
        (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation child
    cases represented with
    | @value _ coreValue payload =>
      let middlePhysical := physical.transport effect frame
      obtain ⟨marker, agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
          preserved, allocationEffect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
        CellAwareInvocationOrdinaryPrefix.complete_at_source bridge mono member extended requestOrdinary allocation annotation same producer registered
          evaluated (valueType ▸ payload) (valueType ▸ post.at_value.1)
          (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
          middleState post.at_value.2 (authority.transport effect) middlePhysical
          (ready middleState middlePhysical.read) allocated type body
      have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
        intro index current stored
        have previous := ready current (by simpa only [locationEq, nativeEq, middlePhysical, CellAwareInvocationPhysical.Physical.transport_location, CellAwareInvocationPhysical.Physical.transport_native] using stored)
        simpa only [locationEq, nativeEq, middlePhysical, CellAwareInvocationPhysical.Physical.transport_location, CellAwareInvocationPhysical.Physical.transport_native] using previous
      obtain ⟨value, finalStore, finalMap, finalWorld, tailEvaluated, represented, finalHeaps,
          tailMaps, tailWorlds, finalFrame, finalMetadata, finalEffect, tailState, tailRelated, tailPost⟩ :=
        tail _ tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
          (runtime.transport (.ofBinderExtends extended))
          ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
          ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
          (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended)
          reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady remainingTrace
      let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := lowered.type)
        (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
      refine ⟨value, finalStore, finalMap, finalWorld, agreement.wrap tailEvaluated, represented, finalHeaps,
        maps.trans (allocationEffect.maps.trans tailMaps), worlds.trans (allocationEffect.worlds.trans tailWorlds),
        frame.trans (preserved.trans finalFrame), metadata.trans (allocationEffect.metadata.trans finalMetadata),
        effect.trans (allocationEffect.trans finalEffect), finalState,
        protocol.trans expressionRelated (protocol.trans related (protocol.trans tailRelated (bindings.restore_related
          (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
          (id := binder.id) (type := lowered.type)
          (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
      exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState tailPost

include allocationInputs reached read form mono extended allocation annotation same sourceEq registered bindings initializerFound valueType typed certified in
theorem reflects_at_source (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment)
      bridge context model index registry invocation certificate faults budget)
    (tail : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, lowered.type) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type (sequence type lowered.expression annotation.expression body) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
    completed
  have found := index.statement_read_reached reached read
  obtain ⟨member, _declaration, ordinary⟩ := SourceLetDeclarationFacts.of_lookup physical.ownership found form
  have requestOrdinary : allocationSource.inputs.any (fun input => decide (input.id = binder.id)) = false := by
    have ids := congrArg (fun inputs : List Resolved.LocalId => inputs.any (fun input => decide (input = binder.id))) allocationInputs
    simp only [List.any_map, Function.comp_def] at ids
    exact ids.trans ordinary
  have original := completed
  rw [TypedLexicalControl.sequence_rename] at original
  obtain ⟨childSize, middleStore, input, childSmaller, childEvaluation⟩ := original.bind_computation
  obtain ⟨childSourceSize, sourceOutcome, middle, middleMap, middleWorld, child, represented, middleHeaps,
      maps, worlds, frame, metadata, effect, middleState, expressionRelated, post⟩ :=
    children childSize (Nat.lt_of_lt_of_le childSmaller within) certified
      (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
      environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation childEvaluation
  cases represented with
  | fault matched =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound
      (CellAwareOrdinaryContinuation.failure childEvaluation.sound)
    exact ⟨Staging.Recursive.Size.stepSize [childSourceSize], context, _, middle, middleMap, middleWorld,
      .letFault (by simpa only [sourceEq] using lookupStatement?_sound found) form mono child,
      .fault matched, middleHeaps, maps, worlds, frame, metadata, effect, middleState, expressionRelated, post.at_fault_type⟩
  | @value sourceValue coreValue payload =>
    let location : Dynamic.Location := ⟨middle.cells.length⟩
    let bound : Dynamic.Heap := ⟨middle.cells ++ [⟨binder.scheme.body, some sourceValue, none⟩]⟩
    have allocated : Dynamic.Heap.Allocates middle binder.scheme.body (some sourceValue) location bound := .append
    let middlePhysical := physical.transport effect frame
    obtain ⟨marker, _agreement, smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
        preserved, allocationEffect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
      CellAwareInvocationOrdinaryPrefix.complete_at_source bridge mono member extended requestOrdinary allocation annotation same producer registered
        childEvaluation.sound (valueType ▸ payload) (valueType ▸ post.at_value.1)
        (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
        middleState post.at_value.2 (authority.transport effect) middlePhysical
        (ready middleState middlePhysical.read) allocated type body
    obtain ⟨tailSize, tailStrict, tailEvaluation⟩ := smaller completed
    have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
      intro index current stored
      have previous := ready current (by simpa only [locationEq, nativeEq, middlePhysical, CellAwareInvocationPhysical.Physical.transport_location, CellAwareInvocationPhysical.Physical.transport_native] using stored)
      simpa only [locationEq, nativeEq, middlePhysical, CellAwareInvocationPhysical.Physical.transport_location, CellAwareInvocationPhysical.Physical.transport_native] using previous
    obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        tailMaps, tailWorlds, finalFrame, finalMetadata, finalEffect, tailState, tailRelated, tailPost⟩ :=
      tail _ (Nat.le_trans (Nat.le_of_lt tailStrict) within) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
        (runtime.transport (.ofBinderExtends extended))
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
        (ProtectedStateImperativeStatementSuffixTyping.let_decl runtime.graph.nodeOccurrencesUnique sourceTyped found form extended)
        reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tailEvaluation
    let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := lowered.type)
      (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
    refine ⟨Staging.Recursive.Size.stepSize [childSourceSize, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
      .letInitialized (by simpa only [sourceEq] using lookupStatement?_sound found) form child mono
        (by simpa only [sourceEq] using extended) allocated trace,
      represented, finalHeaps, maps.trans (allocationEffect.maps.trans tailMaps), worlds.trans (allocationEffect.worlds.trans tailWorlds),
      frame.trans (preserved.trans finalFrame), metadata.trans (allocationEffect.metadata.trans finalMetadata),
      effect.trans (allocationEffect.trans finalEffect), finalState,
      protocol.trans expressionRelated (protocol.trans related (protocol.trans tailRelated (bindings.restore_related
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := lowered.type)
        (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
    exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState tailPost

end RequestSource

section Legacy

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions)
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  (index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame (GeneralizedLocalDescriptorHeap.cellModel model
      (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep)
  {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {mode : Bool} {id : StatementId} {node : StatementNode}
  {binder : TypedBinder} {initializer : ExpressionId} {rest : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {lowered : SourceCoreBasic.LoweredExpr} {body : Expr}
  {stored payload : Ty}
  (reached : index.Reached (.statement id))
  (read : index.policy.readStatement index.compilerSource id = .ok (node, stored))
  (form : node.form = .letDecl binder (some initializer))
  (mono : binder.scheme.quantified = [])
  (extended : BinderExtends index.source.owner context binder nextContext)
  (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts index.owner index.active
    (initializedRequest index.source scope binder lowered.type))
  (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
    whole.indexed.base.globals.length
    (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))
    (initializedRequest index.source scope binder lowered.type))
  (same : annotation.original = allocation.expression)
  (sourceEq : invocation.source = index.source)
  {initializerNode : ExpressionNode} {certificate : GenericExpressionMeaning.Certificate}
  (initializerFound : index.source.lookupExpression? initializer = some initializerNode)
  (valueType : initializerNode.type = binder.scheme.body)
  (typed : ExpressionHasType index.source context initializer initializerNode.type)
  (certified : certificate scope initializer lowered)

include reached read form mono extended allocation annotation same sourceEq registered bindings initializerFound valueType typed certified in
theorem preserves (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment)
      bridge context model index registry invocation certificate faults budget)
    (tail : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, lowered.type) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type (sequence type lowered.expression annotation.expression body) budget := by
  apply preserves_at_source (allocationSource := index.source) <;> first | assumption | rfl

include reached read form mono extended allocation annotation same sourceEq registered bindings initializerFound valueType typed certified in
theorem reflects (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment)
      bridge context model index registry invocation certificate faults budget)
    (tail : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, lowered.type) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type (sequence type lowered.expression annotation.expression body) budget := by
  apply reflects_at_source (allocationSource := index.source) <;> first | assumption | rfl


end Legacy

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationOrdinaryFlow
