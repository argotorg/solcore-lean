import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationOrdinaryPrefix
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAbsentPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedForItemsTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedFlowOutcomes

/-! The existing absent and initialized header proofs use the same actual
invocation, mixed heap, and concrete allocation request source. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion
open CallableIndexedOwnedAdmittedStagedForPostContracts (restoredOutcome)
open TypedLexicalWhile (initializedRequest sequence)
open TypedLexicalControl (absentRequest)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions)
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  (index : ActualBodyInvocation.Index whole bodyRelation)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

include model in
private theorem rep_environment {mapping world expected type outcome value first second}
    (related : Represents model
      mapping world false expected type faults (restoredOutcome first outcome) value) :
    Represents model
      mapping world false expected type faults (restoredOutcome second outcome) value := by
  cases outcome with
  | done environment => cases related with | fallthrough _ allowed => exact .fallthrough _ allowed
  | fault failure => exact related

private theorem post_environment {context expected outcome first second index}
    {reached : protocol.State index}
    (post : Post bridge context expected (restoredOutcome first outcome) reached) :
    Post bridge context expected (restoredOutcome second outcome) reached := by
  cases outcome <;> exact post

private theorem absent_typed {source : TypedSource} {context nextContext : SourceSemantics.Context}
    {binder : TypedBinder} {rest : List ForItemForm}
    (typed : ∃ control final, ForItemsHaveType source control context (.letDecl binder none :: rest) final)
    (extended : BinderExtends source.owner context binder nextContext) :
    ∃ control final, ForItemsHaveType source control nextContext rest final := by
  obtain ⟨control, final, typed⟩ := typed
  exact ⟨control, CallableIndexedOwnedPreparedStagedForItemsTyping.absent ⟨final, typed⟩ extended⟩

private theorem initialized_typed {source : TypedSource} {context nextContext : SourceSemantics.Context}
    {binder : TypedBinder} {initializer : ExpressionId} {rest : List ForItemForm}
    (typed : ∃ control final, ForItemsHaveType source control context (.letDecl binder (some initializer) :: rest) final)
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext) :
    ∃ control final, ForItemsHaveType source control nextContext rest final := by
  obtain ⟨control, final, typed⟩ := typed
  exact ⟨control, CallableIndexedOwnedPreparedStagedForItemsTyping.initialized ⟨final, typed⟩ mono extended⟩


section Absent

variable {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {binder : TypedBinder} {rest : List ForItemForm} {body : Expr}
  {expected : TypeSystem.Ty} {type : Ty} {administrative : Core.Context}
  {allocationSource : TypedSource}
  {payload : Ty}
  (member : binder ∈ SourceCoreDataPlaces.declaredBinders index.source)
  (mono : binder.scheme.quantified = [])
  (extended : BinderExtends index.source.owner context binder nextContext)
  (ordinary : allocationSource.inputs.any (fun input => decide (input.id = binder.id)) = false)
  (projected : projects binder.scheme.body payload)
  (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts index.owner index.active
    (absentRequest allocationSource scope binder payload))
  (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
    whole.indexed.base.globals.length
    (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))
    (absentRequest allocationSource scope binder payload))
  (same : annotation.original = allocation.expression)
  (sourceEq : invocation.source = index.source)

include member mono extended ordinary projected allocation annotation same sourceEq registered bindings in
theorem absent_preserves {budget : Nat}
    (ih : CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults administrative
      ((binder.id, payload) :: scope) rest expected type body budget) :
    CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder none :: rest) expected type (.letE annotation.expression body) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
    finalContext outcome after trace
  obtain ⟨tailSize, location, bound, sameSize, allocated, remainingTrace⟩ :=
    CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.absent
      (by simpa only [sourceEq] using extended) trace
  have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
    rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
  obtain ⟨marker, agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
      preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
    CellAwareInvocationAbsentPrefix.complete_at_source bridge mono member extended ordinary allocation annotation same producer registered
      projected environments heaps locals agrees actualTyped initial admitted authority physical
      (ready initial physical.read) allocated body
  have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
    intro index current stored
    have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
    simpa only [locationEq, nativeEq] using previous
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, finalFrame, metadata, finalEffect, tailState, tailRelated, post⟩ :=
    ih _ tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
      (runtime.transport (.ofBinderExtends extended))
      ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
      ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
      (absent_typed sourceTyped extended)
      reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady remainingTrace
  let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (id := binder.id) (type := payload)
    (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
  refine ⟨value, finalStore, finalMap, finalWorld, agreement.wrap evaluated, rep_environment model represented, finalHeaps,
    effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
    effect.metadata.trans metadata, effect.trans finalEffect, finalState,
    protocol.trans related (protocol.trans tailRelated (bindings.restore_related
      (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := payload)
      (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
  apply post_environment bridge (first := (binder.id, location) :: environment)
  exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post


include member mono extended ordinary projected allocation annotation same sourceEq registered bindings in
theorem absent_reflects {budget : Nat}
    (ih : CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults administrative
      ((binder.id, payload) :: scope) rest expected type body budget) :
    CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder none :: rest) expected type (.letE annotation.expression body) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
    completed
  let location : Dynamic.Location := ⟨before.cells.length⟩
  let bound : Dynamic.Heap := ⟨before.cells ++ [⟨binder.scheme.body, none, none⟩]⟩
  have allocated : Dynamic.Heap.Allocates before binder.scheme.body none location bound := .append
  obtain ⟨marker, _agreement, smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
      preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
    CellAwareInvocationAbsentPrefix.complete_at_source bridge mono member extended ordinary allocation annotation same producer registered
      projected environments heaps locals agrees actualTyped initial admitted authority physical
      (ready initial physical.read) allocated body
  obtain ⟨tailSize, strict, tailCompleted⟩ := smaller completed
  have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
    intro index current stored
    have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
    simpa only [locationEq, nativeEq] using previous
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, finalFrame, metadata, finalEffect, tailState, tailRelated, post⟩ :=
    ih _ (Nat.le_trans (Nat.le_of_lt strict) within) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
      (runtime.transport (.ofBinderExtends extended))
      ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
      ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
      (absent_typed sourceTyped extended)
      reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tailCompleted
  let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (id := binder.id) (type := payload)
    (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
  refine ⟨Staging.Recursive.Size.stepSize [sourceSize], finalContext, outcome, after, finalMap, finalWorld,
    .absent mono (by simpa only [sourceEq] using extended) allocated trace,
    rep_environment model represented, finalHeaps, effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
    effect.metadata.trans metadata, effect.trans finalEffect, finalState,
    protocol.trans related (protocol.trans tailRelated (bindings.restore_related
      (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := payload)
      (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
  apply post_environment bridge (first := (binder.id, location) :: environment)
  exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post


end Absent

section Initialized

variable {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {binder : TypedBinder} {rest : List ForItemForm} {body : Expr}
  {expected : TypeSystem.Ty} {type : Ty} {administrative : Core.Context}
  {allocationSource : TypedSource}
  {initializer : ExpressionId} {initializerNode : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  (member : binder ∈ SourceCoreDataPlaces.declaredBinders index.source)
  (mono : binder.scheme.quantified = [])
  (extended : BinderExtends index.source.owner context binder nextContext)
  (ordinary : allocationSource.inputs.any (fun input => decide (input.id = binder.id)) = false)
  (initializerFound : index.source.lookupExpression? initializer = some initializerNode)
  (valueType : initializerNode.type = binder.scheme.body)
  (typed : ExpressionHasType index.source context initializer initializerNode.type)
  (certified : certificates context scope initializer lowered)
  (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts index.owner index.active
    (initializedRequest allocationSource scope binder lowered.type))
  (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
    whole.indexed.base.globals.length
    (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))
    (initializedRequest allocationSource scope binder lowered.type))
  (same : annotation.original = allocation.expression)
  (sourceEq : invocation.source = index.source)

include member mono extended ordinary initializerFound valueType typed certified allocation annotation same sourceEq registered bindings in
theorem initialized_preserves {budget : Nat}
    (children : ∀ context, Dynamic.SourceRuntimeValid program context index.source →
      invocation.evidence.Covers context → context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context model index registry invocation
        (certificates context) faults budget)
    (ih : CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults administrative
      ((binder.id, lowered.type) :: scope) rest expected type body budget) :
    CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder (some initializer) :: rest) expected type (sequence type lowered.expression annotation.expression body) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
    finalContext outcome after trace
  rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.initialized mono
      (by simpa only [sourceEq] using extended) trace with
    ⟨childSize, failure, sameSize, contextEq, outcomeEq, child⟩ |
    ⟨childSize, tailSize, sourceValue, location, middle, bound, sameSize, child, allocated, remainingTrace⟩
  · subst finalContext
    subst outcome
    have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
      children context runtime covers sameLedger childSize childStrict certified
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
      children context runtime covers sameLedger childSize childStrict certified
        (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation child
    cases represented with
    | @value _ coreValue payload =>
      let middlePhysical := physical.transport effect frame
      obtain ⟨marker, agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
          preserved, allocationEffect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
        CellAwareInvocationOrdinaryPrefix.complete_at_source bridge mono member extended ordinary allocation annotation same producer registered
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
        ih _ tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
          (runtime.transport (.ofBinderExtends extended))
          ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
          ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
          (initialized_typed sourceTyped mono extended)
          reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady remainingTrace
      let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := lowered.type)
        (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
      refine ⟨value, finalStore, finalMap, finalWorld, agreement.wrap tailEvaluated, rep_environment model represented, finalHeaps,
        maps.trans (allocationEffect.maps.trans tailMaps), worlds.trans (allocationEffect.worlds.trans tailWorlds),
        frame.trans (preserved.trans finalFrame), metadata.trans (allocationEffect.metadata.trans finalMetadata),
        effect.trans (allocationEffect.trans finalEffect), finalState,
        protocol.trans expressionRelated (protocol.trans related (protocol.trans tailRelated (bindings.restore_related
          (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
          (id := binder.id) (type := lowered.type)
          (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
      apply post_environment bridge (first := (binder.id, location) :: environment)
      exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState tailPost

include member mono extended ordinary initializerFound valueType typed certified allocation annotation same sourceEq registered bindings in
theorem initialized_reflects {budget : Nat}
    (children : ∀ context, Dynamic.SourceRuntimeValid program context index.source →
      invocation.evidence.Covers context → context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context model index registry invocation
        (certificates context) faults budget)
    (ih : CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults administrative
      ((binder.id, lowered.type) :: scope) rest expected type body budget) :
    CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder (some initializer) :: rest) expected type (sequence type lowered.expression annotation.expression body) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
    completed
  have original := completed
  rw [TypedLexicalControl.sequence_rename] at original
  obtain ⟨childSize, middleStore, input, childSmaller, childEvaluation⟩ := original.bind_computation
  obtain ⟨childSourceSize, sourceOutcome, middle, middleMap, middleWorld, child, represented, middleHeaps,
      maps, worlds, frame, metadata, effect, middleState, expressionRelated, post⟩ :=
    children context runtime covers sameLedger childSize (Nat.lt_of_lt_of_le childSmaller within) certified
      (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
      environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation childEvaluation
  cases represented with
  | fault matched =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound
      (CellAwareOrdinaryContinuation.failure childEvaluation.sound)
    exact ⟨Staging.Recursive.Size.stepSize [childSourceSize], context, _, middle, middleMap, middleWorld,
      .initializerFault mono child,
      .fault matched, middleHeaps, maps, worlds, frame, metadata, effect, middleState, expressionRelated, post.at_fault_type⟩
  | @value sourceValue coreValue payload =>
    let location : Dynamic.Location := ⟨middle.cells.length⟩
    let bound : Dynamic.Heap := ⟨middle.cells ++ [⟨binder.scheme.body, some sourceValue, none⟩]⟩
    have allocated : Dynamic.Heap.Allocates middle binder.scheme.body (some sourceValue) location bound := .append
    let middlePhysical := physical.transport effect frame
    obtain ⟨marker, _agreement, smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
        preserved, allocationEffect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
      CellAwareInvocationOrdinaryPrefix.complete_at_source bridge mono member extended ordinary allocation annotation same producer registered
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
      ih _ (Nat.le_trans (Nat.le_of_lt tailStrict) within) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
        (runtime.transport (.ofBinderExtends extended))
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
        (initialized_typed sourceTyped mono extended)
        reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tailEvaluation
    let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := lowered.type)
      (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
    refine ⟨Staging.Recursive.Size.stepSize [childSourceSize, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
      .initialized mono (by simpa only [sourceEq] using extended) child allocated trace,
      rep_environment model represented, finalHeaps, maps.trans (allocationEffect.maps.trans tailMaps), worlds.trans (allocationEffect.worlds.trans tailWorlds),
      frame.trans (preserved.trans finalFrame), metadata.trans (allocationEffect.metadata.trans finalMetadata),
      effect.trans (allocationEffect.trans finalEffect), finalState,
      protocol.trans expressionRelated (protocol.trans related (protocol.trans tailRelated (bindings.restore_related
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := lowered.type)
        (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
    apply post_environment bridge (first := (binder.id, location) :: environment)
    exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState tailPost

end Initialized

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostAllocation
