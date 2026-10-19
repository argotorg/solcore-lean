import Solcore.SourceSemantics.CoreLowering.CellAwareForPostAssignment
import Solcore.SourceSemantics.CoreLowering.CellAwareForPostDiscard
import Solcore.SourceSemantics.CoreLowering.CellAwareForHeaderTree
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedAbsentPrefix
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedOrdinaryPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedForItemsTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedFlowOutcomes

/-! Post-header declarations, expression effects and actual ordinary writes
retain the mixed heap. Every branch restores the outer lexical observations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForPostTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open CallableIndexedOwnedAdmittedStagedForPostContracts (restoredOutcome)
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics namedCode)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) (GeneralizedLocalInstanceValues.model whole.indexed)))
  {faults : RecursiveStageMeaning.FaultRep}
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  (operandIncluded : ∀ reason token,
    GenericAssignmentDiagnostics.OperandRep compiled.own.assignments reason token → faults (.semantic reason) token)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}

private theorem member_of_root {source : TypedSource} {binder : TypedBinder}
    (declared : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder) :
    binder ∈ SourceCoreDataPlaces.declaredBinders source := by
  have member : binder ∈ (SourceCoreDataPlaces.declaredBinders source).filter
      (fun actual => decide (actual.id = binder.id)) := by
    rw [CompatibleMatchArmScopes.rootBinder_filter declared]
    exact List.mem_cons_self
  exact (List.mem_filter.mp member).1

private theorem rep_environment {mapping world expected type outcome value first second}
    (related : Represents (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
      mapping world false expected type faults (restoredOutcome first outcome) value) :
    Represents (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
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

include bindings transport extension registered operandIncluded in
theorem preserves {budget : Nat}
    (children : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      CellAwareScopeExpressionBounds.PreservesBelow bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named registry invocation
      (certificates context) faults budget)
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {context finishContext : SourceSemantics.Context}
    {scope finishScope : SourceCoreLocalCell.Scope} {items : List ForItemForm}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : CellAwareForHeaderTree.Tree whole.indexed named compiled certificates administrative type
      finishContext finishScope (LocalLoop.fallthrough type) context scope items code) :
    CellAwareScopeForPostBounds.PreservesAtMost bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope items expected type code budget := by
  induction tree with
  | @absent context nextContext scope binder rest body payload
      declaration mono extended ordinary projected allocation annotation same remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      finalContext outcome after trace
    have member := member_of_root declaration
    obtain ⟨tailSize, location, bound, sameSize, allocated, remainingTrace⟩ :=
      CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.absent
        (by simpa only [sourceEq] using extended) trace
    have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    obtain ⟨marker, agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
        preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
      CellAwareNamedAbsentPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
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
    refine ⟨value, finalStore, finalMap, finalWorld, agreement.wrap evaluated, rep_environment functions represented, finalHeaps,
      effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
      effect.metadata.trans metadata, effect.trans finalEffect, finalState,
      protocol.trans related (protocol.trans tailRelated (bindings.restore_related
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload)
        (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
    apply post_environment bridge (first := (binder.id, location) :: environment)
    exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post

  | @initialized context nextContext scope binder initializer initializerNode rest lowered body
      declaration mono extended ordinary initializerFound valueType typed certified allocation annotation same remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      finalContext outcome after trace
    have member := member_of_root declaration
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
          CellAwareNamedOrdinaryPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
            evaluated (valueType ▸ payload) (valueType ▸ post.at_value.1)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
            middleState post.at_value.2 (authority.transport effect) middlePhysical
            (ready middleState middlePhysical.read) allocated type body
        have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
          intro index current stored
          have previous := ready current (by simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using stored)
          simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using previous
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
        refine ⟨value, finalStore, finalMap, finalWorld, agreement.wrap tailEvaluated, rep_environment functions represented, finalHeaps,
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
  | nil =>
    intro size _within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      finalContext outcome after trace
    obtain ⟨rfl, rfl, rfl⟩ := CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.empty trace
    rw [LoopRenaming.fallthrough]
    exact ⟨_, store, mapping, world, LocalLoop.fallthrough_evaluates type actual store,
      .fallthrough environment (.inl rfl), heaps, .refl _, .refl _, .refl _ _, .refl _, .refl _ _ _ _,
      initial, protocol.refl initial, admitted⟩
  | @discard context scope expression node rest lowered body found typed certified remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    exact CellAwareForPostDiscard.preserves bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
      named producer registry invocation faults administrative scope expected type
      (by simpa only [sourceEq] using found) (by simpa only [sourceEq] using typed) certified
      budget (children context runtime covers sameLedger) ih size within
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready trace
  | @assign context scope assignment operator rhs rest body head bare _typed operands remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      have invalid : AssignmentOperandDiagnostics.OperandsLaw
          (fun reason token => faults (.semantic reason) token) operator head.invalid :=
        fun previous right different => operandIncluded _ _ (operands previous right different)
      exact CellAwareForPostAssignment.preserves bridge transport functions producer rfl runtime.graph.nodeOccurrencesUnique
        head bare extension invalid budget (children context runtime covers sameLedger) ih size within
        environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready trace

include bindings transport extension registered operandIncluded in
theorem reflects {budget : Nat}
    (children : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      CellAwareScopeExpressionBounds.ReflectsBelow bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named registry invocation
      (certificates context) faults budget)
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {context finishContext : SourceSemantics.Context}
    {scope finishScope : SourceCoreLocalCell.Scope} {items : List ForItemForm}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : CellAwareForHeaderTree.Tree whole.indexed named compiled certificates administrative type
      finishContext finishScope (LocalLoop.fallthrough type) context scope items code) :
    CellAwareScopeForPostBounds.ReflectsAtMost bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope items expected type code budget := by
  induction tree with
  | @absent context nextContext scope binder rest body payload
      declaration mono extended ordinary projected allocation annotation same remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      completed
    let location : Dynamic.Location := ⟨before.cells.length⟩
    let bound : Dynamic.Heap := ⟨before.cells ++ [⟨binder.scheme.body, none, none⟩]⟩
    have allocated : Dynamic.Heap.Allocates before binder.scheme.body none location bound := .append
    have member := member_of_root declaration
    obtain ⟨marker, _agreement, smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
        preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
      CellAwareNamedAbsentPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
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
      rep_environment functions represented, finalHeaps, effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
      effect.metadata.trans metadata, effect.trans finalEffect, finalState,
      protocol.trans related (protocol.trans tailRelated (bindings.restore_related
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload)
        (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
    apply post_environment bridge (first := (binder.id, location) :: environment)
    exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post

  | @initialized context nextContext scope binder initializer initializerNode rest lowered body
      declaration mono extended ordinary initializerFound valueType typed certified allocation annotation same remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      completed
    have member := member_of_root declaration
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
        CellAwareNamedOrdinaryPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
          childEvaluation.sound (valueType ▸ payload) (valueType ▸ post.at_value.1)
          (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
          middleState post.at_value.2 (authority.transport effect) middlePhysical
          (ready middleState middlePhysical.read) allocated type body
      obtain ⟨tailSize, tailStrict, tailEvaluation⟩ := smaller completed
      have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
        intro index current stored
        have previous := ready current (by simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using stored)
        simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using previous
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
        rep_environment functions represented, finalHeaps, maps.trans (allocationEffect.maps.trans tailMaps), worlds.trans (allocationEffect.worlds.trans tailWorlds),
        frame.trans (preserved.trans finalFrame), metadata.trans (allocationEffect.metadata.trans finalMetadata),
        effect.trans (allocationEffect.trans finalEffect), finalState,
        protocol.trans expressionRelated (protocol.trans related (protocol.trans tailRelated (bindings.restore_related
          (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
          (id := binder.id) (type := lowered.type)
          (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
      apply post_environment bridge (first := (binder.id, location) :: environment)
      exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState tailPost
  | nil =>
    intro size _within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready completed
    rw [LoopRenaming.fallthrough] at completed
    obtain ⟨rfl,rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.fallthrough_evaluates type actual store)
    exact ⟨1, _, _, before, mapping, world, .empty,
      .fallthrough environment (.inl rfl), heaps, .refl _, .refl _, .refl _ _, .refl _, .refl _ _ _ _,
      initial, protocol.refl initial, admitted⟩
  | @discard context scope expression node rest lowered body found typed certified remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    exact CellAwareForPostDiscard.reflects bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
      named producer registry invocation faults administrative scope expected type
      (by simpa only [sourceEq] using found) (by simpa only [sourceEq] using typed) certified
      budget (children context runtime covers sameLedger) ih size within
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
  | @assign context scope assignment operator rhs rest body head bare _typed operands remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      have invalid : AssignmentOperandDiagnostics.OperandsLaw
          (fun reason token => faults (.semantic reason) token) operator head.invalid :=
        fun previous right different => operandIncluded _ _ (operands previous right different)
      exact CellAwareForPostAssignment.reflects bridge transport functions producer rfl runtime.graph.nodeOccurrencesUnique
        head bare extension invalid budget (children context runtime covers sameLedger) ih size within
        environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready completed

end Solcore.SourceSemantics.CoreLowering.CellAwareForPostTreeBounds
