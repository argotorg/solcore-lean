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
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAbsentFlow
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
  (form : node.form = .letDecl binder none)
  (mono : binder.scheme.quantified = [])
  (extended : BinderExtends index.source.owner context binder nextContext)
  {allocationSource : TypedSource}
  (allocationInputs : allocationSource.inputs.map (·.id) = index.source.inputs.map (·.id))
  (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts index.owner index.active
    (absentRequest allocationSource scope binder payload))
  (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
    whole.indexed.base.globals.length
    (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))
    (absentRequest allocationSource scope binder payload))
  (same : annotation.original = allocation.expression)
  (sourceEq : invocation.source = index.source)
  (projected : projects binder.scheme.body payload)

include allocationInputs reached read form mono extended allocation annotation same sourceEq registered bindings projected in
theorem preserves_at_source (budget : Nat)
    (tail : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, payload) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type (Expr.letE annotation.expression body) budget := by
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
  obtain ⟨tailSize, location, bound, sameSize, allocated, remainingTrace⟩ :=
    CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.absent
      (by simpa only [sourceEq] using unique) (by simpa only [sourceEq] using found) form
      (by simpa only [sourceEq] using extended) trace
  have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
    rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
  obtain ⟨marker, agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
      preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
    CellAwareInvocationAbsentPrefix.complete_at_source bridge mono member extended requestOrdinary allocation annotation same producer registered
      projected environments heaps locals agrees actualTyped initial admitted authority physical
      (ready initial physical.read) allocated body
  have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
    intro index current stored
    have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
    simpa only [locationEq, nativeEq] using previous
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, finalFrame, metadata, finalEffect, tailState, tailRelated, post⟩ :=
    tail _ tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
      (runtime.transport (.ofBinderExtends extended))
      ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
      ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
      (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended)
      reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady remainingTrace
  let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (id := binder.id) (type := payload)
    (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
  refine ⟨value, finalStore, finalMap, finalWorld, agreement.wrap evaluated, represented, finalHeaps,
    effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
    effect.metadata.trans metadata, effect.trans finalEffect, finalState,
    protocol.trans related (protocol.trans tailRelated (bindings.restore_related
      (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := payload)
      (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
  exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post

include allocationInputs reached read form mono extended allocation annotation same sourceEq registered bindings projected in
theorem reflects_at_source (budget : Nat)
    (tail : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, payload) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type (Expr.letE annotation.expression body) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
    completed
  have found := index.statement_read_reached reached read
  obtain ⟨member, _declaration, ordinary⟩ := SourceLetDeclarationFacts.of_lookup physical.ownership found form
  have requestOrdinary : allocationSource.inputs.any (fun input => decide (input.id = binder.id)) = false := by
    have ids := congrArg (fun inputs : List Resolved.LocalId => inputs.any (fun input => decide (input = binder.id))) allocationInputs
    simp only [List.any_map, Function.comp_def] at ids
    exact ids.trans ordinary
  let location : Dynamic.Location := ⟨before.cells.length⟩
  let bound : Dynamic.Heap := ⟨before.cells ++ [⟨binder.scheme.body, none, none⟩]⟩
  have allocated : Dynamic.Heap.Allocates before binder.scheme.body none location bound := .append
  have unique := runtime.graph.nodeOccurrencesUnique
  obtain ⟨marker, _agreement, smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
      preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
    CellAwareInvocationAbsentPrefix.complete_at_source bridge mono member extended requestOrdinary allocation annotation same producer registered
      projected environments heaps locals agrees actualTyped initial admitted authority physical
      (ready initial physical.read) allocated body
  obtain ⟨tailSize, strict, tailCompleted⟩ := smaller completed
  have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
    intro index current stored
    have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
    simpa only [locationEq, nativeEq] using previous
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, finalFrame, metadata, finalEffect, tailState, tailRelated, post⟩ :=
    tail _ (Nat.le_trans (Nat.le_of_lt strict) within) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
      (runtime.transport (.ofBinderExtends extended))
      ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
      ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
      (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended)
      reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tailCompleted
  let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (id := binder.id) (type := payload)
    (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
  refine ⟨Staging.Recursive.Size.stepSize [sourceSize], finalContext, outcome, after, finalMap, finalWorld,
    .letUninitialized (by simpa only [sourceEq] using lookupStatement?_sound found) form
      mono (by simpa only [sourceEq] using extended) allocated trace,
    represented, finalHeaps, effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
    effect.metadata.trans metadata, effect.trans finalEffect, finalState,
    protocol.trans related (protocol.trans tailRelated (bindings.restore_related
      (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := payload)
      (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
  exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post

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
  (form : node.form = .letDecl binder none)
  (mono : binder.scheme.quantified = [])
  (extended : BinderExtends index.source.owner context binder nextContext)
  (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts index.owner index.active
    (absentRequest index.source scope binder payload))
  (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
    whole.indexed.base.globals.length
    (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))
    (absentRequest index.source scope binder payload))
  (same : annotation.original = allocation.expression)
  (sourceEq : invocation.source = index.source)
  (projected : projects binder.scheme.body payload)

include reached read form mono extended allocation annotation same sourceEq registered bindings projected in
theorem preserves (budget : Nat)
    (tail : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, payload) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type (Expr.letE annotation.expression body) budget := by
  apply preserves_at_source (allocationSource := index.source) <;> first | assumption | rfl

include reached read form mono extended allocation annotation same sourceEq registered bindings projected in
theorem reflects (budget : Nat)
    (tail : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, payload) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type (Expr.letE annotation.expression body) budget := by
  apply reflects_at_source (allocationSource := index.source) <;> first | assumption | rfl


end Legacy

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAbsentFlow
