import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationExpressions
import Solcore.SourceSemantics.CoreLowering.CellAllocationReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedFlowOutcomes
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeTypedSourceSites
import Solcore.SourceSemantics.CoreLowering.SourceLetDeclarationFacts
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationReachedReads
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationPhysical
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationAllocationReceipt
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalStatements
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationReads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion
import Solcore.SourceSemantics.CoreLowering.LoopRenaming
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedTerminalSourceBodyInversion
import Solcore.SourceSemantics.Staging.RecursiveControlViews
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedDiscardSourceBodyInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBlockSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedConditionalHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedConditionalSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFooter
import Solcore.SourceSemantics.Staging.RecursiveTypedControlBoundary
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.StagedProjected
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationSnapshotReceipt

/-!
# Cell-aware invocations: statement flows

Statement flows of one actual body invocation: terminals, transfers, discards, blocks, conditionals, declarations and the body finish.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationFlowBounds
/-! Common mixed-cell flow bounds retain ordinary control outcomes and exact
generalized descriptor effects. Scoped and function bodies differ only in their
mode; actual compiler trees close these internal recursive contracts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationFlowBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyRelation : ActualBodyInvocation.BodyRelation} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  (index : ActualBodyInvocation.Index compiled bodyRelation)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope) (mode : Bool) (statements : List StatementId)
  (expected : TypeSystem.Ty) (type : Ty) (code : Expr)

/-- Source and native grades remain independent. Every reached branch keeps
its exact mixed heap and restores the caller's lexical observations. -/
def PreservesAt (size : Nat) : Prop :=
  ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical compiled.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context index.source →
    invocation.evidence.Covers context →
    context.solvedRequirements = index.compilation.solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements index.source context statements →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
      Admission bridge context initial →
      CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        index.owner index.active mapping world before store environment →
    ∀ physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled index context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
      owner.key.frameLocation = physical.location →
      ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {finalContext outcome after},
      Staging.Recursive.Size.StatementsIn program registry mode size invocation context environment before
        statements finalContext outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename embedding) value finalStore ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ Post bridge context expected outcome reached

/-- Actual native completion reconstructs the chosen Source branch and its
real allocations, failures and control transfers. -/
def ReflectsAt (size : Nat) : Prop :=
  ∀ {mapping world actualContext environment canonical actual before store embedding value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical compiled.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context index.source →
    invocation.evidence.Covers context →
    context.solvedRequirements = index.compilation.solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements index.source context statements →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
      Admission bridge context initial →
      CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        index.owner index.active mapping world before store environment →
    ∀ physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled index context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
      owner.key.frameLocation = physical.location →
      ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    EvaluationSize size actual store (code.rename embedding) value finalStore →
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program registry mode sourceSize invocation context environment before
        statements finalContext outcome after ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ Post bridge context expected outcome reached

def PreservesAtMost (budget : Nat) : Prop :=
  ∀ size, size ≤ budget → PreservesAt (attachment := attachment) bridge context model index producer registry invocation faults administrative scope mode statements expected type code size

def PreservesBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → PreservesAt (attachment := attachment) bridge context model index producer registry invocation faults administrative scope mode statements expected type code size

def ReflectsAtMost (budget : Nat) : Prop :=
  ∀ size, size ≤ budget → ReflectsAt (attachment := attachment) bridge context model index producer registry invocation faults administrative scope mode statements expected type code size

def ReflectsBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → ReflectsAt (attachment := attachment) bridge context model index producer registry invocation faults administrative scope mode statements expected type code size

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationFlowBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAbsentFlow
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAbsentAcceptedAllocation
/-! The actual compiler allocation callback supplies its exact receipts.
The common flow proof keeps compiler request Source and runtime Source distinct. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAbsentAcceptedAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open TypedLexicalControl (absentRequest)
open TypedLexicalWhile (initializedRequest sequence)
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
  {code : Expr}
  (allocated : SourceCoreSourceCells.letUninitialized index.policy.sourceCells index.compilerSource scope Renaming.id
    binder payload body = .ok code)
  (sourceEq : invocation.source = index.source)
  (projected : projects binder.scheme.body payload)

include reached read form mono extended allocated sourceEq registered bindings projected in
theorem preserves (budget : Nat)
    (tail : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, payload) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type code budget := by
  obtain ⟨allocation, annotation, same, emitted⟩ := index.let_uninitialized_receipt allocated
  rw [emitted]
  apply CellAwareInvocationAbsentFlow.preserves_at_source
    (allocation := allocation) (annotation := annotation) (allocationInputs := index.compiler_inputs) <;> assumption

include reached read form mono extended allocated sourceEq registered bindings projected in
theorem reflects (budget : Nat)
    (tail : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, payload) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type code budget := by
  obtain ⟨allocation, annotation, same, emitted⟩ := index.let_uninitialized_receipt allocated
  rw [emitted]
  apply CellAwareInvocationAbsentFlow.reflects_at_source
    (allocation := allocation) (annotation := annotation) (allocationInputs := index.compiler_inputs) <;> assumption


end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAbsentAcceptedAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTerminalStatements
/-! Return and tail-expression execution at an actual named or contextual body.
The same stored descriptors, captured frame and heap survive either outcome. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTerminalStatements
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head control ResultRepresents)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyRelation : ActualBodyInvocation.BodyRelation} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

section Terminal
variable {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId}
  {statements : List StatementId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  (head : Head invocation expression statements)
  (certified : certificate scope expression lowered)
  (found : invocation.source.lookupExpression? expression = some node)
  (sourceTyped : ExpressionHasType invocation.source context expression node.type)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) index.owner index.active mapping world before store environment)
  (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled index context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (sameLocation : owner.key.frameLocation = physical.location)

include head certified found sourceTyped environments heaps locals agrees typed admitted authority physical sameLocation in
/-- The real parent step gives a strict expression grade. The expression IH
runs once and the existing return helper preserves its exact endpoint. -/
theorem preserves (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment)
      bridge context model index registry invocation certificate faults budget)
    {childSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment
      before expression outcome after)
    (within : Staging.Recursive.Size.stepSize [childSize] ≤ budget) :
    Staging.Recursive.Size.Statements program registry (Staging.Recursive.Size.stepSize [childSize])
      invocation context environment before statements context (control outcome) after ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.returnValue lowered.type lowered.expression).rename ξ) value finalStore ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  have strict : childSize < budget :=
    Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (child := childSize)
      (children := [childSize]) (by simp)) within
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    children childSize strict certified found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner sameLocation child
  refine ⟨head.trace child, ?_⟩
  cases represented with
  | value payload =>
    exact ⟨_, finalStore, finalMap, finalWorld,
      by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_success _ evaluated,
      .returned payload, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩
  | fault matched =>
    exact ⟨_, finalStore, finalMap, finalWorld,
      by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_failure _ evaluated,
      .fault matched, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩

include head certified found sourceTyped environments heaps locals agrees typed admitted authority physical sameLocation in
/-- Native inversion uses the original sum bind and its strict child grade.
The Source result and parent grade are reconstructed from that one child IH. -/
theorem reflects (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment)
      bridge context model index registry invocation certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((LocalLoop.returnValue lowered.type lowered.expression).rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program registry sourceSize invocation context environment
        before statements context (control outcome) after ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  have original := completed
  rw [LoopRenaming.returnValue] at original
  change EvaluationSize size actual store
    (LanguageResult.bind (LocalLoop.controlType lowered.type) (lowered.expression.rename ξ)
      (LocalLoop.returned (.var 0))) value finalStore at original
  cases CallableIndirectCallBounds.bind_completed original within with
  | failed child strict =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
      children _ strict certified found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner sameLocation child
    cases represented with
    | fault matched =>
      exact ⟨_, _, after, finalMap, finalWorld, head.trace trace, .fault matched,
        finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩
  | continued child remaining strict _remainingStrict =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
      children _ strict certified found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner sameLocation child
    cases represented with
    | value payload =>
      have expected := LocalLoop.returnValue_success lowered.type child.sound
      obtain ⟨same, stores⟩ := evaluation_deterministic original.sound expected
      cases same
      subst stores
      exact ⟨_, _, after, finalMap, finalWorld, head.trace trace, .returned payload,
        finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩
end Terminal

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTerminalStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTerminalFlows
/-! Actual terminal flow branches preserve both Source and native completion
at a named or contextual invocation. Expression semantics are the strict
recursive children, with the same stored descriptors and captured frame. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTerminalFlows
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head control)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyRelation : ActualBodyInvocation.BodyRelation} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {context : SourceSemantics.Context} {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId}
  {statements : List StatementId} {node : ExpressionNode} {expected : TypeSystem.Ty}
  {lowered : SourceCoreBasic.LoweredExpr}

theorem preserves {budget : Nat}
    (children : Dynamic.SourceRuntimeValid program context index.source →
      invocation.evidence.Covers context →
      context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context model index registry invocation
        certificate faults budget)
    (source : invocation.source = index.source)
    (head : Head invocation expression statements)
    (certified : certificate scope expression lowered)
    (found : invocation.source.lookupExpression? expression = some node)
    (typed : ExpressionHasType invocation.source context expression node.type)
    (valueType : node.type = expected) :
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope true statements expected lowered.type
      (LocalLoop.returnValue lowered.type lowered.expression) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers ledger _sourceTyped initial admitted authority physical
    owner sameLocation _ready finalContext outcome after trace
  obtain ⟨childSize, childOutcome, sameSize, _sameContext, sameOutcome, child⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.child_of_body
      (by simpa only [source] using runtime.graph.nodeOccurrencesUnique) head trace
  subst outcome
  obtain ⟨_trace, value, finalStore, finalMap, finalWorld, evaluated, represented,
      finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    CellAwareInvocationTerminalStatements.preserves bridge head certified found typed environments heaps locals
      agrees actualTyped initial admitted authority physical owner sameLocation budget (children runtime covers ledger)
      child (sameSize ▸ within)
  refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame,
    metadata, effect, reached, related, ?_⟩
  · cases represented with
    | returned payload => exact .returned (valueType ▸ payload)
    | fault matched => exact .fault matched
  · cases childOutcome <;> simpa only [Post, CallableIndexedOwnedAdmittedStagedTerminalStatements.control, ← valueType] using post

theorem reflects {budget : Nat}
    (children : Dynamic.SourceRuntimeValid program context index.source →
      invocation.evidence.Covers context →
      context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context model index registry invocation
        certificate faults budget)
    (head : Head invocation expression statements)
    (certified : certificate scope expression lowered)
    (found : invocation.source.lookupExpression? expression = some node)
    (typed : ExpressionHasType invocation.source context expression node.type)
    (valueType : node.type = expected) :
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope true statements expected lowered.type
      (LocalLoop.returnValue lowered.type lowered.expression) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers ledger _sourceTyped initial admitted authority physical
    owner sameLocation _ready completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
      frame, metadata, effect, reached, related, post⟩ :=
    CellAwareInvocationTerminalStatements.reflects bridge head certified found typed environments heaps locals agrees
      actualTyped initial admitted authority physical owner sameLocation budget (children runtime covers ledger)
      completed within
  refine ⟨sourceSize, context, CallableIndexedOwnedAdmittedStagedTerminalStatements.control outcome, after, finalMap, finalWorld, trace, ?_, finalHeaps, maps,
    worlds, frame, metadata, effect, reached, related, ?_⟩
  · cases represented with
    | returned payload => exact .returned (valueType ▸ payload)
    | fault matched => exact .fault matched
  · cases outcome <;> simpa only [Post, CallableIndexedOwnedAdmittedStagedTerminalStatements.control, ← valueType] using post

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTerminalFlows
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationEmptyFlow
/-! Empty scoped flow preserves the actual mixed heap and every descriptor.
Function fallthrough is admitted only at its real Unit result type. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationEmptyFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  (index : ActualBodyInvocation.Index compiled bodyRelation)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope) (mode : Bool)
  (expected : TypeSystem.Ty) (type : Ty)

theorem preserves (allowed : mode = false ∨ expected = .unit) (size : Nat) :
    CellAwareInvocationFlowBounds.PreservesAt (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode [] expected type (LocalLoop.fallthrough type) size := by
  intro mapping world actualContext environment canonical actual before store embedding
    _environments heaps _locals _agrees _actualTyped _runtime _covers _sameLedger _typed
    initial admitted _authority _physical _owner _sameLocation _ready finalContext outcome after trace
  cases trace
  exact ⟨_, store, mapping, world,
    by simpa only [LoopRenaming.fallthrough] using LocalLoop.fallthrough_evaluates type actual store,
    .fallthrough environment allowed, heaps, .refl _, .refl _, .refl _ _, .refl _,
    .refl _ _ _ _, initial, protocol.refl initial, admitted⟩

theorem reflects (allowed : mode = false ∨ expected = .unit) (size : Nat) :
    CellAwareInvocationFlowBounds.ReflectsAt (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode [] expected type (LocalLoop.fallthrough type) size := by
  intro mapping world actualContext environment canonical actual before store embedding value finalStore
    _environments heaps _locals _agrees _actualTyped _runtime _covers _sameLedger _typed
    initial admitted _authority _physical _owner _sameLocation _ready completed
  have expectedRun : Evaluates actual store ((LocalLoop.fallthrough type).rename embedding)
      (LocalLoop.fallthroughValue type) store := by
    simpa only [LoopRenaming.fallthrough] using LocalLoop.fallthrough_evaluates type actual store
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound expectedRun
  exact ⟨_, context, .fallthrough environment, before, mapping, world, .nil,
    .fallthrough environment allowed, heaps, .refl _, .refl _, .refl _ _, .refl _,
    .refl _ _ _ _, initial, protocol.refl initial, admitted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationEmptyFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationScopedTerminalFlow
/-! Actual terminal statement composition over the same mixed heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationScopedTerminalFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedScopedTerminalStatements (Head control ResultRepresents)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

section Terminal
variable {mode : Bool} {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId}
  {statements : List StatementId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  (head : Head invocation expression mode statements)
  (certified : certificate scope expression lowered)
  (found : invocation.source.lookupExpression? expression = some node)
  (sourceTyped : ExpressionHasType invocation.source context expression node.type)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) index.owner index.active mapping world before store environment)
  (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled index context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (sameLocation : owner.key.frameLocation = physical.location)

include head certified found sourceTyped environments heaps locals agrees typed admitted authority physical sameLocation in
/-- The real parent step gives a strict expression grade. The expression IH
runs once and the existing return helper preserves its exact endpoint. -/
private theorem preserves_child (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment)
      bridge context model index registry invocation certificate faults budget)
    {childSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment
      before expression outcome after)
    (within : Staging.Recursive.Size.stepSize [childSize] ≤ budget) :
    Staging.Recursive.Size.StatementsIn program registry mode (Staging.Recursive.Size.stepSize [childSize])
      invocation context environment before statements context (control outcome) after ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.returnValue lowered.type lowered.expression).rename ξ) value finalStore ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  have strict : childSize < budget :=
    Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (child := childSize)
      (children := [childSize]) (by simp)) within
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    children childSize strict certified found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner sameLocation child
  refine ⟨head.trace child, ?_⟩
  cases represented with
  | value payload =>
    exact ⟨_, finalStore, finalMap, finalWorld,
      by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_success _ evaluated,
      .returned payload, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩
  | fault matched =>
    exact ⟨_, finalStore, finalMap, finalWorld,
      by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_failure _ evaluated,
      .fault matched, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩

include head certified found sourceTyped environments heaps locals agrees typed admitted authority physical sameLocation in
/-- Native inversion uses the original sum bind and its strict child grade.
The Source result and parent grade are reconstructed from that one child IH. -/
private theorem reflects_child (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment)
      bridge context model index registry invocation certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((LocalLoop.returnValue lowered.type lowered.expression).rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program registry mode sourceSize invocation context environment
        before statements context (control outcome) after ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  have original := completed
  rw [LoopRenaming.returnValue] at original
  change EvaluationSize size actual store
    (LanguageResult.bind (LocalLoop.controlType lowered.type) (lowered.expression.rename ξ)
      (LocalLoop.returned (.var 0))) value finalStore at original
  cases CallableIndirectCallBounds.bind_completed original within with
  | failed child strict =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
      children _ strict certified found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner sameLocation child
    cases represented with
    | fault matched =>
      exact ⟨_, _, after, finalMap, finalWorld, head.trace trace, .fault matched,
        finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩
  | continued child remaining strict _remainingStrict =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
      children _ strict certified found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner sameLocation child
    cases represented with
    | value payload =>
      have expected := LocalLoop.returnValue_success lowered.type child.sound
      obtain ⟨same, stores⟩ := evaluation_deterministic original.sound expected
      cases same
      subst stores
      exact ⟨_, _, after, finalMap, finalWorld, head.trace trace, .returned payload,
        finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩
end Terminal

section Bounds
variable {mode : Bool} {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId}
  {statements : List StatementId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  {administrative : Core.Context}
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) callerProtocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))

theorem preserves
    (unique : NodeOccurrencesUnique invocation.source)
    (head : Head invocation expression mode statements)
    (found : invocation.source.lookupExpression? expression = some node)
    (sourceTyped : ExpressionHasType invocation.source context expression node.type)
    (certified : certificate scope expression lowered)
    (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context model index registry invocation certificate faults budget) :
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode statements node.type lowered.type
      (LocalLoop.returnValue lowered.type lowered.expression) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees typed _runtime _covers _ledger _sourceSites initial admitted authority physical owner sameLocation _ready
    finalContext bodyOutcome after trace
  obtain ⟨childSize,outcome,rfl,rfl,rfl,child⟩ :=
    CallableIndexedOwnedPreparedStagedScopedTerminalSourceBodyInversion.child_of_body unique head trace
  obtain ⟨_trace,value,finalStore,finalMap,finalWorld,evaluated,represented,finalHeaps,maps,worlds,
      frame,metadata,effect,reached,related,post⟩ :=
    preserves_child bridge head certified found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner sameLocation
      budget children child within
  cases represented with
  | returned payload => exact ⟨_,finalStore,finalMap,finalWorld,evaluated,.returned payload,
      finalHeaps,maps,worlds,frame,metadata,effect,reached,related,post⟩
  | fault matched => exact ⟨_,finalStore,finalMap,finalWorld,evaluated,.fault matched,
      finalHeaps,maps,worlds,frame,metadata,effect,reached,related,post⟩

theorem reflects
    (head : Head invocation expression mode statements)
    (found : invocation.source.lookupExpression? expression = some node)
    (sourceTyped : ExpressionHasType invocation.source context expression node.type)
    (certified : certificate scope expression lowered)
    (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context model index registry invocation certificate faults budget) :
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode statements node.type lowered.type
      (LocalLoop.returnValue lowered.type lowered.expression) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees typed _runtime _covers _ledger _sourceSites initial admitted authority physical owner sameLocation _ready completed
  obtain ⟨sourceSize,outcome,after,finalMap,finalWorld,trace,represented,finalHeaps,maps,worlds,
      frame,metadata,effect,reached,related,post⟩ :=
    reflects_child bridge head certified found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner sameLocation
      budget children completed within
  cases represented with
  | returned payload => exact ⟨sourceSize,context,_,after,finalMap,finalWorld,trace,.returned payload,
      finalHeaps,maps,worlds,frame,metadata,effect,reached,related,post⟩
  | fault matched => exact ⟨sourceSize,context,_,after,finalMap,finalWorld,trace,.fault matched,
      finalHeaps,maps,worlds,frame,metadata,effect,reached,related,post⟩
end Bounds

section Unit
variable {mode : Bool} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {id : StatementId} {node : StatementNode} {rest : List StatementId}
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) callerProtocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (unitValue : ∀ mapping world, model.Represents mapping world .unit .unit .unit .unit)
  (found : invocation.source.lookupStatement? id = some node)
  (form : node.form = .returnStmt none)

include unitValue found form in
theorem unit_preserves (unique : NodeOccurrencesUnique invocation.source) (size : Nat) :
    CellAwareInvocationFlowBounds.PreservesAt (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) .unit .unit (LocalLoop.returned .unit) size := by
  intro mapping world actualContext environment canonical actual before store embedding
    _environments heaps _locals _agrees _typed _runtime _covers _ledger _sourceSites initial admitted
    _authority _physical _owner _sameLocation _ready finalContext outcome after trace
  obtain ⟨rfl,rfl,rfl⟩ := CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.return_unit unique found form trace
  refine ⟨_,store,mapping,world,?_,.returned (unitValue mapping world),heaps,.refl _,.refl _,
    .refl _ _,.refl _,.refl _ _ _ _,initial,callerProtocol.refl initial,?_⟩
  · simpa only [LoopRenaming.returned, Expr.rename] using
      (LocalLoop.returned_evaluates (show Evaluates actual store .unit .unit store from .unit))
  · exact ⟨admitted.rows,by intro source same; cases same; exact ⟨.unit,admitted.heap⟩⟩

include unitValue found form in
theorem unit_reflects (size : Nat) :
    CellAwareInvocationFlowBounds.ReflectsAt (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) .unit .unit (LocalLoop.returned .unit) size := by
  intro mapping world actualContext environment canonical actual before store embedding value finalStore
    _environments heaps _locals _agrees _typed _runtime _covers _ledger _sourceSites initial admitted
    _authority _physical _owner _sameLocation _ready completed
  have evaluated : Evaluates actual store ((LocalLoop.returned .unit).rename embedding)
      (LocalLoop.returnedValue .unit) store := by
    simpa only [LoopRenaming.returned, Expr.rename] using
      (LocalLoop.returned_evaluates (show Evaluates actual store .unit .unit store from .unit))
  obtain ⟨rfl,rfl⟩ := evaluation_deterministic completed.sound evaluated
  refine ⟨_,context,.returned .unit,before,mapping,world,
    .returnUnit (lookupStatement?_sound found) form,.returned (unitValue mapping world),heaps,.refl _,.refl _,
    .refl _ _,.refl _,.refl _ _ _ _,initial,callerProtocol.refl initial,?_⟩
  exact ⟨admitted.rows,by intro source same; cases same; exact ⟨.unit,admitted.heap⟩⟩
end Unit

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationScopedTerminalFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTransferFlow
/-! Loop transfer leaves the actual mixed heap and all generalized descriptors intact.
The source occurrence authenticates the selected break or continue statement. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTransferFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  (index : ActualBodyInvocation.Index compiled bodyRelation)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope) (mode : Bool)
  (expected : TypeSystem.Ty) (type : Ty)


variable {id : StatementId} {node : StatementNode} {rest : List StatementId}

theorem breaking_preserves
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .breakStmt) (size : Nat) :
    CellAwareInvocationFlowBounds.PreservesAt (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type (LocalLoop.breaking type) size := by
  intro mapping world actualContext environment canonical actual before store embedding
    _environments heaps _locals _agrees _actualTyped _runtime _covers _sameLedger _typed
    initial admitted _authority _physical _owner _sameLocation _ready finalContext outcome after trace
  obtain ⟨rfl, rfl, rfl⟩ := Staging.Recursive.Size.StatementsIn.breaking_view unique found form trace
  exact ⟨_, store, mapping, world,
    LocalLoop.breaking_evaluates type actual store,
    .breaking environment, heaps, .refl _, .refl _, .refl _ _, .refl _,
    .refl _ _ _ _, initial, protocol.refl initial, admitted⟩

theorem breaking_reflects
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .breakStmt) (size : Nat) :
    CellAwareInvocationFlowBounds.ReflectsAt (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type (LocalLoop.breaking type) size := by
  intro mapping world actualContext environment canonical actual before store embedding value finalStore
    _environments heaps _locals _agrees _actualTyped _runtime _covers _sameLedger _typed
    initial admitted _authority _physical _owner _sameLocation _ready completed
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.breaking_evaluates type actual store)
  exact ⟨_, context, .breaking environment, before, mapping, world,
    .breaking (lookupStatement?_sound found) form,
    .breaking environment, heaps, .refl _, .refl _, .refl _ _, .refl _,
    .refl _ _ _ _, initial, protocol.refl initial, admitted⟩

variable {id : StatementId} {node : StatementNode} {rest : List StatementId}

theorem continuing_preserves
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .continueStmt) (size : Nat) :
    CellAwareInvocationFlowBounds.PreservesAt (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type (LocalLoop.continuing type) size := by
  intro mapping world actualContext environment canonical actual before store embedding
    _environments heaps _locals _agrees _actualTyped _runtime _covers _sameLedger _typed
    initial admitted _authority _physical _owner _sameLocation _ready finalContext outcome after trace
  obtain ⟨rfl, rfl, rfl⟩ := Staging.Recursive.Size.StatementsIn.continuing_view unique found form trace
  exact ⟨_, store, mapping, world,
    LocalLoop.continuing_evaluates type actual store,
    .continuing environment, heaps, .refl _, .refl _, .refl _ _, .refl _,
    .refl _ _ _ _, initial, protocol.refl initial, admitted⟩

theorem continuing_reflects
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .continueStmt) (size : Nat) :
    CellAwareInvocationFlowBounds.ReflectsAt (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type (LocalLoop.continuing type) size := by
  intro mapping world actualContext environment canonical actual before store embedding value finalStore
    _environments heaps _locals _agrees _actualTyped _runtime _covers _sameLedger _typed
    initial admitted _authority _physical _owner _sameLocation _ready completed
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.continuing_evaluates type actual store)
  exact ⟨_, context, .continuing environment, before, mapping, world,
    .continuing (lookupStatement?_sound found) form,
    .continuing environment, heaps, .refl _, .refl _, .refl _ _, .refl _,
    .refl _ _ _ _, initial, protocol.refl initial, admitted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTransferFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationDiscardFlow
/-! Discarded expressions execute once before their actual remaining flow.
Their concrete descriptor effects compose at the reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationDiscardFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  (index : ActualBodyInvocation.Index compiled bodyRelation)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope) (mode : Bool)
  (expected : TypeSystem.Ty) (type : Ty)


variable {id : StatementId} {node : StatementNode} {expression : ExpressionId}
  {expressionNode : ExpressionNode} {semicolon : Bool} {rest : List StatementId}
  {lowered : SourceCoreBasic.LoweredExpr} {body : Expr}
  {certificate : GenericExpressionMeaning.Certificate}
  (sourceEq : invocation.source = index.source)
  (unique : NodeOccurrencesUnique invocation.source)
  (found : invocation.source.lookupStatement? id = some node)
  (form : node.form = .expression expression semicolon)
  (continuing : semicolon = true ∨ mode = false)
  (expressionFound : invocation.source.lookupExpression? expression = some expressionNode)
  (typed : ExpressionHasType invocation.source context expression expressionNode.type)
  (certified : certificate scope expression lowered)

include sourceEq unique found form continuing expressionFound typed certified in
theorem preserves (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context model index registry invocation certificate faults budget)
    (tail : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationFlowBounds.PreservesAt (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type
      (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready finalContext outcome after trace
  have suffix := ProtectedStateImperativeStatementSuffixTyping.discard
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ found) form
  rw [LoopRenaming.discard]
  rcases CallableIndexedOwnedPreparedStagedScopedDiscardSourceBodyInversion.child_and_tail unique
      (lookupStatement?_sound found) form continuing trace with
    ⟨childSize, failure, sameSize, contextEq, outcomeEq, childTrace⟩ |
    ⟨childSize, tailSize, sourceValue, middle, sameSize, childTrace, remainingTrace⟩
  · subst finalContext
    subst outcome
    have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, post⟩ :=
      children childSize childStrict certified expressionFound typed environments heaps locals agrees actualTyped
        initial admitted authority physical owner sameLocation childTrace
    cases represented with
    | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LocalSequence.discard_failure _ evaluated,
        .fault matched, finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, post.at_fault_type⟩
  · have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    obtain ⟨value, middleStore, middleMap, middleWorld, first, represented,
        middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, expressionRelated, firstPost⟩ :=
      children childSize childStrict certified expressionFound typed environments heaps locals agrees actualTyped
        initial admitted authority physical owner sameLocation childTrace
    cases represented with
    | @value sourceValue coreValue payload =>
        obtain ⟨value, finalStore, finalMap, finalWorld, second, related,
            finalHeaps, maps, worlds, preservation, metadata, effect, reached, tailRelated, post⟩ :=
          tail tailSize tailWithin (environments.extend firstMaps firstWorlds)
            middleHeaps (locals.mono firstMetadata) (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
            runtime covers sameLedger suffix middleState firstPost.at_value.2 (authority.transport firstEffect)
            (physical.transport firstEffect firstFrame) owner sameLocation ready remainingTrace
        rw [GenericExpressionMeaning.rename_prefix] at second
        exact ⟨value, finalStore, finalMap, finalWorld, LocalSequence.discard_success _ first second,
          related, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans preservation,
          firstMetadata.trans metadata, firstEffect.trans effect, reached, protocol.trans expressionRelated tailRelated, post⟩

include sourceEq unique found form continuing expressionFound typed certified in
theorem reflects (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context model index registry invocation certificate faults budget)
    (tail : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationFlowBounds.ReflectsAt (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type
      (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready completed
  have suffix := ProtectedStateImperativeStatementSuffixTyping.discard
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ found) form
  rw [LoopRenaming.discard] at completed
  obtain ⟨childSize, middleStore, input, smaller, childEvaluation⟩ := completed.bind_computation
  obtain ⟨sourceSize, childOutcome, middle, middleMap, middleWorld, childTrace, represented,
      middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, expressionRelated, firstPost⟩ :=
    children childSize (Nat.lt_of_lt_of_le smaller within) certified expressionFound typed
      environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation childEvaluation
  cases represented with
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalSequence.discard_failure _ childEvaluation.sound)
      exact ⟨Staging.Recursive.Size.stepSize [sourceSize], context, _, middle, middleMap, middleWorld,
        .expressionFault (lookupStatement?_sound found) form childTrace, .fault matched, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, expressionRelated, firstPost.at_fault_type⟩
  | @value sourceValue coreValue payload =>
      obtain ⟨tailSize, tailSmaller, tailEvaluation⟩ := completed.bind_success childEvaluation.sound
      obtain ⟨tailSourceSize, finalContext, outcome, after, finalMap, finalWorld, tailTrace, related,
          finalHeaps, maps, worlds, preservation, metadata, effect, reached, tailRelated, post⟩ :=
        tail tailSize (Nat.le_trans (Nat.le_of_lt tailSmaller) within)
          (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
          (GenericExpressionMeaning.agree_prefix agrees coreValue)
          (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds)) runtime covers sameLedger suffix
          middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame)
          owner sameLocation ready (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEvaluation)
      have combined : Staging.Recursive.Size.StatementsIn program registry mode
          (Staging.Recursive.Size.stepSize [sourceSize, tailSourceSize]) invocation context environment before
          (id :: rest) finalContext outcome after := by
        cases semicolon with
        | true => exact .discard (lookupStatement?_sound found) form childTrace tailTrace
        | false =>
            have falseMode : mode = false := continuing.resolve_left (by decide)
            cases falseMode
            exact .discardValue (lookupStatement?_sound found) form childTrace tailTrace
      exact ⟨Staging.Recursive.Size.stepSize [sourceSize, tailSourceSize], finalContext, outcome, after, finalMap, finalWorld,
        combined, related, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
        firstFrame.trans preservation, firstMetadata.trans metadata, firstEffect.trans effect,
        reached, protocol.trans expressionRelated tailRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationDiscardFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationBlockFlow
/-! A scoped block restores its lexical observations while keeping the
actual mixed heap, every retained descriptor, and its original control outcome. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationBlockFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  (index : ActualBodyInvocation.Index compiled bodyRelation)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope) (mode : Bool)
  (expected : TypeSystem.Ty) (type : Ty)


variable {id : StatementId} {statement : StatementNode} {statements rest : List StatementId}
  {innerCode body : Expr}
  (sourceEq : invocation.source = index.source)
  (unique : NodeOccurrencesUnique invocation.source)
  (statementFound : invocation.source.lookupStatement? id = some statement)
  (form : statement.form = .block statements)

include sourceEq unique statementFound form in
theorem reflects (budget : Nat)
    (innerCorrect : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope false statements expected type innerCode budget)
    (remaining : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationFlowBounds.ReflectsAt (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type (LocalLoop.sequence type innerCode body) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready completed
  have innerTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.inner
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  rw [LoopRenaming.sequence] at completed
  obtain ⟨headSize, middleStore, headValue, headSmaller, headEval⟩ := completed.bind_computation
  obtain ⟨headSourceSize, innerContext, headOutcome, middle, middleMap, middleWorld, headTrace, represented,
      middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, headRelated, headPost⟩ :=
    innerCorrect _ (Nat.le_trans (Nat.le_of_lt headSmaller) within)
      environments heaps locals agrees actualTyped runtime covers sameLedger innerTyped
      initial admitted authority physical owner sameLocation ready headEval
  cases represented with
  | returned payload =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_returned _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .blockReturned (lookupStatement?_sound statementFound) form headTrace,
        .returned payload, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
        middleState, headRelated, headPost⟩
  | breaking innerEnvironment =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_transfer _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .blockBreaking (lookupStatement?_sound statementFound) form headTrace,
        .breaking environment, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
        middleState, headRelated, headPost⟩
  | continuing innerEnvironment =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_transfer _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .blockContinuing (lookupStatement?_sound statementFound) form headTrace,
        .continuing environment, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
        middleState, headRelated, headPost⟩
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_failure _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .blockFault (lookupStatement?_sound statementFound) form headTrace,
        .fault matched, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
        middleState, headRelated, headPost⟩
  | fallthrough innerEnvironment _ =>
      obtain ⟨tailSize, smaller, tailEval⟩ := completed.sequence_fallthrough headEval.sound
      obtain ⟨tailSourceSize, finalContext, outcome, after, finalMap, finalWorld, tailTrace, represented,
          finalHeaps, maps, worlds, framePreserved, metadata, effect, reached, tailRelated, post⟩ :=
        remaining _ (Nat.le_trans (Nat.le_of_lt smaller) within)
          (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
          (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
            (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
          (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken firstWorlds)))) runtime covers sameLedger suffixTyped
          middleState headPost (authority.transport firstEffect) (physical.transport firstEffect firstFrame)
          owner sameLocation ready
          (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEval)
      exact ⟨_, finalContext, outcome, after, finalMap, finalWorld,
        .blockFallthrough (lookupStatement?_sound statementFound) form headTrace tailTrace,
        represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
        firstFrame.trans framePreserved, firstMetadata.trans metadata, firstEffect.trans effect, reached,
        protocol.trans headRelated tailRelated, post⟩

include sourceEq unique statementFound form in
theorem preserves (budget : Nat)
    (innerCorrect : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope false statements expected type innerCode budget)
    (remaining : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationFlowBounds.PreservesAt (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type (LocalLoop.sequence type innerCode body) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready finalContext outcome after trace
  have innerTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.inner
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  have finish {headSize : Nat} {innerContext : SourceSemantics.Context}
      {headOutcome : Staging.Recursive.BodyOutcome}
      (headTrace : Staging.Recursive.Size.StatementsIn program registry false headSize invocation context
        environment before statements innerContext headOutcome after)
      (terminal : ∀ innerEnvironment, headOutcome ≠ .fallthrough innerEnvironment)
      (bounded : headSize ≤ budget) :
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((LocalLoop.sequence type innerCode body).rename embedding) value finalStore ∧
        Represents model finalMap finalWorld mode expected type faults (headOutcome.restore environment) value ∧
        GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
          protocol.Relates initial reached ∧ Post bridge context expected (headOutcome.restore environment) reached := by
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, preservation, metadata, effect, reached, related, post⟩ :=
      innerCorrect _ bounded environments heaps locals agrees actualTyped runtime covers sameLedger innerTyped
        initial admitted authority physical owner sameLocation ready headTrace
    cases represented with
    | returned payload =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .returned payload, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_returned _ evaluated
    | breaking innerEnvironment =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .breaking environment, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_transfer _ evaluated
    | continuing innerEnvironment =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .continuing environment, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_transfer _ evaluated
    | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_failure _ evaluated
    | fallthrough innerEnvironment _ => exact False.elim (terminal innerEnvironment rfl)
  rcases CallableIndexedOwnedPreparedStagedScopedBlockSourceInversion.block_and_tail unique statementFound form trace with
    ⟨innerSize, innerContext, sourceValue, sameSize, contextEq, outcomeEq, innerTrace⟩ |
    ⟨innerSize, innerContext, failure, sameSize, contextEq, outcomeEq, innerTrace⟩ |
    ⟨innerSize, innerContext, innerEnvironment, sameSize, contextEq, outcomeEq, innerTrace⟩ |
    ⟨innerSize, innerContext, innerEnvironment, sameSize, contextEq, outcomeEq, innerTrace⟩ |
    ⟨innerSize, tailSize, innerContext, innerEnvironment, middle, sameSize, innerTrace, tailTrace⟩
  · subst outcome
    exact finish innerTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (sameSize ▸ Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · subst outcome
    exact finish innerTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (sameSize ▸ Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · subst outcome
    exact finish innerTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (sameSize ▸ Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · subst outcome
    exact finish innerTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (sameSize ▸ Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · have headWithin : innerSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    obtain ⟨value, middleStore, middleMap, middleWorld, headEval, represented, middleHeaps,
        maps, worlds, preservation, metadata, firstEffect, middleState, headRelated, headPost⟩ :=
      innerCorrect _ headWithin environments heaps locals agrees actualTyped runtime covers sameLedger innerTyped
        initial admitted authority physical owner sameLocation ready innerTrace
    cases represented with
    | fallthrough innerEnvironment _ =>
        have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
        obtain ⟨value, finalStore, finalMap, finalWorld, tailEval, represented, finalHeaps,
            lastMaps, lastWorlds, lastFrame, lastMetadata, lastEffect, reached, tailRelated, post⟩ :=
          remaining _ tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
              (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
            (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken worlds)))) runtime covers sameLedger suffixTyped
            middleState headPost (authority.transport firstEffect) (physical.transport firstEffect preservation)
            owner sameLocation ready tailTrace
        refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame,
          metadata.trans lastMetadata, firstEffect.trans lastEffect, reached, protocol.trans headRelated tailRelated, post⟩
        rw [LoopRenaming.sequence]
        simp only [GenericExpressionMeaning.rename_prefix] at tailEval
        exact LocalLoop.sequence_fallthrough _ headEval tailEval

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationBlockFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationConditionalHead
/-! An actual Boolean condition chooses exactly one mixed scoped branch.
Both phases retain their concrete descriptor effects and reached admission. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationConditionalHead
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  (index : ActualBodyInvocation.Index compiled bodyRelation)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope)
  (expected : TypeSystem.Ty) (type : Ty)


open CallableIndexedOwnedAdmittedStagedConditionalHeads (Trace)
variable {test : ExpressionId} {node : ExpressionNode}
  {left : List StatementId} {right : Option (List StatementId)}
  {testCode leftCode rightCode : Expr} {certificate : GenericExpressionMeaning.Certificate}
  (booleans : ∀ {mapping world sourceValue nativeValue},
    model.Represents mapping world .bool sourceValue nativeValue .bool →
    ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
  (found : invocation.source.lookupExpression? test = some node)
  (nodeType : node.type = .bool)
  (typed : ExpressionHasType invocation.source context test node.type)
  (generated : certificate scope test ⟨.bool, testCode⟩)
  (leftTyped : ProtectedStateImperativeTypedSourceSites.Statements index.source context left)
  (rightTyped : ProtectedStateImperativeTypedSourceSites.Statements index.source context (right.getD []))

include booleans found nodeType typed generated leftTyped rightTyped in
theorem reflects (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context model index registry invocation certificate faults budget)
    (leftCorrect : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope false left expected type leftCode budget)
    (rightCorrect : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope false (right.getD []) expected type rightCode budget)
    {size : Nat} (within : size ≤ budget)
    {mapping world actualContext environment canonical actual before store embedding}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (runtime : Dynamic.SourceRuntimeValid program context index.source)
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = index.compilation.solvedRequirements)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
      index.owner index.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled index context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    {value finalStore}
    (completed : EvaluationSize size actual store ((LocalLoop.conditional type testCode leftCode rightCode).rename embedding) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Trace program registry invocation context environment before test left right sourceSize outcome after ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  rw [LoopRenaming.conditional] at completed
  obtain ⟨testSize, middleStore, input, smaller, testEval⟩ := completed.bind_computation
  obtain ⟨testSourceSize, testOutcome, middle, middleMap, middleWorld, testTrace, represented,
      middleHeaps, maps, worlds, preservation, metadata, firstEffect, middleState, expressionRelated, testPost⟩ :=
    children testSize (Nat.lt_of_lt_of_le smaller within) generated found typed
      environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation testEval
  cases represented with
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalControl.choose_failure _ testEval.sound)
      exact ⟨_, _, middle, middleMap, middleWorld, .fault testTrace, .fault matched, middleHeaps,
        maps, worlds, preservation, metadata, firstEffect, middleState, expressionRelated, testPost.at_fault_type⟩
  | value payload =>
      rw [nodeType] at payload
      obtain ⟨truth, sourceEq, coreEq⟩ := booleans payload
      subst sourceEq
      subst coreEq
      have selected : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer registry invocation faults
              administrative scope false (if truth then left else right.getD []) expected type
              (if truth then leftCode else rightCode) budget := by
        cases truth <;> assumption
      have branch : ∃ branchSize, branchSize < size ∧ EvaluationSize branchSize (.bool truth :: actual)
          middleStore (((if truth then leftCode else rightCode).rename embedding).weakenAt 0) value finalStore := by
        cases truth with
        | false => exact completed.choose_false testEval.sound
        | true => exact completed.choose_true testEval.sound
      obtain ⟨branchSize, branchSmaller, branchEval⟩ := branch
      obtain ⟨branchSourceSize, finalContext, outcome, after, finalMap, finalWorld, branchTrace,
          represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lastEffect, reached, branchRelated, post⟩ :=
        selected _ (Nat.le_trans (Nat.le_of_lt branchSmaller) within)
          (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (GenericExpressionMeaning.agree_prefix agrees (.bool truth))
          (.cons .bool (actualTyped.weaken worlds)) runtime covers sameLedger
          (by cases truth <;> assumption)
          middleState testPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect preservation)
          owner sameLocation ready
          (by simpa only [GenericExpressionMeaning.rename_prefix] using branchEval)
      exact ⟨_, outcome, after, finalMap, finalWorld, .branch testTrace branchTrace, represented, finalHeaps,
        maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata, firstEffect.trans lastEffect,
        reached, protocol.trans expressionRelated branchRelated, post⟩

include booleans found nodeType typed generated leftTyped rightTyped in
theorem preserves (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context model index registry invocation certificate faults budget)
    (leftCorrect : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope false left expected type leftCode budget)
    (rightCorrect : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope false (right.getD []) expected type rightCode budget)
    {size : Nat} (within : size ≤ budget)
    {mapping world actualContext environment canonical actual before store embedding}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (runtime : Dynamic.SourceRuntimeValid program context index.source)
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = index.compilation.solvedRequirements)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
      index.owner index.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled index context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    {outcome after}
    (trace : Trace program registry invocation context environment before test left right size outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.conditional type testCode leftCode rightCode).rename embedding) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  cases trace with
  | @fault testSize failure after testTrace =>
      have smaller : testSize < budget := Nat.lt_of_lt_of_le
        (Staging.Recursive.Size.child_lt_stepSize (by simp)) within
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩ :=
        children testSize smaller generated found typed environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation testTrace
      cases represented with
      | fault matched =>
          refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
            maps, worlds, preservation, metadata, effect, reached, related, post.at_fault_type⟩
          rw [LoopRenaming.conditional]
          exact LocalControl.choose_failure _ evaluated
  | @branch testSize branchSize truth middle innerContext outcome after testTrace branchTrace =>
      have smaller : testSize < budget := Nat.lt_of_lt_of_le
        (Staging.Recursive.Size.child_lt_stepSize (by simp)) within
      obtain ⟨value, middleStore, middleMap, middleWorld, testEval, represented, middleHeaps,
          maps, worlds, preservation, metadata, firstEffect, middleState, expressionRelated, testPost⟩ :=
        children testSize smaller generated found typed environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation testTrace
      cases represented with
      | value payload =>
          rw [nodeType] at payload
          obtain ⟨actualTruth, sourceEq, coreEq⟩ := booleans payload
          cases sourceEq
          subst coreEq
          have selected : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer registry invocation faults
              administrative scope false (if truth then left else right.getD []) expected type
              (if truth then leftCode else rightCode) budget := by
            cases truth <;> assumption
          have branchWithin : branchSize ≤ budget := Nat.le_trans
            (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within
          obtain ⟨value, finalStore, finalMap, finalWorld, branchEval, represented, finalHeaps,
              lastMaps, lastWorlds, lastFrame, lastMetadata, lastEffect, reached, branchRelated, post⟩ :=
            selected _ branchWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (GenericExpressionMeaning.agree_prefix agrees (.bool truth))
              (.cons .bool (actualTyped.weaken worlds)) runtime covers sameLedger
              (by cases truth <;> assumption)
              middleState testPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect preservation)
              owner sameLocation ready branchTrace
          refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
            maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata, firstEffect.trans lastEffect,
            reached, protocol.trans expressionRelated branchRelated, post⟩
          rw [LoopRenaming.conditional]
          rw [GenericExpressionMeaning.rename_prefix] at branchEval
          cases truth with
          | false => exact LocalControl.choose_false _ testEval branchEval
          | true => exact LocalControl.choose_true _ testEval branchEval

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationConditionalHead
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationConditionalFlow
/-! An actual Boolean condition chooses exactly one mixed scoped branch.
Both phases retain their concrete descriptor effects and reached admission. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationConditionalFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  (index : ActualBodyInvocation.Index compiled bodyRelation)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope)
  (expected : TypeSystem.Ty) (type : Ty)


open CallableIndexedOwnedAdmittedStagedConditionalHeads (Trace)
variable {test : ExpressionId} {node : ExpressionNode}
  {left : List StatementId} {right : Option (List StatementId)}
  {testCode leftCode rightCode : Expr} {certificate : GenericExpressionMeaning.Certificate}
  (booleans : ∀ {mapping world sourceValue nativeValue},
    model.Represents mapping world .bool sourceValue nativeValue .bool →
    ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
  (found : invocation.source.lookupExpression? test = some node)
  (nodeType : node.type = .bool)
  (typed : ExpressionHasType invocation.source context test node.type)
  (generated : certificate scope test ⟨.bool, testCode⟩)

  {mode : Bool} {id : StatementId} {statement : StatementNode} {rest : List StatementId} {body : Expr}
  (sourceEq : invocation.source = index.source)
  (unique : NodeOccurrencesUnique invocation.source)
  (statementFound : invocation.source.lookupStatement? id = some statement)
  (form : statement.form = .ifThen test left right)


include sourceEq unique statementFound form booleans found nodeType typed generated in
theorem reflects (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context model index registry invocation certificate faults budget)
    (leftCorrect : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope false left expected type leftCode budget)
    (rightCorrect : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope false (right.getD []) expected type rightCode budget)
    (remaining : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationFlowBounds.ReflectsAt (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type
      (LocalLoop.sequence type (LocalLoop.conditional type testCode leftCode rightCode) body) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready completed
  have leftTyped := ProtectedStateImperativeTypedSourceSites.branch_typed true (sourceEq ▸ unique)
    (ProtectedStateImperativeTypedSourceSites.head sourceTyped) (sourceEq ▸ statementFound) form
  have rightTyped := ProtectedStateImperativeTypedSourceSites.branch_typed false (sourceEq ▸ unique)
    (ProtectedStateImperativeTypedSourceSites.head sourceTyped) (sourceEq ▸ statementFound) form
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  rw [LoopRenaming.sequence] at completed
  obtain ⟨headSize, middleStore, headValue, headSmaller, headEval⟩ := completed.bind_computation
  obtain ⟨headSourceSize, headOutcome, middle, middleMap, middleWorld, headTrace, represented,
      middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, headRelated, headPost⟩ :=
    CellAwareInvocationConditionalHead.reflects bridge context model index producer registry invocation faults
      administrative scope expected type booleans found nodeType typed generated leftTyped rightTyped
      budget children leftCorrect rightCorrect (Nat.le_trans (Nat.le_of_lt headSmaller) within)
      environments heaps locals agrees actualTyped runtime covers sameLedger
      initial admitted authority physical owner sameLocation ready headEval
  cases represented with
  | returned payload =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_returned _ headEval.sound)
      cases headTrace with
      | branch testTrace branchTrace =>
          exact ⟨_, context, _, middle, middleMap, middleWorld,
            .ifReturned (lookupStatement?_sound statementFound) form testTrace branchTrace,
            .returned payload, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
            middleState, headRelated, headPost⟩
  | breaking innerEnvironment =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_transfer _ headEval.sound)
      cases headTrace with
      | branch testTrace branchTrace =>
          exact ⟨_, context, _, middle, middleMap, middleWorld,
            .ifBreaking (lookupStatement?_sound statementFound) form testTrace branchTrace,
            .breaking environment, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
            middleState, headRelated, headPost⟩
  | continuing innerEnvironment =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_transfer _ headEval.sound)
      cases headTrace with
      | branch testTrace branchTrace =>
          exact ⟨_, context, _, middle, middleMap, middleWorld,
            .ifContinuing (lookupStatement?_sound statementFound) form testTrace branchTrace,
            .continuing environment, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
            middleState, headRelated, headPost⟩
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_failure _ headEval.sound)
      cases headTrace with
      | fault testTrace =>
          exact ⟨_, context, _, middle, middleMap, middleWorld,
            .ifConditionFault (lookupStatement?_sound statementFound) form testTrace,
            .fault matched, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
            middleState, headRelated, headPost⟩
      | branch testTrace branchTrace =>
          exact ⟨_, context, _, middle, middleMap, middleWorld,
            .ifFault (lookupStatement?_sound statementFound) form testTrace branchTrace,
            .fault matched, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
            middleState, headRelated, headPost⟩
  | fallthrough innerEnvironment _ =>
      cases headTrace with
      | @branch testSize branchSize truth tested innerContext outcome after testTrace branchTrace =>
        obtain ⟨tailSize, smaller, tailEval⟩ := completed.sequence_fallthrough headEval.sound
        obtain ⟨tailSourceSize, finalContext, outcome, after, finalMap, finalWorld, tailTrace, represented,
            finalHeaps, maps, worlds, framePreserved, metadata, effect, reached, tailRelated, post⟩ :=
          remaining _ (Nat.le_trans (Nat.le_of_lt smaller) within)
            (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
              (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
            (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken firstWorlds)))) runtime covers sameLedger suffixTyped
            middleState headPost (authority.transport firstEffect) (physical.transport firstEffect firstFrame)
            owner sameLocation ready
            (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEval)
        exact ⟨_, finalContext, outcome, after, finalMap, finalWorld,
          .ifFallthrough (lookupStatement?_sound statementFound) form testTrace branchTrace tailTrace,
          represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
          firstFrame.trans framePreserved, firstMetadata.trans metadata, firstEffect.trans effect, reached,
          protocol.trans headRelated tailRelated, post⟩

include sourceEq unique statementFound form booleans found nodeType typed generated in
theorem preserves (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context model index registry invocation certificate faults budget)
    (leftCorrect : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope false left expected type leftCode budget)
    (rightCorrect : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope false (right.getD []) expected type rightCode budget)
    (remaining : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationFlowBounds.PreservesAt (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type
      (LocalLoop.sequence type (LocalLoop.conditional type testCode leftCode rightCode) body) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready finalContext outcome after trace
  have leftTyped := ProtectedStateImperativeTypedSourceSites.branch_typed true (sourceEq ▸ unique)
    (ProtectedStateImperativeTypedSourceSites.head sourceTyped) (sourceEq ▸ statementFound) form
  have rightTyped := ProtectedStateImperativeTypedSourceSites.branch_typed false (sourceEq ▸ unique)
    (ProtectedStateImperativeTypedSourceSites.head sourceTyped) (sourceEq ▸ statementFound) form
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  have finish {headSize : Nat} {headOutcome : Staging.Recursive.BodyOutcome}
      (headTrace : Trace program registry invocation context environment before test left right headSize headOutcome after)
      (terminal : ∀ innerEnvironment, headOutcome ≠ .fallthrough innerEnvironment)
      (bounded : headSize ≤ budget) :
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((LocalLoop.sequence type (LocalLoop.conditional type testCode leftCode rightCode) body).rename embedding) value finalStore ∧
        Represents model finalMap finalWorld mode expected type faults (headOutcome.restore environment) value ∧
        GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
          mapping world before store finalMap finalWorld after finalStore ∧
        ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
          protocol.Relates initial reached ∧ Post bridge context expected (headOutcome.restore environment) reached := by
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, preservation, metadata, effect, reached, related, post⟩ :=
      CellAwareInvocationConditionalHead.preserves bridge context model index producer registry invocation faults
        administrative scope expected type booleans found nodeType typed generated leftTyped rightTyped
        budget children leftCorrect rightCorrect bounded environments heaps locals agrees actualTyped runtime covers sameLedger
        initial admitted authority physical owner sameLocation ready headTrace
    cases represented with
    | returned payload =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .returned payload, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_returned _ evaluated
    | breaking innerEnvironment =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .breaking environment, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_transfer _ evaluated
    | continuing innerEnvironment =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .continuing environment, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_transfer _ evaluated
    | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_failure _ evaluated
    | fallthrough innerEnvironment _ => exact False.elim (terminal innerEnvironment rfl)
  rcases CallableIndexedOwnedPreparedStagedScopedConditionalSourceInversion.children unique statementFound form trace with
    ⟨testSize, failure, sameSize, contextEq, outcomeEq, testTrace⟩ |
    ⟨testSize, branchSize, truth, sourceValue, middle, innerContext, sameSize, contextEq, outcomeEq, testTrace, branchTrace⟩ |
    ⟨testSize, branchSize, truth, failure, middle, innerContext, sameSize, contextEq, outcomeEq, testTrace, branchTrace⟩ |
    ⟨testSize, branchSize, truth, innerEnvironment, middle, innerContext, sameSize, contextEq, outcomeEq, testTrace, branchTrace⟩ |
    ⟨testSize, branchSize, truth, innerEnvironment, middle, innerContext, sameSize, contextEq, outcomeEq, testTrace, branchTrace⟩ |
    ⟨testSize, branchSize, tailSize, truth, middle, branchHeap, innerContext, innerEnvironment, sameSize, testTrace, branchTrace, tailTrace⟩
  · subst outcome
    exact finish (.fault testTrace) (by intros; intro impossible; cases impossible) (sameSize ▸ within)
  · subst outcome
    exact finish (.branch testTrace branchTrace) (by intros; intro impossible; cases impossible) (sameSize ▸ within)
  · subst outcome
    exact finish (.branch testTrace branchTrace) (by intros; intro impossible; cases impossible) (sameSize ▸ within)
  · subst outcome
    exact finish (.branch testTrace branchTrace) (by intros; intro impossible; cases impossible) (sameSize ▸ within)
  · subst outcome
    exact finish (.branch testTrace branchTrace) (by intros; intro impossible; cases impossible) (sameSize ▸ within)
  · have headWithin : Staging.Recursive.Size.stepSize [testSize, branchSize] ≤ budget := by
      rw [sameSize] at within
      simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil] at within ⊢
      omega
    obtain ⟨value, middleStore, middleMap, middleWorld, headEval, represented, middleHeaps,
        maps, worlds, preservation, metadata, firstEffect, middleState, headRelated, headPost⟩ :=
      CellAwareInvocationConditionalHead.preserves bridge context model index producer registry invocation faults
        administrative scope expected type booleans found nodeType typed generated leftTyped rightTyped
        budget children leftCorrect rightCorrect headWithin environments heaps locals agrees actualTyped runtime covers sameLedger
        initial admitted authority physical owner sameLocation ready (.branch testTrace branchTrace)
    cases represented with
    | fallthrough innerEnvironment _ =>
        have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
        obtain ⟨value, finalStore, finalMap, finalWorld, tailEval, represented, finalHeaps,
            lastMaps, lastWorlds, lastFrame, lastMetadata, lastEffect, reached, tailRelated, post⟩ :=
          remaining _ tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
              (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
            (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken worlds)))) runtime covers sameLedger suffixTyped
            middleState headPost (authority.transport firstEffect) (physical.transport firstEffect preservation)
            owner sameLocation ready tailTrace
        refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame,
          metadata.trans lastMetadata, firstEffect.trans lastEffect, reached, protocol.trans headRelated tailRelated, post⟩
        rw [LoopRenaming.sequence]
        simp only [GenericExpressionMeaning.rename_prefix] at tailEval
        exact LocalLoop.sequence_fallthrough _ headEval tailEval

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationConditionalFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationOrdinaryFlow
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationOrdinaryAcceptedAllocation
/-! The actual compiler allocation callback supplies its exact receipts.
The common flow proof keeps compiler request Source and runtime Source distinct. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationOrdinaryAcceptedAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open TypedLexicalControl (absentRequest)
open TypedLexicalWhile (initializedRequest sequence)
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
  {code : Expr}
  (childType : SourceCoreBasic.ensureType (.binder binder.id) payload lowered.type = .ok ())
  (allocated : SourceCoreSourceCells.letInitialized index.policy.sourceCells index.compilerSource scope Renaming.id
    binder (LocalLoop.controlType type) payload lowered.expression body = .ok code)
  (sourceEq : invocation.source = index.source)
  {initializerNode : ExpressionNode} {certificate : GenericExpressionMeaning.Certificate}
  (initializerFound : index.source.lookupExpression? initializer = some initializerNode)
  (valueType : initializerNode.type = binder.scheme.body)
  (typed : ExpressionHasType index.source context initializer initializerNode.type)
  (certified : certificate scope initializer lowered)

include reached read form mono extended allocated childType sourceEq registered bindings initializerFound valueType typed certified in
theorem preserves (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment)
      bridge context model index registry invocation certificate faults budget)
    (tail : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, lowered.type) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type code budget := by
  have payloadEq : payload = lowered.type := by
    by_cases sameType : payload = lowered.type
    · exact sameType
    · simp [SourceCoreBasic.ensureType, sameType] at childType
  subst payload
  obtain ⟨allocation, annotation, same, emitted⟩ := index.let_initialized_receipt allocated
  rw [emitted]
  apply CellAwareInvocationOrdinaryFlow.preserves_at_source
    (allocation := allocation) (annotation := annotation) (allocationInputs := index.compiler_inputs) <;> assumption

include reached read form mono extended allocated childType sourceEq registered bindings initializerFound valueType typed certified in
theorem reflects (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment)
      bridge context model index registry invocation certificate faults budget)
    (tail : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, lowered.type) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type code budget := by
  have payloadEq : payload = lowered.type := by
    by_cases sameType : payload = lowered.type
    · exact sameType
    · simp [SourceCoreBasic.ensureType, sameType] at childType
  subst payload
  obtain ⟨allocation, annotation, same, emitted⟩ := index.let_initialized_receipt allocated
  rw [emitted]
  apply CellAwareInvocationOrdinaryFlow.reflects_at_source
    (allocation := allocation) (annotation := annotation) (allocationInputs := index.compiler_inputs) <;> assumption


end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationOrdinaryAcceptedAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationBodyFinish
/-! The genuine function footer consumes mixed imperative flow. Actual
zero-loop-depth Source typing excludes escaped control; the actual result
projection validates Unit fallthrough. All reached heap effects survive. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationBodyFinish
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {receiving : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed)}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {index : ActualBodyInvocation.Index whole bodyRelation}

local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions

variable
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
      (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {context : SourceSemantics.Context}
  {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
  {control : ControlContext} {staticFinal : SourceSemantics.Context} {facts : BodyFacts}

theorem preserves {budget : Nat}
    (bound : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope true statements expected type code budget)
    (sourceEq : invocation.source = index.source)
    (sourceTyped : StatementsHaveType (index.source) control context statements staticFinal facts)
    (depth : control.loopDepth = 0)
    (projection : whole.compatible.checked.catalog.project expected = .ok type)
    (fellThrough escaped : Word) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (index.source) →
    invocation.evidence.Covers context →
    context.solvedRequirements = index.compilation.solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (index.source) context statements →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
      index.owner index.active mapping world before store environment →
    ∀ physical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole index context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {finalContext outcome after},
    Staging.Recursive.Size.Statements program registry size invocation context environment before
      statements finalContext outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((CompatibleStatements.finish type code fellThrough escaped).rename embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected type faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context expected
          (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger typed initial admitted authority physical owner sameLocation ready
    finalContext outcome after trace
  obtain ⟨flowValue, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    bound size within environments heaps locals agrees actualTyped runtime covers sameLedger typed
      initial admitted authority physical owner sameLocation ready trace
  have closed := Staging.Recursive.TypedControlBoundary.function
    (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
    (by simpa only [sourceEq] using sourceTyped) depth trace.sound
  have functionValue := Represents.to_function projection represented closed
  obtain ⟨value, complete, result⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates functionValue evaluated fellThrough escaped embedding
  exact ⟨value, finalStore, finalMap, finalWorld,
    by rwa [CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename], result,
    finalHeaps, maps, worlds, frame, metadata, effect, reached, related,
    CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post⟩

theorem reflects {budget : Nat}
    (bound : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope true statements expected type code budget)
    (sourceEq : invocation.source = index.source)
    (sourceTyped : StatementsHaveType (index.source) control context statements staticFinal facts)
    (depth : control.loopDepth = 0)
    (projection : whole.compatible.checked.catalog.project expected = .ok type)
    (fellThrough escaped : Word) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (index.source) →
    invocation.evidence.Covers context →
    context.solvedRequirements = index.compilation.solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (index.source) context statements →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
      index.owner index.active mapping world before store environment →
    ∀ physical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole index context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {value finalStore}, EvaluationSize size actual store ((CompatibleStatements.finish type code fellThrough escaped).rename embedding) value finalStore →
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program registry sourceSize invocation context environment before
        statements finalContext outcome after ∧
      Staging.Recursive.BodyResult expected outcome (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected type faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context expected
          (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger typed initial admitted authority physical owner sameLocation ready
    value finalStore completed
  have original := completed
  rw [CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] at original
  obtain ⟨flowSize, flowValue, flowStore, flow, strict⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.flow_prefix original within
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    bound flowSize (Nat.le_of_lt strict) environments heaps locals agrees actualTyped runtime covers sameLedger typed
      initial admitted authority physical owner sameLocation ready flow
  have closed := Staging.Recursive.TypedControlBoundary.function
    (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
    (by simpa only [sourceEq] using sourceTyped) depth trace.sound
  have functionValue := Represents.to_function projection represented closed
  obtain ⟨native, complete, result⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates functionValue flow.sound fellThrough escaped embedding
  obtain ⟨same, stores⟩ := evaluation_deterministic original.sound complete
  cases same
  subst stores
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented.body_result,
    result, finalHeaps, maps, worlds, frame, metadata, effect, reached, related,
    CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationBodyFinish
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGeneralizedFlow
/-! The actual generalized allocation composes with its remaining statement
flow. The declaration first copies its scope; the principal captures the
copies and the continuation keeps the original cells. Both directions retain
the same descriptor attachment, physical frame and strict continuation grade.
Lambda shape observations used for reflection are explicit until supplied by
the actual initializer's source receipt. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGeneralizedFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open TypedLexicalWhile (initializedRequest)
open CellAwareGeneralizedSnapshotCode (snapshotInner snapshotSequence)
open SourceSemantics.CaptureBinders (copiedBinder?)

private theorem head_typed {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId}
    (typed : ProtectedStateImperativeTypedSourceSites.Statements source context (id :: rest)) :
    ∃ control final facts, StatementHasType source control context id final facts := by
  obtain ⟨control, final, facts, typed⟩ := typed
  cases typed with
  | singleton head => exact ⟨control, _, _, head⟩
  | cons head _ => exact ⟨control, _, _, head⟩


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
  (index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame (GeneralizedLocalDescriptorHeap.cellModel model
      (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep)
  {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {mode : Bool} {id : StatementId} {node : StatementNode}
  {binder : TypedBinder} {initializer : ExpressionId} {rest : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {lowered : SourceCoreBasic.LoweredExpr} {body : Expr}
  {childFuel : Nat} {reasonAt : ExpressionId → Word} {stored payload : Ty}
  {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
  (artifact : sourceCompiled.artifact? = some whole)
  (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
  (entry : index.ResidualEntry) (site : index.Site (.statement id))
  (read : index.policy.readStatement index.compilerSource id = .ok (node, stored))
  (form : node.form = .letDecl binder (some initializer))
  (projected : index.policy.lowerBinder index.compilerSource scope binder = .ok payload)
  (generated : index.policy.lowerExpression childFuel index.compilerSource scope initializer reasonAt = .ok lowered)
  (issuer : GeneralizedLocalDiagnosticIssuer.Receipt whole.indexed
    (index.initializerInputs childFuel scope initializer reasonAt))
  (declaration : (SourceCoreDataPlaces.declaredBinders index.source).filter
    (fun actual => decide (actual.id = binder.id)) = [binder])
  (polymorphic : binder.scheme.quantified ≠ [])
  (extended : BinderExtends index.source.owner context binder nextContext)
  {allocationSource : TypedSource}
  (ordinary : allocationSource.inputs.any (fun input => decide (input.id = binder.id)) = false)
  (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
    lowered.expression (LanguageResult.resultType lowered.type) whole.indexed.layouts.definitions)
  (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts index.owner index.active
    (initializedRequest allocationSource scope binder lowered.type))
  (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
    whole.indexed.base.globals.length
    (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))
    (initializedRequest allocationSource scope binder lowered.type))
  (same : annotation.original = allocation.expression)
  {captured : Expr}
  (copied : SourceCoreSourceCells.copyScope
    (some (SourceCoreCallableIndexedAllocationFrames.allocator whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))))
    allocationSource scope (fun index => index) (snapshotInner lowered.type lowered.expression annotation.expression) =
      .ok captured)
  (copiedIds : ∀ id, (copiedBinder? allocationSource id).isSome = (copiedBinder? index.source id).isSome)
  (sourceEq : invocation.source = index.source)


include artifact checked entry site read form projected generated issuer declaration polymorphic
  extended ordinary nativeTyped allocation annotation same copied copiedIds sourceEq registered bindings in
theorem preserves_at_source (budget : Nat)
    (tail : CellAwareInvocationFlowBounds.PreservesAtMost
      (attachment := GeneralizedLocalCapturedScopes.Attachment) bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, lowered.type) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.PreservesAtMost
      (attachment := GeneralizedLocalCapturedScopes.Attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type
      (snapshotSequence type captured body) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
    finalContext outcome after trace
  have unique := runtime.graph.nodeOccurrencesUnique
  have found := index.statement_read_reached site.reached read
  obtain ⟨tailSize, copies, snapshotHeap, function, location, bound, sameSize, snapshot, captures, allocated,
      remainingTrace⟩ :=
    CellAwareGeneralizedSourceInversion.generalized (by simpa only [sourceEq] using unique)
      (by simpa only [sourceEq] using found) form polymorphic
      (by simpa only [sourceEq] using extended) trace
  have snapshotIndexed : Dynamic.EnvironmentCopies index.source environment before copies snapshotHeap := by
    simpa only [sourceEq] using snapshot
  have capturesIndexed : Dynamic.GeneralizedClosureCaptures context index.source copies binder initializer function := by
    simpa only [sourceEq] using captures
  obtain ⟨control, next, facts, headTyped⟩ := head_typed sourceTyped
  have functionTyped := CellAwareGeneralizedSourceInversion.captured_wellTyped runtime (snapshotIndexed.agrees locals)
    headTyped found form polymorphic capturesIndexed
  have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
    rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
  obtain ⟨values, marker, copiedStore, copiedMap, copiedWorld, agreement, _smaller, nextEnvironments, nextHeaps,
      nextLocals, nextAgrees, nextTyped, preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical,
      locationEq, nativeEq⟩ :=
    CellAwareInvocationGeneralizedPrefix.complete_at_source bridge artifact checked entry unique site read form
      projected generated issuer declaration polymorphic extended ordinary nativeTyped allocation annotation same
      copied copiedIds producer bindings registered environments heaps locals agrees actualTyped initial admitted
      authority physical ready snapshotIndexed capturesIndexed functionTyped allocated type body
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
    (id := binder.id) (type := lowered.type)
    (value := .cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)) tailState
  refine ⟨value, finalStore, finalMap, finalWorld, agreement.wrap evaluated, represented, finalHeaps,
    effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
    effect.metadata.trans metadata, effect.trans finalEffect, finalState,
    protocol.trans related (protocol.trans tailRelated (bindings.restore_related
      (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := lowered.type)
      (value := .cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)) tailState)), ?_⟩
  exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2))
    tailState post

variable {initializerNode : ExpressionNode} {parameters : List TypedBinder}
  {result : TypeSystem.Ty} {lambdaBody : List StatementId}
  (initializerFound : index.source.lookupExpression? initializer = some initializerNode)
  (initializerForm : initializerNode.form = .lambda parameters result lambdaBody)
  (valueType : initializerNode.type = binder.scheme.body)
  (requirements : initializerNode.requirements = []) (coercions : initializerNode.coercions = [])

include artifact checked entry site read form projected generated issuer declaration polymorphic
  extended ordinary nativeTyped allocation annotation same copied copiedIds sourceEq registered bindings
  initializerFound initializerForm valueType requirements coercions in
theorem reflects_at_source (budget : Nat)
    (tail : CellAwareInvocationFlowBounds.ReflectsAtMost
      (attachment := GeneralizedLocalCapturedScopes.Attachment) bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, lowered.type) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.ReflectsAtMost
      (attachment := GeneralizedLocalCapturedScopes.Attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type
      (snapshotSequence type captured body) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
    completed
  obtain ⟨copies, snapshotHeap, snapshot⟩ := CellAwareGeneralizedSourceInversion.copies_exist index.source locals
  let function := Dynamic.GeneralizedClosure.ofDirectLambda context index.source copies binder initializer
    parameters result lambdaBody
  have captures : Dynamic.GeneralizedClosureCaptures context index.source copies binder initializer function :=
    .directLambda (lookupExpression?_sound initializerFound) initializerForm
      (by simpa only [ExpressionNode.rawType, coercions] using valueType) valueType requirements coercions
  let location : Dynamic.Location := ⟨snapshotHeap.cells.length⟩
  let bound : Dynamic.Heap := ⟨snapshotHeap.cells ++ [⟨function.binder.scheme.body, none, some function⟩]⟩
  have allocated : Dynamic.Heap.AllocatesGeneralized snapshotHeap function location bound := .append
  have unique := runtime.graph.nodeOccurrencesUnique
  have found := index.statement_read_reached site.reached read
  obtain ⟨control, next, facts, headTyped⟩ := head_typed sourceTyped
  have functionTyped := CellAwareGeneralizedSourceInversion.captured_wellTyped runtime (snapshot.agrees locals)
    headTyped found form polymorphic captures
  obtain ⟨values, marker, copiedStore, copiedMap, copiedWorld, _agreement, smaller, nextEnvironments, nextHeaps,
      nextLocals, nextAgrees, nextTyped, preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical,
      locationEq, nativeEq⟩ :=
    CellAwareInvocationGeneralizedPrefix.complete_at_source bridge artifact checked entry unique site read form
      projected generated issuer declaration polymorphic extended ordinary nativeTyped allocation annotation same
      copied copiedIds producer bindings registered environments heaps locals agrees actualTyped initial admitted
      authority physical ready snapshot captures functionTyped allocated type body
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
    (id := binder.id) (type := lowered.type)
    (value := .cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)) tailState
  refine ⟨Staging.Recursive.Size.stepSize [sourceSize], finalContext, outcome, after, finalMap, finalWorld,
    .letGeneralized (by simpa only [sourceEq] using lookupStatement?_sound found) form
      (by simpa only [sourceEq] using snapshot) (by simpa only [sourceEq] using captures) polymorphic
      (by simpa only [sourceEq] using extended) allocated trace,
    represented, finalHeaps, effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
    effect.metadata.trans metadata, effect.trans finalEffect, finalState,
    protocol.trans related (protocol.trans tailRelated (bindings.restore_related
      (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := lowered.type)
      (value := .cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)) tailState)), ?_⟩
  exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2))
    tailState post

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
  (index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame (GeneralizedLocalDescriptorHeap.cellModel model
      (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep)
  {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {mode : Bool} {id : StatementId} {node : StatementNode}
  {binder : TypedBinder} {initializer : ExpressionId} {rest : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {lowered : SourceCoreBasic.LoweredExpr} {body : Expr}
  {childFuel : Nat} {reasonAt : ExpressionId → Word} {stored payload : Ty}
  {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
  (artifact : sourceCompiled.artifact? = some whole)
  (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
  (entry : index.ResidualEntry) (site : index.Site (.statement id))
  (read : index.policy.readStatement index.compilerSource id = .ok (node, stored))
  (form : node.form = .letDecl binder (some initializer))
  (projected : index.policy.lowerBinder index.compilerSource scope binder = .ok payload)
  (generated : index.policy.lowerExpression childFuel index.compilerSource scope initializer reasonAt = .ok lowered)
  (issuer : GeneralizedLocalDiagnosticIssuer.Receipt whole.indexed
    (index.initializerInputs childFuel scope initializer reasonAt))
  (declaration : (SourceCoreDataPlaces.declaredBinders index.source).filter
    (fun actual => decide (actual.id = binder.id)) = [binder])
  (polymorphic : binder.scheme.quantified ≠ [])
  (extended : BinderExtends index.source.owner context binder nextContext)
  (ordinary : index.source.inputs.any (fun input => decide (input.id = binder.id)) = false)
  (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
    lowered.expression (LanguageResult.resultType lowered.type) whole.indexed.layouts.definitions)
  (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts index.owner index.active
    (initializedRequest index.source scope binder lowered.type))
  (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
    whole.indexed.base.globals.length
    (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))
    (initializedRequest index.source scope binder lowered.type))
  (same : annotation.original = allocation.expression)
  {captured : Expr}
  (copied : SourceCoreSourceCells.copyScope
    (some (SourceCoreCallableIndexedAllocationFrames.allocator whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))))
    index.source scope (fun index => index) (snapshotInner lowered.type lowered.expression annotation.expression) =
      .ok captured)
  (sourceEq : invocation.source = index.source)


include artifact checked entry site read form projected generated issuer declaration polymorphic
  extended ordinary nativeTyped allocation annotation same copied sourceEq registered bindings in
theorem preserves (budget : Nat)
    (tail : CellAwareInvocationFlowBounds.PreservesAtMost
      (attachment := GeneralizedLocalCapturedScopes.Attachment) bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, lowered.type) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.PreservesAtMost
      (attachment := GeneralizedLocalCapturedScopes.Attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type
      (snapshotSequence type captured body) budget := by
  apply preserves_at_source (allocationSource := index.source) (copiedIds := fun _ => rfl) <;>
    first | assumption | rfl

variable {initializerNode : ExpressionNode} {parameters : List TypedBinder}
  {result : TypeSystem.Ty} {lambdaBody : List StatementId}
  (initializerFound : index.source.lookupExpression? initializer = some initializerNode)
  (initializerForm : initializerNode.form = .lambda parameters result lambdaBody)
  (valueType : initializerNode.type = binder.scheme.body)
  (requirements : initializerNode.requirements = []) (coercions : initializerNode.coercions = [])

include artifact checked entry site read form projected generated issuer declaration polymorphic
  extended ordinary nativeTyped allocation annotation same copied sourceEq registered bindings
  initializerFound initializerForm valueType requirements coercions in
theorem reflects (budget : Nat)
    (tail : CellAwareInvocationFlowBounds.ReflectsAtMost
      (attachment := GeneralizedLocalCapturedScopes.Attachment) bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, lowered.type) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.ReflectsAtMost
      (attachment := GeneralizedLocalCapturedScopes.Attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type
      (snapshotSequence type captured body) budget := by
  apply reflects_at_source (allocationSource := index.source) (copiedIds := fun _ => rfl) <;>
    first | assumption | rfl


end Legacy

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGeneralizedFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGeneralizedAcceptedAllocation
/-! The actual compiler allocation callback supplies its exact receipts for the
scope copies and the marked descriptor allocation of a generalized
declaration. The common flow proof keeps compiler request Source and runtime
Source distinct; both copy the same identifiers. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGeneralizedAcceptedAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open SourceSemantics.CaptureBinders (copiedBinder?)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions)
  (index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame (GeneralizedLocalDescriptorHeap.cellModel model
      (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep)
  {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {mode : Bool} {id : StatementId} {node : StatementNode}
  {binder : TypedBinder} {initializer : ExpressionId} {rest : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {lowered : SourceCoreBasic.LoweredExpr} {body : Expr}
  {childFuel : Nat} {reasonAt : ExpressionId → Word} {stored payload : Ty}
  {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
  (artifact : sourceCompiled.artifact? = some whole)
  (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
  (entry : index.ResidualEntry) (site : index.Site (.statement id))
  (read : index.policy.readStatement index.compilerSource id = .ok (node, stored))
  (form : node.form = .letDecl binder (some initializer))
  (projected : index.policy.lowerBinder index.compilerSource scope binder = .ok payload)
  (generated : index.policy.lowerExpression childFuel index.compilerSource scope initializer reasonAt = .ok lowered)
  (issuer : GeneralizedLocalDiagnosticIssuer.Receipt whole.indexed
    (index.initializerInputs childFuel scope initializer reasonAt))
  (declaration : (SourceCoreDataPlaces.declaredBinders index.source).filter
    (fun actual => decide (actual.id = binder.id)) = [binder])
  (polymorphic : binder.scheme.quantified ≠ [])
  (extended : BinderExtends index.source.owner context binder nextContext)
  (ordinary : index.source.inputs.any (fun input => decide (input.id = binder.id)) = false)
  (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
    lowered.expression (LanguageResult.resultType lowered.type) whole.indexed.layouts.definitions)
  {code : Expr}
  (childType : SourceCoreBasic.ensureType (.binder binder.id) payload lowered.type = .ok ())
  (allocated : SourceCoreSourceCells.letInitializedSnapshot index.policy.sourceCells index.compilerSource scope
    binder (LocalLoop.controlType type) payload lowered.expression body = .ok code)
  (sourceEq : invocation.source = index.source)


include artifact checked entry site read form projected generated issuer declaration polymorphic
  extended ordinary nativeTyped allocated childType sourceEq registered bindings in
theorem preserves (budget : Nat)
    (tail : CellAwareInvocationFlowBounds.PreservesAtMost
      (attachment := GeneralizedLocalCapturedScopes.Attachment) bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, lowered.type) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.PreservesAtMost
      (attachment := GeneralizedLocalCapturedScopes.Attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type
      code budget := by
  have payloadEq : payload = lowered.type := by
    by_cases sameType : payload = lowered.type
    · exact sameType
    · simp [SourceCoreBasic.ensureType, sameType] at childType
  subst payload
  obtain ⟨allocation, annotation, same, captured, copied, emitted⟩ := index.let_initialized_snapshot_receipt allocated
  rw [emitted]
  have compilerOrdinary := index.compiler_noninput ordinary
  have copiedIds : ∀ id, (copiedBinder? index.compilerSource id).isSome = (copiedBinder? index.source id).isSome :=
    fun id => (index.copied_ids id).symm
  apply CellAwareInvocationGeneralizedFlow.preserves_at_source
    (allocation := allocation) (annotation := annotation) (copied := copied) <;> assumption

variable {initializerNode : ExpressionNode} {parameters : List TypedBinder}
  {result : TypeSystem.Ty} {lambdaBody : List StatementId}
  (initializerFound : index.source.lookupExpression? initializer = some initializerNode)
  (initializerForm : initializerNode.form = .lambda parameters result lambdaBody)
  (valueType : initializerNode.type = binder.scheme.body)
  (requirements : initializerNode.requirements = []) (coercions : initializerNode.coercions = [])

include artifact checked entry site read form projected generated issuer declaration polymorphic
  extended ordinary nativeTyped allocated childType sourceEq registered bindings
  initializerFound initializerForm valueType requirements coercions in
theorem reflects (budget : Nat)
    (tail : CellAwareInvocationFlowBounds.ReflectsAtMost
      (attachment := GeneralizedLocalCapturedScopes.Attachment) bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, lowered.type) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.ReflectsAtMost
      (attachment := GeneralizedLocalCapturedScopes.Attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type
      code budget := by
  have payloadEq : payload = lowered.type := by
    by_cases sameType : payload = lowered.type
    · exact sameType
    · simp [SourceCoreBasic.ensureType, sameType] at childType
  subst payload
  obtain ⟨allocation, annotation, same, captured, copied, emitted⟩ := index.let_initialized_snapshot_receipt allocated
  rw [emitted]
  have compilerOrdinary := index.compiler_noninput ordinary
  have copiedIds : ∀ id, (copiedBinder? index.compilerSource id).isSome = (copiedBinder? index.source id).isSome :=
    fun id => (index.copied_ids id).symm
  apply CellAwareInvocationGeneralizedFlow.reflects_at_source
    (allocation := allocation) (annotation := annotation) (copied := copied) <;> assumption


end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGeneralizedAcceptedAllocation
end
