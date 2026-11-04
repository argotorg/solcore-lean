import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedForLoops
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationExpressions
import Solcore.SourceSemantics.CoreLowering.CellAllocationReadiness
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedFlows
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeTypedSourceSites
import Solcore.SourceSemantics.CoreLowering.LoopRenaming
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ScopedSourceInversion
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedTerminalDispatch
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationPhysical
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ActualInvocationAllocation
import Solcore.SourceSemantics.CoreLowering.SourceLetDeclarationFacts
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationAssignments
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping
import Solcore.SourceSemantics.Staging.RecursiveProjectedTargetFacts
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ReadEffects
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ForLoops
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationStatements
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LoopAndMatchBounds
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.Loops
import Solcore.SourceSemantics.CoreLowering.TypedImperativeForPost
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StatementContracts

/-!
# Cell-aware invocations: for loops

`for` loops in one actual body invocation: bounds, state and edges, and initial and post statements by form, for accepted and ordinary allocation.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostBounds
/-! Actual for-post items retain every reached mixed heap and restore the outer
lexical context before another condition. The real header tree closes these
internal preservation and reflection contracts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedForPostContracts (restoredOutcome)
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
  (bodyIndex : ActualBodyInvocation.Index compiled bodyRelation)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope) (items : List ForItemForm)
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
    Dynamic.SourceRuntimeValid program context (bodyIndex.source) →
    invocation.evidence.Covers context →
    context.solvedRequirements = bodyIndex.compilation.solvedRequirements →
    (∃ control final, ForItemsHaveType (bodyIndex.source) control context items final) →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
      Admission bridge context initial →
      CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        bodyIndex.owner bodyIndex.active mapping world before store environment →
    ∀ physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
      owner.key.frameLocation = physical.location →
      ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {finalContext outcome after},
      Staging.Recursive.Size.ForItems program registry size invocation context environment before
        items finalContext outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename embedding) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults (restoredOutcome environment outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ Post bridge context expected (restoredOutcome environment outcome) reached

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
    Dynamic.SourceRuntimeValid program context (bodyIndex.source) →
    invocation.evidence.Covers context →
    context.solvedRequirements = bodyIndex.compilation.solvedRequirements →
    (∃ control final, ForItemsHaveType (bodyIndex.source) control context items final) →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
      Admission bridge context initial →
      CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        bodyIndex.owner bodyIndex.active mapping world before store environment →
    ∀ physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
      owner.key.frameLocation = physical.location →
      ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    EvaluationSize size actual store (code.rename embedding) value finalStore →
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.ForItems program registry sourceSize invocation context environment before
        items finalContext outcome after ∧
      Represents model finalMap finalWorld false expected type faults (restoredOutcome environment outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ Post bridge context expected (restoredOutcome environment outcome) reached

def PreservesAtMost (budget : Nat) : Prop :=
  ∀ size, size ≤ budget → PreservesAt bridge context model bodyIndex producer registry invocation faults administrative scope items expected type code size

def PreservesBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → PreservesAt bridge context model bodyIndex producer registry invocation faults administrative scope items expected type code size

def ReflectsAtMost (budget : Nat) : Prop :=
  ∀ size, size ≤ budget → ReflectsAt bridge context model bodyIndex producer registry invocation faults administrative scope items expected type code size

def ReflectsBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → ReflectsAt bridge context model bodyIndex producer registry invocation faults administrative scope items expected type code size

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostDiscard
/-! Discarded expressions execute once before their actual remaining flow.
Their concrete descriptor effects compose at the reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostDiscard
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
  (bodyIndex : ActualBodyInvocation.Index compiled bodyRelation)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope)
  (expected : TypeSystem.Ty) (type : Ty)


variable {expression : ExpressionId}
  {expressionNode : ExpressionNode} {rest : List ForItemForm}
  {lowered : SourceCoreBasic.LoweredExpr} {body : Expr}
  {certificate : GenericExpressionMeaning.Certificate}
  (sourceEq : invocation.source = bodyIndex.source)
  (expressionFound : invocation.source.lookupExpression? expression = some expressionNode)
  (typed : ExpressionHasType invocation.source context expression expressionNode.type)
  (certified : certificate scope expression lowered)

include expressionFound typed certified in
theorem preserves (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context model bodyIndex registry invocation certificate faults budget)
    (tail : CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment) bridge context model bodyIndex producer registry invocation faults
      administrative scope rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationForPostBounds.PreservesAt (attachment := attachment) bridge context model bodyIndex producer registry invocation faults
      administrative scope (.expression expression :: rest) expected type
      (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready finalContext outcome after trace
  obtain ⟨control, final, original⟩ := sourceTyped
  have suffix : ∃ control final, ForItemsHaveType (bodyIndex.source) control context rest final :=
    ⟨control, CallableIndexedOwnedPreparedStagedForItemsTyping.expression ⟨final, original⟩⟩
  rw [LoopRenaming.discard]
  rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.expression trace with
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

include expressionFound typed certified in
theorem reflects (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context model bodyIndex registry invocation certificate faults budget)
    (tail : CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment) bridge context model bodyIndex producer registry invocation faults
      administrative scope rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationForPostBounds.ReflectsAt (attachment := attachment) bridge context model bodyIndex producer registry invocation faults
      administrative scope (.expression expression :: rest) expected type
      (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready completed
  obtain ⟨control, final, original⟩ := sourceTyped
  have suffix : ∃ control final, ForItemsHaveType (bodyIndex.source) control context rest final :=
    ⟨control, CallableIndexedOwnedPreparedStagedForItemsTyping.expression ⟨final, original⟩⟩
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
        .expressionFailure childTrace, .fault matched, middleHeaps,
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
      exact ⟨Staging.Recursive.Size.stepSize [sourceSize, tailSourceSize], finalContext, outcome, after, finalMap, finalWorld,
        .expression childTrace tailTrace, related, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
        firstFrame.trans preservation, firstMetadata.trans metadata, firstEffect.trans effect,
        reached, protocol.trans expressionRelated tailRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostDiscard
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostAllocation
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostAcceptedAllocation
/-! The existing absent and initialized header proofs use the same actual
invocation, mixed heap, and concrete allocation request source. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostAcceptedAllocation
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
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  (index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

variable {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
  (artifact : sourceCompiled.artifact? = some whole)
  (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
  {parentId : StatementId} {statement : StatementNode}
  {allInitial allPost : List ForItemForm} {condition : ExpressionId} {bodyStatements : List StatementId}
  (reached : index.Reached (.statement parentId))
  (found : index.compilerSource.lookupStatement? parentId = some statement)
  (form : statement.form = .forLoop allInitial condition allPost bodyStatements)

section Absent

variable {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {binder : TypedBinder} {rest : List ForItemForm} {body code : Expr}
  {expected : TypeSystem.Ty} {type payload : Ty} {administrative : Core.Context}
  (present : ForItemForm.letDecl binder none ∈ allInitial ++ allPost)
  (binderLowered : index.policy.lowerBinder index.compilerSource scope binder = .ok payload)
  (extended : BinderExtends index.source.owner context binder nextContext)
  (projected : projects binder.scheme.body payload)
  (allocated : SourceCoreSourceCells.letUninitialized index.policy.sourceCells index.compilerSource scope Renaming.id
    binder payload body = .ok code)
  (sourceEq : invocation.source = index.source)

include artifact checked reached found form present binderLowered extended allocated sourceEq registered bindings projected in
theorem absent_preserves {budget : Nat}
    (ih : CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults administrative
      ((binder.id, payload) :: scope) rest expected type body budget) :
    CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder none :: rest) expected type code budget := by
  have mono := index.header_binder_monomorphic artifact checked found form present binderLowered
  obtain ⟨allocation, annotation, same, emitted⟩ := index.let_uninitialized_receipt allocated
  rw [emitted]
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical
  have sourceFound := (index.reached_view.statement (.inr reached)).trans found
  obtain ⟨member, _singleton, ordinary⟩ :=
    SourceLetDeclarationFacts.of_header_lookup physical.ownership sourceFound form present
  have compilerOrdinary := index.compiler_noninput ordinary
  have sound : CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder none :: rest) expected type
      (.letE annotation.expression body) budget := by
    apply CellAwareInvocationForPostAllocation.absent_preserves
      (allocation := allocation) (annotation := annotation) <;> assumption
  exact sound size within environments heaps locals agrees actualTyped runtime covers sameLedger
    sourceTyped initial admitted authority physical

include artifact checked reached found form present binderLowered extended allocated sourceEq registered bindings projected in
theorem absent_reflects {budget : Nat}
    (ih : CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults administrative
      ((binder.id, payload) :: scope) rest expected type body budget) :
    CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder none :: rest) expected type code budget := by
  have mono := index.header_binder_monomorphic artifact checked found form present binderLowered
  obtain ⟨allocation, annotation, same, emitted⟩ := index.let_uninitialized_receipt allocated
  rw [emitted]
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical
  have sourceFound := (index.reached_view.statement (.inr reached)).trans found
  obtain ⟨member, _singleton, ordinary⟩ :=
    SourceLetDeclarationFacts.of_header_lookup physical.ownership sourceFound form present
  have compilerOrdinary := index.compiler_noninput ordinary
  have sound : CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder none :: rest) expected type
      (.letE annotation.expression body) budget := by
    apply CellAwareInvocationForPostAllocation.absent_reflects
      (allocation := allocation) (annotation := annotation) <;> assumption
  exact sound size within environments heaps locals agrees actualTyped runtime covers sameLedger
    sourceTyped initial admitted authority physical

end Absent

section Initialized

variable {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {binder : TypedBinder} {rest : List ForItemForm} {body code : Expr}
  {expected : TypeSystem.Ty} {type payload : Ty} {administrative : Core.Context}
  {initializer : ExpressionId} {initializerNode : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  (present : ForItemForm.letDecl binder (some initializer) ∈ allInitial ++ allPost)
  (binderLowered : index.policy.lowerBinder index.compilerSource scope binder = .ok payload)
  (extended : BinderExtends index.source.owner context binder nextContext)
  (initializerFound : index.source.lookupExpression? initializer = some initializerNode)
  (valueType : initializerNode.type = binder.scheme.body)
  (typed : ExpressionHasType index.source context initializer initializerNode.type)
  (certified : certificates context scope initializer lowered)
  (childType : SourceCoreBasic.ensureType (.binder binder.id) payload lowered.type = .ok ())
  (allocated : SourceCoreSourceCells.letInitialized index.policy.sourceCells index.compilerSource scope Renaming.id
    binder (LocalLoop.controlType type) payload lowered.expression body = .ok code)
  (sourceEq : invocation.source = index.source)

include artifact checked reached found form present binderLowered extended allocated sourceEq registered bindings childType initializerFound valueType typed certified in
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
      scope (.letDecl binder (some initializer) :: rest) expected type code budget := by
  have payloadEq : payload = lowered.type := by
    by_cases sameType : payload = lowered.type
    · exact sameType
    · simp [SourceCoreBasic.ensureType, sameType] at childType
  subst payload
  have mono := index.header_binder_monomorphic artifact checked found form present binderLowered
  obtain ⟨allocation, annotation, same, emitted⟩ := index.let_initialized_receipt allocated
  rw [emitted]
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical
  have sourceFound := (index.reached_view.statement (.inr reached)).trans found
  obtain ⟨member, _singleton, ordinary⟩ :=
    SourceLetDeclarationFacts.of_header_lookup physical.ownership sourceFound form present
  have compilerOrdinary := index.compiler_noninput ordinary
  have sound : CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder (some initializer) :: rest) expected type
      (sequence type lowered.expression annotation.expression body) budget := by
    apply CellAwareInvocationForPostAllocation.initialized_preserves
      (allocation := allocation) (annotation := annotation) <;> assumption
  exact sound size within environments heaps locals agrees actualTyped runtime covers sameLedger
    sourceTyped initial admitted authority physical

include artifact checked reached found form present binderLowered extended allocated sourceEq registered bindings childType initializerFound valueType typed certified in
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
      scope (.letDecl binder (some initializer) :: rest) expected type code budget := by
  have payloadEq : payload = lowered.type := by
    by_cases sameType : payload = lowered.type
    · exact sameType
    · simp [SourceCoreBasic.ensureType, sameType] at childType
  subst payload
  have mono := index.header_binder_monomorphic artifact checked found form present binderLowered
  obtain ⟨allocation, annotation, same, emitted⟩ := index.let_initialized_receipt allocated
  rw [emitted]
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical
  have sourceFound := (index.reached_view.statement (.inr reached)).trans found
  obtain ⟨member, _singleton, ordinary⟩ :=
    SourceLetDeclarationFacts.of_header_lookup physical.ownership sourceFound form present
  have compilerOrdinary := index.compiler_noninput ordinary
  have sound : CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder (some initializer) :: rest) expected type
      (sequence type lowered.expression annotation.expression body) budget := by
    apply CellAwareInvocationForPostAllocation.initialized_reflects
      (allocation := allocation) (annotation := annotation) <;> assumption
  exact sound size within environments heaps locals agrees actualTyped runtime covers sameLedger
    sourceTyped initial admitted authority physical

end Initialized

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostAcceptedAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostAssignment
/-! Mixed bare assignments execute the real target snapshot, RHS, modifier
and write before the remaining header items. Every reached descriptor survives
both successful updates and genuine failures. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostAssignment
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedImperativeFlow (fault_post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
  {expected : TypeSystem.Ty} {type : Ty}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  {rest : List ForItemForm} {body : Expr}
variable
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (sourceEq : invocation.source = bodyIndex.source)
  (unique : NodeOccurrencesUnique invocation.source)
  (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context certificate
    scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
  (bare : assignment.target.projections = [])
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  (invalidToken : AssignmentOperandDiagnostics.OperandsLaw
    (fun reason token => faults (.semantic reason) token) operator head.invalid)

include transport sourceEq unique bare extension invalidToken in
theorem preserves (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults budget)
    (tail : CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages invocation faults
      administrative scope rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationForPostBounds.PreservesAt (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages invocation faults
      administrative scope (.assignValue assignment operator rhs :: rest) expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready finalContext outcome after trace
  obtain ⟨control, final, original⟩ := sourceTyped
  have facts := CallableIndexedOwnedPreparedStagedForItemsTyping.assignment ⟨final, original⟩
  have assignmentTyped := sourceEq.symm ▸ facts.1
  have suffix : ∃ control final, ForItemsHaveType (bodyIndex.source) control context rest final := ⟨control, facts.2⟩
  obtain ⟨target, snapshot⟩ := CellAwareInvocationBareAssignmentHeads.target_snapshot
    (invocation := invocation) bridge functions extension head bare environments heaps locals agrees initial admitted
  rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.assignment snapshot trace with
    ⟨childSize, failure, sameSize, contextEq, outcomeEq, childTrace⟩ |
    ⟨childSize, right, currentCell, initialValue, currentSelected, sameSize, contextEq, outcomeEq, childTrace,
      currentRead, rootType, initialized, path, invalid⟩ |
    ⟨childSize, tailSize, right, middle, written, updated, sameSize, childTrace, write, remainingTrace⟩
  · subst finalContext
    subst outcome
    have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, stable⟩ :=
      CellAwareInvocationBareAssignmentHeads.preserves_fault bridge functions extension head bare
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
        (children childSize childStrict) childTrace body (LocalLoop.controlType type)
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
      preservation, metadata, effect, reached, related, fault_post bridge reached stable⟩
  · subst finalContext
    subst outcome
    have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, stable⟩ :=
      CellAwareInvocationBareAssignmentHeads.preserves_operands bridge functions extension head bare
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
        (children childSize childStrict) snapshot invalid childTrace body (LocalLoop.controlType type) invalidToken
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
      preservation, metadata, effect, reached, related,
      fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  · have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
        effect, count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
      CellAwareInvocationBareAssignmentHeads.preserves_value bridge functions extension transport head bare
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
        (children childSize childStrict) snapshot childTrace write
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
        finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
      tail tailSize tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees slots) typed runtime covers sameLedger suffix
        reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready remainingTrace
    have native := (continuation body (LocalLoop.controlType type)).wrap (by
      simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
        SourceCoreDataPlaces.shift] using evaluated)
    exact ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps,
      maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame, metadata.trans finalMetadata,
      effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

include transport sourceEq unique bare extension invalidToken in
theorem reflects (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults budget)
    (tail : CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages invocation faults
      administrative scope rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationForPostBounds.ReflectsAt (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages invocation faults
      administrative scope (.assignValue assignment operator rhs :: rest) expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready completed
  obtain ⟨control, final, original⟩ := sourceTyped
  have facts := CallableIndexedOwnedPreparedStagedForItemsTyping.assignment ⟨final, original⟩
  have assignmentTyped := sourceEq.symm ▸ facts.1
  have suffix : ∃ control final, ForItemsHaveType (bodyIndex.source) control context rest final := ⟨control, facts.2⟩
  have result := CellAwareInvocationBareAssignmentHeads.reflects_bounded bridge functions extension transport
    head bare environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
    budget children invalidToken completed within
  cases result with
  | fault snapshot trace same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
    cases same
    exact ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
      .assignmentFailure snapshot trace, .fault matched,
      finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, fault_post bridge reached stable⟩
  | operands snapshot trace currentRead rootType initialized path invalid same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
    cases same
    exact ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
      .assignmentOperands snapshot trace currentRead rootType initialized path invalid,
      .fault matched, finalHeaps, maps, worlds, preservation, metadata, effect, reached, related,
      fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  | success snapshot childTrace write middleHeaps maps worlds preservation metadata effect count typed reached related nextAdmitted strict remaining =>
    obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
        finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
      tail _ (Nat.le_trans (Nat.le_of_lt strict) within) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees _) typed runtime covers sameLedger suffix
        reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready
        (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
          SourceCoreDataPlaces.shift] using remaining)
    exact ⟨Staging.Recursive.Size.stepSize [_, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
      .assignment snapshot childTrace write trace, represented,
      finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
      metadata.trans finalMetadata, effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostAssignment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostProjectedAssignment
/-! Projected assignment sequences retain the reached key, getter, RHS and
write states before continuing through the same mixed scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostProjectedAssignment
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedImperativeFlow (fault_post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
  {expected : TypeSystem.Ty} {type : Ty}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  {rest : List ForItemForm} {body : Expr}
variable
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (sourceEq : invocation.source = bodyIndex.source)
  (unique : NodeOccurrencesUnique invocation.source)
  (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context certificate
    scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
  (projected : assignment.target.projections ≠ [])
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  (diagnostics : SourceAssignmentHasType invocation.source context assignment operator rhs →
    ∀ {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
      (initial : protocol.State initialIndex),
      ProtectedPlaceReachedDiagnostics.ShapeErrors (.initial compiled.compatible.checked) registry functions protocol
        invocation.source context certificate scope administrative environment assignment.target head.prepared operator head.invalid
        initial (fun reason token => faults (.semantic reason) token) head.shape)

include transport sourceEq unique projected extension faithful observations diagnostics in
theorem preserves (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults budget)
    (tail : CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages invocation faults
      administrative scope rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationForPostBounds.PreservesAt (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages invocation faults
      administrative scope (.assignValue assignment operator rhs :: rest) expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready finalContext outcome after trace
  obtain ⟨control, final, original⟩ := sourceTyped
  have facts := CallableIndexedOwnedPreparedStagedForItemsTyping.assignment ⟨final, original⟩
  have assignmentTyped := sourceEq.symm ▸ facts.1
  have suffix : ∃ control final, ForItemsHaveType (bodyIndex.source) control context rest final := ⟨control, facts.2⟩
  cases trace with
  | assignment snapshot _ _ _ | assignmentFailure snapshot _ | assignmentOperands snapshot _ _ _ _ _ _ =>
    cases snapshot with | intro empty _ _ _ => exact (projected empty).elim
  | unbound empty _ | dangling empty _ _ => exact (projected empty).elim
  | projectedAssignmentRootFault _ failed => exact False.elim (failed.excluded head.writable locals)
  | projectedAssignmentKeysFault _ ready keyTrace =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
          preservation, metadata, effect, reached, related, stable⟩ :=
        CellAwareInvocationProjectedAssignmentHeads.preserves_key_fault
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children ready keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge reached stable⟩
  | projectedAssignmentGetterFault _ keyTrace failed =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
          preservation, metadata, effect, reached, related, stable⟩ :=
        CellAwareInvocationProjectedAssignmentHeads.preserves_getter_fault
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children (diagnostics assignmentTyped initial)
          keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) failed body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  | projectedAssignmentRhsFault _ keyTrace snapshot childTrace =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
          preservation, metadata, effect, reached, related, stable⟩ :=
        CellAwareInvocationProjectedAssignmentHeads.preserves_fault
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot childTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge reached stable⟩
  | projectedAssignmentWriteFault _ keyTrace snapshot childTrace failed =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
          preservation, metadata, effect, reached, related, stable⟩ :=
        CellAwareInvocationProjectedAssignmentHeads.preserves_write_fault
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children (diagnostics assignmentTyped initial)
          keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot childTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) failed body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  | projectedAssignment _ keyTrace snapshot childTrace write remainingTrace =>
      obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
          effect, count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
        CellAwareInvocationProjectedAssignmentHeads.preserves_value
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot childTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) write
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
          finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
        tail _ (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed runtime covers sameLedger suffix
          reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready remainingTrace
      have native := (continuation body (LocalLoop.controlType type)).wrap (by
        simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
          SourceCoreDataPlaces.shift] using evaluated)
      exact ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps,
        maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame, metadata.trans finalMetadata,
        effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

include transport sourceEq unique projected extension faithful observations diagnostics in
theorem reflects (functionTypes : FunctionRuntimeViews functions) (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults budget)
    (tail : CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages invocation faults
      administrative scope rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationForPostBounds.ReflectsAt (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages invocation faults
      administrative scope (.assignValue assignment operator rhs :: rest) expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready completed
  obtain ⟨control, final, original⟩ := sourceTyped
  have facts := CallableIndexedOwnedPreparedStagedForItemsTyping.assignment ⟨final, original⟩
  have assignmentTyped := sourceEq.symm ▸ facts.1
  have suffix : ∃ control final, ForItemsHaveType (bodyIndex.source) control context rest final := ⟨control, facts.2⟩
  have result := CellAwareInvocationProjectedAssignmentHeads.reflects_bounded (compiled := compiled)
    (invocation := invocation)
    (context := context) (scope := scope) (administrative := administrative) bridge functions extension transport faithful observations
    head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
    budget children functionTypes
      (diagnostics assignmentTyped initial) completed within
  cases result with
  | keyFault ready keyTrace same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
      cases same
      refine ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
        .projectedAssignmentKeysFault projected ready keyTrace, .fault matched,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge reached stable
  | getterFault keyTrace failed same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
      cases same
      refine ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
        .projectedAssignmentGetterFault projected keyTrace failed, .fault matched,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable
  | rhsFault keyTrace snapshot childTrace same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
      cases same
      refine ⟨Staging.Recursive.Size.stepSize [_, _], context, _, _, _, _,
        .projectedAssignmentRhsFault projected keyTrace snapshot childTrace, .fault matched,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge reached stable
  | writeFault keyTrace snapshot childTrace failed same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
      cases same
      refine ⟨Staging.Recursive.Size.stepSize [_, _], context, _, _, _, _,
        .projectedAssignmentWriteFault projected keyTrace snapshot childTrace failed, .fault matched,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable
  | success keyTrace snapshot childTrace write middleHeaps maps worlds preservation metadata effect count typed reached related nextAdmitted strict remaining =>
      obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
          finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
        tail _ (Nat.le_trans (Nat.le_of_lt strict) within)
          (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees _) typed runtime covers sameLedger suffix
          reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready
          (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
      exact ⟨Staging.Recursive.Size.stepSize [_, _, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
        .projectedAssignment projected keyTrace snapshot childTrace write trace, represented,
        finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
        metadata.trans finalMetadata, effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostProjectedAssignment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostBitNot
/-! Actual bare bit-not post-header items preserve and reflect the same mixed heap.
The original invocation, seven administrative slots and remaining post-header are
retained through the write, including unrelated generalized closure cells. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostBitNot
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedImperativeFlow (fault_post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
  {expected : TypeSystem.Ty} {type : Ty} {assignment : AssignmentResolution}
  {rest : List ForItemForm} {body : Expr}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (head : CompatibleBitNotStatements.Head context scope assignment)
  (sourceEq : invocation.source = bodyIndex.source)
  (errors : head.Errors (fun reason token => faults (.semantic reason) token))

include transport sourceEq errors in
theorem preserves (budget : Nat)
    (tail : CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment)
      bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      bodyIndex producer stages invocation faults administrative scope rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationForPostBounds.PreservesAt (attachment := attachment)
      bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      bodyIndex producer stages invocation faults administrative scope (.assignBitNot assignment :: rest)
      expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready finalContext outcome after trace
  obtain ⟨control, final, original⟩ := sourceTyped
  have facts := CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot ⟨final, original⟩
  have assignmentTyped := sourceEq.symm ▸ facts.1
  have suffix : ∃ control final, ForItemsHaveType bodyIndex.source control context rest final := ⟨control, facts.2⟩
  rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.bitNot head.bare trace with
    ⟨reason, _sameSize, contextEq, outcomeEq, heapEq, failed⟩ |
    ⟨tailSize, target, updated, written, sameSize, snapshot, write, remainingTrace⟩
  · subst finalContext
    subst outcome
    subst after
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
        preservation, effect, reached, related, stable⟩ :=
      CellAwareBareBitNotHeads.preserves_fault (values := .initial compiled.compatible.checked)
        (instances := GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        bridge functions transport head environments GeneralizedLocalDescriptorHeap.ordinary_cells
        heaps locals agrees initial admitted errors failed body (LocalLoop.controlType type)
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
      preservation, .refl _, effect, reached, related, fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  · have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
        effect, count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
      CellAwareBareBitNotHeads.preserves_value (values := .initial compiled.compatible.checked)
        (instances := GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        bridge functions transport head environments GeneralizedLocalDescriptorHeap.ordinary_cells
        heaps locals agrees actualTyped initial admitted assignmentTyped snapshot write
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
        finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
      tail tailSize tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees slots) typed runtime covers sameLedger suffix
        reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready remainingTrace
    have native := (continuation body (LocalLoop.controlType type)).wrap (by
      simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
        SourceCoreDataPlaces.shift] using evaluated)
    exact ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps,
      maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame, metadata.trans finalMetadata,
      effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

include transport sourceEq errors in
theorem reflects (budget : Nat)
    (tail : CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment)
      bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      bodyIndex producer stages invocation faults administrative scope rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationForPostBounds.ReflectsAt (attachment := attachment)
      bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      bodyIndex producer stages invocation faults administrative scope (.assignBitNot assignment :: rest)
      expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready completed
  obtain ⟨control, final, original⟩ := sourceTyped
  have facts := CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot ⟨final, original⟩
  have assignmentTyped := sourceEq.symm ▸ facts.1
  have suffix : ∃ control final, ForItemsHaveType bodyIndex.source control context rest final := ⟨control, facts.2⟩
  have result := CellAwareBareBitNotHeads.reflects_bounded (values := .initial compiled.compatible.checked)
        (instances := GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
    bridge functions transport head environments GeneralizedLocalDescriptorHeap.ordinary_cells
    heaps locals agrees actualTyped initial admitted assignmentTyped errors completed
  cases result with
  | fault trace same matched finalHeaps maps worlds preservation effect reached related stable =>
    cases same
    exact ⟨Staging.Recursive.Size.stepSize [], context, _, _, _, _,
      .bitNotFault head.bare trace, .fault matched,
      finalHeaps, maps, worlds, preservation, .refl _, effect, reached, related, fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  | success snapshot write middleHeaps maps worlds preservation metadata effect count typed reached related nextAdmitted strict remaining =>
    obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
        finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
      tail _ (Nat.le_trans (Nat.le_of_lt strict) within) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees _) typed runtime covers sameLedger suffix
        reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready
        (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
          SourceCoreDataPlaces.shift] using remaining)
    exact ⟨Staging.Recursive.Size.stepSize [sourceSize], finalContext, outcome, after, finalMap, finalWorld,
      .bitNot snapshot write trace, represented,
      finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
      metadata.trans finalMetadata, effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostBitNot
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostProjectedBitNot
/-! Projected unary headers execute the ordered keys, getter and write
before continuing through the same actual invocation and mixed scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostProjectedBitNot
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedImperativeFlow (fault_post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
  {expected : TypeSystem.Ty} {type : Ty}
  {assignment : AssignmentResolution}
  {rest : List ForItemForm} {body : Expr}
variable
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (sourceEq : invocation.source = bodyIndex.source)
  (unique : NodeOccurrencesUnique invocation.source)
  (head : CompatibleProjectedBitNotStatements.Head (.initial compiled.compatible.checked) invocation.source context certificate
    scope administrative compiled.indexed.layouts.definitions assignment)
  (projected : assignment.target.projections ≠ [])
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  (diagnostics : SourceBitNotAssignmentValid invocation.source context assignment →
    ∀ {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
      (initial : protocol.State initialIndex),
      CompatibleProjectedBitNotStatements.Head.ReachedErrors
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        functions protocol head environment initial (fun reason token => faults (.semantic reason) token)
        (registry := registry))

include transport sourceEq unique projected extension faithful observations diagnostics in
theorem preserves (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults budget)
    (tail : CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages invocation faults
      administrative scope rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationForPostBounds.PreservesAt (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages invocation faults
      administrative scope (.assignBitNot assignment :: rest) expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready finalContext outcome after trace
  obtain ⟨control, final, original⟩ := sourceTyped
  have facts := CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot ⟨final, original⟩
  have assignmentTyped := sourceEq.symm ▸ facts.1
  have suffix : ∃ control final, ForItemsHaveType (bodyIndex.source) control context rest final := ⟨control, facts.2⟩
  cases trace with
  | bitNot snapshot _ _ =>
    cases snapshot with | intro empty _ _ _ => exact (projected empty).elim
  | bitNotFault empty _ => exact (projected empty).elim
  | projectedBitNotRootFault _ failed => exact False.elim (failed.excluded head.writable locals)
  | projectedBitNotKeysFault _ ready keyTrace =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
          preservation, metadata, effect, reached, related, stable⟩ :=
        CellAwareInvocationProjectedBitNotHeads.preserves_key_fault
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children ready keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge reached stable⟩
  | projectedBitNotGetterFault _ keyTrace failed =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
          preservation, metadata, effect, reached, related, stable⟩ :=
        CellAwareInvocationProjectedBitNotHeads.preserves_getter_fault
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children (diagnostics assignmentTyped initial)
          keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) failed body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  | projectedBitNot _ keyTrace snapshot write remainingTrace =>
      obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
          effect, count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
        CellAwareInvocationProjectedBitNotHeads.preserves_value
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot write
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
          finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
        tail _ (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed runtime covers sameLedger suffix
          reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready remainingTrace
      have native := (continuation body (LocalLoop.controlType type)).wrap (by
        simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
          SourceCoreDataPlaces.shift] using evaluated)
      exact ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps,
        maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame, metadata.trans finalMetadata,
        effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

include transport sourceEq unique projected extension faithful observations diagnostics in
theorem reflects (functionTypes : FunctionRuntimeViews functions) (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults budget)
    (tail : CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages invocation faults
      administrative scope rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationForPostBounds.ReflectsAt (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages invocation faults
      administrative scope (.assignBitNot assignment :: rest) expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready completed
  obtain ⟨control, final, original⟩ := sourceTyped
  have facts := CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot ⟨final, original⟩
  have assignmentTyped := sourceEq.symm ▸ facts.1
  have suffix : ∃ control final, ForItemsHaveType (bodyIndex.source) control context rest final := ⟨control, facts.2⟩
  have result := CellAwareInvocationProjectedBitNotHeads.reflects_bounded (compiled := compiled)
    (invocation := invocation)
    (context := context) (scope := scope) (administrative := administrative) bridge functions extension transport faithful observations
    head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
    budget children functionTypes
      (diagnostics assignmentTyped initial) completed within
  cases result with
  | keyFault ready keyTrace same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
      cases same
      refine ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
        .projectedBitNotKeysFault projected ready keyTrace, .fault matched,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge reached stable
  | getterFault keyTrace failed same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
      cases same
      refine ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
        .projectedBitNotGetterFault projected keyTrace failed, .fault matched,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable
  | success keyTrace snapshot write middleHeaps maps worlds preservation metadata effect count typed reached related nextAdmitted strict remaining =>
      obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
          finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
        tail _ (Nat.le_trans (Nat.le_of_lt strict) within)
          (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees _) typed runtime covers sameLedger suffix
          reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready
          (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
      exact ⟨Staging.Recursive.Size.stepSize [_, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
        .projectedBitNot projected keyTrace snapshot write trace, represented,
        finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
        metadata.trans finalMetadata, effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostProjectedBitNot
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialBounds
/-! Actual initializer prefixes keep their bindings through the finite loop,
then restore the original lexical observations with the reached mixed heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedForHeadContracts (Trace)
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
  (bodyIndex : ActualBodyInvocation.Index compiled bodyRelation)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope) (items : List ForItemForm)
  (test : ExpressionId) (postItems : List ForItemForm) (statements : List StatementId)
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
    Dynamic.SourceRuntimeValid program context (bodyIndex.source) →
    invocation.evidence.Covers context →
    context.solvedRequirements = bodyIndex.compilation.solvedRequirements →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
      Admission bridge context initial →
      CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        bodyIndex.owner bodyIndex.active mapping world before store environment →
    ∀ physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
      owner.key.frameLocation = physical.location →
      ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {outcome after},
      Trace program registry invocation context environment before items test postItems statements size outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename embedding) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
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
    Dynamic.SourceRuntimeValid program context (bodyIndex.source) →
    invocation.evidence.Covers context →
    context.solvedRequirements = bodyIndex.compilation.solvedRequirements →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
      Admission bridge context initial →
      CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        bodyIndex.owner bodyIndex.active mapping world before store environment →
    ∀ physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
      owner.key.frameLocation = physical.location →
      ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    EvaluationSize size actual store (code.rename embedding) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      Trace program registry invocation context environment before items test postItems statements sourceSize outcome after ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
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
  ∀ size, size ≤ budget → PreservesAt bridge context model bodyIndex producer registry invocation faults administrative scope items test postItems statements expected type code size

def PreservesBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → PreservesAt bridge context model bodyIndex producer registry invocation faults administrative scope items test postItems statements expected type code size

def ReflectsAtMost (budget : Nat) : Prop :=
  ∀ size, size ≤ budget → ReflectsAt bridge context model bodyIndex producer registry invocation faults administrative scope items test postItems statements expected type code size

def ReflectsBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → ReflectsAt bridge context model bodyIndex producer registry invocation faults administrative scope items test postItems statements expected type code size

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialDiscard
/-! Discarded expressions execute once before their actual remaining flow.
Their concrete descriptor effects compose at the reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialDiscard
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedForInitializerSource
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
  (bodyIndex : ActualBodyInvocation.Index compiled bodyRelation)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope)
  (expected : TypeSystem.Ty) (type : Ty)


variable {expression : ExpressionId}
  {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}
  {expressionNode : ExpressionNode} {rest : List ForItemForm}
  {lowered : SourceCoreBasic.LoweredExpr} {body : Expr}
  {certificate : GenericExpressionMeaning.Certificate}
  (sourceEq : invocation.source = bodyIndex.source)
  (expressionFound : invocation.source.lookupExpression? expression = some expressionNode)
  (typed : ExpressionHasType invocation.source context expression expressionNode.type)
  (certified : certificate scope expression lowered)

include expressionFound typed certified in
theorem preserves (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context model bodyIndex registry invocation certificate faults budget)
    (tail : CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment) bridge context model bodyIndex producer registry invocation faults
      administrative scope rest test postItems statements expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationForInitialBounds.PreservesAt (attachment := attachment) bridge context model bodyIndex producer registry invocation faults
      administrative scope (.expression expression :: rest) test postItems statements expected type
      (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger
    initial admitted authority physical owner sameLocation ready outcome after trace
  rw [LoopRenaming.discard]
  rcases CallableIndexedOwnedAdmittedStagedForInitializerSource.expression trace with
    ⟨childSize, failure, sameSize, outcomeEq, childTrace⟩ |
    ⟨childSize, tailSize, sourceValue, middle, sameSize, childTrace, remainingTrace⟩
  · subst outcome
    have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega) within
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, post⟩ :=
      children childSize childStrict certified expressionFound typed environments heaps locals agrees actualTyped
        initial admitted authority physical owner sameLocation childTrace
    cases represented with
    | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LocalSequence.discard_failure _ evaluated,
        .fault matched, finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, post.at_fault_type⟩
  · have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega) within
    have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega)) within
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
            runtime covers sameLedger middleState firstPost.at_value.2 (authority.transport firstEffect)
            (physical.transport firstEffect firstFrame) owner sameLocation ready remainingTrace
        rw [GenericExpressionMeaning.rename_prefix] at second
        exact ⟨value, finalStore, finalMap, finalWorld, LocalSequence.discard_success _ first second,
          related, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans preservation,
          firstMetadata.trans metadata, firstEffect.trans effect, reached, protocol.trans expressionRelated tailRelated, post⟩

include expressionFound typed certified in
theorem reflects (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context model bodyIndex registry invocation certificate faults budget)
    (tail : CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment) bridge context model bodyIndex producer registry invocation faults
      administrative scope rest test postItems statements expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationForInitialBounds.ReflectsAt (attachment := attachment) bridge context model bodyIndex producer registry invocation faults
      administrative scope (.expression expression :: rest) test postItems statements expected type
      (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger
    initial admitted authority physical owner sameLocation ready completed
  rw [LoopRenaming.discard] at completed
  obtain ⟨childSize, middleStore, input, smaller, childEvaluation⟩ := completed.bind_computation
  obtain ⟨sourceSize, childOutcome, middle, middleMap, middleWorld, childTrace, represented,
      middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, expressionRelated, firstPost⟩ :=
    children childSize (Nat.lt_of_lt_of_le smaller within) certified expressionFound typed
      environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation childEvaluation
  cases represented with
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalSequence.discard_failure _ childEvaluation.sound)
      exact ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [sourceSize]], _, middle, middleMap, middleWorld,
        expression_fault childTrace, .fault matched, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, expressionRelated, firstPost.at_fault_type⟩
  | @value sourceValue coreValue payload =>
      obtain ⟨tailSize, tailSmaller, tailEvaluation⟩ := completed.bind_success childEvaluation.sound
      obtain ⟨tailSourceSize, outcome, after, finalMap, finalWorld, tailTrace, related,
          finalHeaps, maps, worlds, preservation, metadata, effect, reached, tailRelated, post⟩ :=
        tail tailSize (Nat.le_trans (Nat.le_of_lt tailSmaller) within)
          (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
          (GenericExpressionMeaning.agree_prefix agrees coreValue)
          (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds)) runtime covers sameLedger
          middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame)
          owner sameLocation ready (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEvaluation)
      exact ⟨Staging.Recursive.Size.stepSize [sourceSize, tailSourceSize], outcome, after, finalMap, finalWorld,
        prepend_expression childTrace tailTrace, related, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
        firstFrame.trans preservation, firstMetadata.trans metadata, firstEffect.trans effect,
        reached, protocol.trans expressionRelated tailRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialDiscard
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialAllocation
/-! The existing absent and initialized header proofs use the same actual
invocation, mixed heap, and concrete allocation request source. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open CallableIndexedOwnedAdmittedStagedForInitializerSource
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
  {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}

include model in
private theorem rep_restore {mapping world expected type outcome value environment}
    (related : Represents model
      mapping world false expected type faults outcome value) :
    Represents model
      mapping world false expected type faults (outcome.restore environment) value := by
  cases related with
  | returned payload => exact .returned payload
  | fault matched => exact .fault matched
  | fallthrough _ allowed => exact .fallthrough environment allowed
  | breaking _ => exact .breaking environment
  | continuing _ => exact .continuing environment

private theorem post_restore {context expected outcome environment index}
    {reached : protocol.State index}
    (post : Post bridge context expected outcome reached) :
    Post bridge context expected (outcome.restore environment) reached := by
  cases outcome <;> exact post


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
    (ih : CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults administrative
      ((binder.id, payload) :: scope) rest test postItems statements expected type body budget) :
    CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder none :: rest) test postItems statements expected type (.letE annotation.expression body) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready
    outcome after trace
  obtain ⟨tailSize, location, bound, nextOutcome, sameSize, sameOutcome, allocated, remainingTrace⟩ :=
    CallableIndexedOwnedAdmittedStagedForInitializerSource.absent
      (by simpa only [sourceEq] using extended) trace
  subst outcome
  have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
    simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega)) within
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
      reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady remainingTrace
  let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (id := binder.id) (type := payload)
    (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
  refine ⟨value, finalStore, finalMap, finalWorld, agreement.wrap evaluated, rep_restore model represented, finalHeaps,
    effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
    effect.metadata.trans metadata, effect.trans finalEffect, finalState,
    protocol.trans related (protocol.trans tailRelated (bindings.restore_related
      (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := payload)
      (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
  apply post_restore bridge
  exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post


include member mono extended ordinary projected allocation annotation same sourceEq registered bindings in
theorem absent_reflects {budget : Nat}
    (ih : CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults administrative
      ((binder.id, payload) :: scope) rest test postItems statements expected type body budget) :
    CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder none :: rest) test postItems statements expected type (.letE annotation.expression body) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready
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
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, finalFrame, metadata, finalEffect, tailState, tailRelated, post⟩ :=
    ih _ (Nat.le_trans (Nat.le_of_lt strict) within) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
      (runtime.transport (.ofBinderExtends extended))
      ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
      ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
      reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tailCompleted
  let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (id := binder.id) (type := payload)
    (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
  refine ⟨Staging.Recursive.Size.stepSize [sourceSize], outcome.restore environment, after, finalMap, finalWorld,
    prepend_absent mono (by simpa only [sourceEq] using extended) allocated trace,
    rep_restore model represented, finalHeaps, effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
    effect.metadata.trans metadata, effect.trans finalEffect, finalState,
    protocol.trans related (protocol.trans tailRelated (bindings.restore_related
      (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := payload)
      (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
  apply post_restore bridge
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
    (ih : CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults administrative
      ((binder.id, lowered.type) :: scope) rest test postItems statements expected type body budget) :
    CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder (some initializer) :: rest) test postItems statements expected type (sequence type lowered.expression annotation.expression body) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready
    outcome after trace
  rcases CallableIndexedOwnedAdmittedStagedForInitializerSource.initialized mono
      (by simpa only [sourceEq] using extended) trace with
    ⟨childSize, failure, sameSize, outcomeEq, child⟩ |
    ⟨childSize, tailSize, sourceValue, location, middle, bound, nextOutcome, sameSize, sameOutcome, child, allocated, remainingTrace⟩
  · subst outcome
    have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega) within
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
      children context runtime covers sameLedger childSize childStrict certified
        (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation child
    cases represented with
    | fault matched =>
      exact ⟨_, finalStore, finalMap, finalWorld, CellAwareOrdinaryContinuation.failure evaluated,
        .fault matched, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post.at_fault_type⟩
  · subst outcome
    have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega) within
    have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega)) within
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
          reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady remainingTrace
      let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := lowered.type)
        (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
      refine ⟨value, finalStore, finalMap, finalWorld, agreement.wrap tailEvaluated, rep_restore model represented, finalHeaps,
        maps.trans (allocationEffect.maps.trans tailMaps), worlds.trans (allocationEffect.worlds.trans tailWorlds),
        frame.trans (preserved.trans finalFrame), metadata.trans (allocationEffect.metadata.trans finalMetadata),
        effect.trans (allocationEffect.trans finalEffect), finalState,
        protocol.trans expressionRelated (protocol.trans related (protocol.trans tailRelated (bindings.restore_related
          (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
          (id := binder.id) (type := lowered.type)
          (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
      apply post_restore bridge
      exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState tailPost

include member mono extended ordinary initializerFound valueType typed certified allocation annotation same sourceEq registered bindings in
theorem initialized_reflects {budget : Nat}
    (children : ∀ context, Dynamic.SourceRuntimeValid program context index.source →
      invocation.evidence.Covers context → context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context model index registry invocation
        (certificates context) faults budget)
    (ih : CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults administrative
      ((binder.id, lowered.type) :: scope) rest test postItems statements expected type body budget) :
    CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder (some initializer) :: rest) test postItems statements expected type (sequence type lowered.expression annotation.expression body) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready
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
    exact ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [childSourceSize]], _, middle, middleMap, middleWorld,
      initializer_fault mono child,
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
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        tailMaps, tailWorlds, finalFrame, finalMetadata, finalEffect, tailState, tailRelated, tailPost⟩ :=
      ih _ (Nat.le_trans (Nat.le_of_lt tailStrict) within) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
        (runtime.transport (.ofBinderExtends extended))
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
        reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tailEvaluation
    let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := lowered.type)
      (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
    refine ⟨Staging.Recursive.Size.stepSize [childSourceSize, sourceSize], outcome.restore environment, after, finalMap, finalWorld,
      prepend_initialized mono (by simpa only [sourceEq] using extended) child allocated trace,
      rep_restore model represented, finalHeaps, maps.trans (allocationEffect.maps.trans tailMaps), worlds.trans (allocationEffect.worlds.trans tailWorlds),
      frame.trans (preserved.trans finalFrame), metadata.trans (allocationEffect.metadata.trans finalMetadata),
      effect.trans (allocationEffect.trans finalEffect), finalState,
      protocol.trans expressionRelated (protocol.trans related (protocol.trans tailRelated (bindings.restore_related
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := lowered.type)
        (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
    apply post_restore bridge
    exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState tailPost

end Initialized

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialAcceptedAllocation
/-! The existing absent and initialized header proofs use the same actual
invocation, mixed heap, and concrete allocation request source. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialAcceptedAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open CallableIndexedOwnedAdmittedStagedForInitializerSource
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
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  (index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}

variable {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
  (artifact : sourceCompiled.artifact? = some whole)
  (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
  {parentId : StatementId} {statement : StatementNode}
  {allInitial allPost : List ForItemForm} {condition : ExpressionId} {bodyStatements : List StatementId}
  (reached : index.Reached (.statement parentId))
  (found : index.compilerSource.lookupStatement? parentId = some statement)
  (form : statement.form = .forLoop allInitial condition allPost bodyStatements)

section Absent

variable {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {binder : TypedBinder} {rest : List ForItemForm} {body code : Expr}
  {expected : TypeSystem.Ty} {type payload : Ty} {administrative : Core.Context}
  (present : ForItemForm.letDecl binder none ∈ allInitial ++ allPost)
  (binderLowered : index.policy.lowerBinder index.compilerSource scope binder = .ok payload)
  (extended : BinderExtends index.source.owner context binder nextContext)
  (projected : projects binder.scheme.body payload)
  (allocated : SourceCoreSourceCells.letUninitialized index.policy.sourceCells index.compilerSource scope Renaming.id
    binder payload body = .ok code)
  (sourceEq : invocation.source = index.source)

include artifact checked reached found form present binderLowered extended allocated sourceEq registered bindings projected in
theorem absent_preserves {budget : Nat}
    (ih : CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults administrative
      ((binder.id, payload) :: scope) rest test postItems statements expected type body budget) :
    CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder none :: rest) test postItems statements expected type code budget := by
  have mono := index.header_binder_monomorphic artifact checked found form present binderLowered
  obtain ⟨allocation, annotation, same, emitted⟩ := index.let_uninitialized_receipt allocated
  rw [emitted]
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical
  have sourceFound := (index.reached_view.statement (.inr reached)).trans found
  obtain ⟨member, _singleton, ordinary⟩ :=
    SourceLetDeclarationFacts.of_header_lookup physical.ownership sourceFound form present
  have compilerOrdinary := index.compiler_noninput ordinary
  have sound : CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder none :: rest) test postItems statements expected type
      (.letE annotation.expression body) budget := by
    apply CellAwareInvocationForInitialAllocation.absent_preserves
      (allocation := allocation) (annotation := annotation) <;> assumption
  exact sound size within environments heaps locals agrees actualTyped runtime covers sameLedger
    initial admitted authority physical

include artifact checked reached found form present binderLowered extended allocated sourceEq registered bindings projected in
theorem absent_reflects {budget : Nat}
    (ih : CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults administrative
      ((binder.id, payload) :: scope) rest test postItems statements expected type body budget) :
    CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder none :: rest) test postItems statements expected type code budget := by
  have mono := index.header_binder_monomorphic artifact checked found form present binderLowered
  obtain ⟨allocation, annotation, same, emitted⟩ := index.let_uninitialized_receipt allocated
  rw [emitted]
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical
  have sourceFound := (index.reached_view.statement (.inr reached)).trans found
  obtain ⟨member, _singleton, ordinary⟩ :=
    SourceLetDeclarationFacts.of_header_lookup physical.ownership sourceFound form present
  have compilerOrdinary := index.compiler_noninput ordinary
  have sound : CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder none :: rest) test postItems statements expected type
      (.letE annotation.expression body) budget := by
    apply CellAwareInvocationForInitialAllocation.absent_reflects
      (allocation := allocation) (annotation := annotation) <;> assumption
  exact sound size within environments heaps locals agrees actualTyped runtime covers sameLedger
    initial admitted authority physical

end Absent

section Initialized

variable {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {binder : TypedBinder} {rest : List ForItemForm} {body code : Expr}
  {expected : TypeSystem.Ty} {type payload : Ty} {administrative : Core.Context}
  {initializer : ExpressionId} {initializerNode : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  (present : ForItemForm.letDecl binder (some initializer) ∈ allInitial ++ allPost)
  (binderLowered : index.policy.lowerBinder index.compilerSource scope binder = .ok payload)
  (extended : BinderExtends index.source.owner context binder nextContext)
  (initializerFound : index.source.lookupExpression? initializer = some initializerNode)
  (valueType : initializerNode.type = binder.scheme.body)
  (typed : ExpressionHasType index.source context initializer initializerNode.type)
  (certified : certificates context scope initializer lowered)
  (childType : SourceCoreBasic.ensureType (.binder binder.id) payload lowered.type = .ok ())
  (allocated : SourceCoreSourceCells.letInitialized index.policy.sourceCells index.compilerSource scope Renaming.id
    binder (LocalLoop.controlType type) payload lowered.expression body = .ok code)
  (sourceEq : invocation.source = index.source)

include artifact checked reached found form present binderLowered extended allocated sourceEq registered bindings childType initializerFound valueType typed certified in
theorem initialized_preserves {budget : Nat}
    (children : ∀ context, Dynamic.SourceRuntimeValid program context index.source →
      invocation.evidence.Covers context → context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context model index registry invocation
        (certificates context) faults budget)
    (ih : CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults administrative
      ((binder.id, lowered.type) :: scope) rest test postItems statements expected type body budget) :
    CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder (some initializer) :: rest) test postItems statements expected type code budget := by
  have payloadEq : payload = lowered.type := by
    by_cases sameType : payload = lowered.type
    · exact sameType
    · simp [SourceCoreBasic.ensureType, sameType] at childType
  subst payload
  have mono := index.header_binder_monomorphic artifact checked found form present binderLowered
  obtain ⟨allocation, annotation, same, emitted⟩ := index.let_initialized_receipt allocated
  rw [emitted]
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical
  have sourceFound := (index.reached_view.statement (.inr reached)).trans found
  obtain ⟨member, _singleton, ordinary⟩ :=
    SourceLetDeclarationFacts.of_header_lookup physical.ownership sourceFound form present
  have compilerOrdinary := index.compiler_noninput ordinary
  have sound : CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder (some initializer) :: rest) test postItems statements expected type
      (sequence type lowered.expression annotation.expression body) budget := by
    apply CellAwareInvocationForInitialAllocation.initialized_preserves
      (allocation := allocation) (annotation := annotation) <;> assumption
  exact sound size within environments heaps locals agrees actualTyped runtime covers sameLedger
    initial admitted authority physical

include artifact checked reached found form present binderLowered extended allocated sourceEq registered bindings childType initializerFound valueType typed certified in
theorem initialized_reflects {budget : Nat}
    (children : ∀ context, Dynamic.SourceRuntimeValid program context index.source →
      invocation.evidence.Covers context → context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context model index registry invocation
        (certificates context) faults budget)
    (ih : CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults administrative
      ((binder.id, lowered.type) :: scope) rest test postItems statements expected type body budget) :
    CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder (some initializer) :: rest) test postItems statements expected type code budget := by
  have payloadEq : payload = lowered.type := by
    by_cases sameType : payload = lowered.type
    · exact sameType
    · simp [SourceCoreBasic.ensureType, sameType] at childType
  subst payload
  have mono := index.header_binder_monomorphic artifact checked found form present binderLowered
  obtain ⟨allocation, annotation, same, emitted⟩ := index.let_initialized_receipt allocated
  rw [emitted]
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical
  have sourceFound := (index.reached_view.statement (.inr reached)).trans found
  obtain ⟨member, _singleton, ordinary⟩ :=
    SourceLetDeclarationFacts.of_header_lookup physical.ownership sourceFound form present
  have compilerOrdinary := index.compiler_noninput ordinary
  have sound : CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder (some initializer) :: rest) test postItems statements expected type
      (sequence type lowered.expression annotation.expression body) budget := by
    apply CellAwareInvocationForInitialAllocation.initialized_reflects
      (allocation := allocation) (annotation := annotation) <;> assumption
  exact sound size within environments heaps locals agrees actualTyped runtime covers sameLedger
    initial admitted authority physical

end Initialized

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialAcceptedAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialAssignment
/-! Mixed bare assignments execute the real target snapshot, RHS, modifier
and write before the remaining header items. Every reached descriptor survives
both successful updates and genuine failures. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialAssignment
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedImperativeFlow (fault_post)
open CallableIndexedOwnedAdmittedStagedForInitializerSource
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
  {expected : TypeSystem.Ty} {type : Ty}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}
  {rest : List ForItemForm} {body : Expr}
variable
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (sourceEq : invocation.source = bodyIndex.source)
  (unique : NodeOccurrencesUnique invocation.source)
  (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context certificate
    scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
  (bare : assignment.target.projections = [])
  (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  (invalidToken : AssignmentOperandDiagnostics.OperandsLaw
    (fun reason token => faults (.semantic reason) token) operator head.invalid)

include transport unique bare assignmentTyped extension invalidToken in
theorem preserves (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults budget)
    (tail : CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages invocation faults
      administrative scope rest test postItems statements expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationForInitialBounds.PreservesAt (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages invocation faults
      administrative scope (.assignValue assignment operator rhs :: rest) test postItems statements expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger
    initial admitted authority physical owner sameLocation ready outcome after trace
  obtain ⟨target, snapshot⟩ := CellAwareInvocationBareAssignmentHeads.target_snapshot
    (invocation := invocation) bridge functions extension head bare environments heaps locals agrees initial admitted
  rcases CallableIndexedOwnedAdmittedStagedForInitializerSource.assignment snapshot trace with
    ⟨childSize, failure, sameSize, outcomeEq, childTrace⟩ |
    ⟨childSize, right, currentCell, initialValue, currentSelected, sameSize, outcomeEq, childTrace,
      currentRead, rootType, initialized, path, invalid⟩ |
    ⟨childSize, tailSize, right, middle, written, updated, sameSize, childTrace, write, remainingTrace⟩
  · subst outcome
    have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega) within
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, stable⟩ :=
      CellAwareInvocationBareAssignmentHeads.preserves_fault bridge functions extension head bare
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
        (children childSize childStrict) childTrace body (LocalLoop.controlType type)
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
      preservation, metadata, effect, reached, related, fault_post bridge reached stable⟩
  · subst outcome
    have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega) within
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, stable⟩ :=
      CellAwareInvocationBareAssignmentHeads.preserves_operands bridge functions extension head bare
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
        (children childSize childStrict) snapshot invalid childTrace body (LocalLoop.controlType type) invalidToken
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
      preservation, metadata, effect, reached, related,
      fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  · have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega) within
    have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega)) within
    obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
        effect, count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
      CellAwareInvocationBareAssignmentHeads.preserves_value bridge functions extension transport head bare
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
        (children childSize childStrict) snapshot childTrace write
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
        finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
      tail tailSize tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees slots) typed runtime covers sameLedger
        reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready remainingTrace
    have native := (continuation body (LocalLoop.controlType type)).wrap (by
      simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
        SourceCoreDataPlaces.shift] using evaluated)
    exact ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps,
      maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame, metadata.trans finalMetadata,
      effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

include transport unique bare assignmentTyped extension invalidToken in
theorem reflects (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults budget)
    (tail : CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages invocation faults
      administrative scope rest test postItems statements expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationForInitialBounds.ReflectsAt (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages invocation faults
      administrative scope (.assignValue assignment operator rhs :: rest) test postItems statements expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger
    initial admitted authority physical owner sameLocation ready completed
  have result := CellAwareInvocationBareAssignmentHeads.reflects_bounded bridge functions extension transport
    head bare environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
    budget children invalidToken completed within
  cases result with
  | fault snapshot trace same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
    cases same
    exact ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [_]], _, _, _, _,
      assignment_fault snapshot trace, .fault matched,
      finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, fault_post bridge reached stable⟩
  | operands snapshot trace currentRead rootType initialized path invalid same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
    cases same
    exact ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [_]], _, _, _, _,
      assignment_operands snapshot trace currentRead rootType initialized path invalid,
      .fault matched, finalHeaps, maps, worlds, preservation, metadata, effect, reached, related,
      fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  | success snapshot childTrace write middleHeaps maps worlds preservation metadata effect count typed reached related nextAdmitted strict remaining =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
        finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
      tail _ (Nat.le_trans (Nat.le_of_lt strict) within) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees _) typed runtime covers sameLedger
        reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready
        (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
          SourceCoreDataPlaces.shift] using remaining)
    exact ⟨Staging.Recursive.Size.stepSize [_, sourceSize], outcome, after, finalMap, finalWorld,
      prepend_assignment snapshot childTrace write trace, represented,
      finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
      metadata.trans finalMetadata, effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialAssignment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialProjectedAssignment
/-! Projected assignment sequences retain the reached key, getter, RHS and
write states before continuing through the same mixed scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialProjectedAssignment
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedImperativeFlow (fault_post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
  {expected : TypeSystem.Ty} {type : Ty}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}
  {rest : List ForItemForm} {body : Expr}
variable
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (sourceEq : invocation.source = bodyIndex.source)
  (unique : NodeOccurrencesUnique invocation.source)
  (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context certificate
    scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
  (projected : assignment.target.projections ≠ [])
  (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  (diagnostics : SourceAssignmentHasType invocation.source context assignment operator rhs →
    ∀ {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
      (initial : protocol.State initialIndex),
      ProtectedPlaceReachedDiagnostics.ShapeErrors (.initial compiled.compatible.checked) registry functions protocol
        invocation.source context certificate scope administrative environment assignment.target head.prepared operator head.invalid
        initial (fun reason token => faults (.semantic reason) token) head.shape)

include transport unique projected assignmentTyped extension faithful observations diagnostics in
theorem preserves (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults budget)
    (tail : CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages invocation faults
      administrative scope rest test postItems statements expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationForInitialBounds.PreservesAt (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages invocation faults
      administrative scope (.assignValue assignment operator rhs :: rest) test postItems statements expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger
    initial admitted authority physical owner sameLocation ready outcome after trace
  have splitTrace := CallableIndexedOwnedAdmittedStagedForInitializerProjectedInversion.projected_assignment projected trace
  cases splitTrace with
  | rootFault failed => exact False.elim (failed.excluded head.writable locals)
  | keysFault ready keyTrace =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
          preservation, metadata, effect, reached, related, stable⟩ :=
        CellAwareInvocationProjectedAssignmentHeads.preserves_key_fault
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children ready keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge reached stable⟩
  | getterFault keyTrace failed =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
          preservation, metadata, effect, reached, related, stable⟩ :=
        CellAwareInvocationProjectedAssignmentHeads.preserves_getter_fault
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children (diagnostics assignmentTyped initial)
          keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) failed body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  | rhsFault keyTrace snapshot childTrace =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
          preservation, metadata, effect, reached, related, stable⟩ :=
        CellAwareInvocationProjectedAssignmentHeads.preserves_fault
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot childTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge reached stable⟩
  | writeFault keyTrace snapshot childTrace failed =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
          preservation, metadata, effect, reached, related, stable⟩ :=
        CellAwareInvocationProjectedAssignmentHeads.preserves_write_fault
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children (diagnostics assignmentTyped initial)
          keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot childTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) failed body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  | success keyTrace snapshot childTrace write remainingTrace =>
      obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
          effect, count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
        CellAwareInvocationProjectedAssignmentHeads.preserves_value
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot childTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) write
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
          finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
        tail _ (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed runtime covers sameLedger
          reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready remainingTrace
      have native := (continuation body (LocalLoop.controlType type)).wrap (by
        simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
          SourceCoreDataPlaces.shift] using evaluated)
      exact ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps,
        maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame, metadata.trans finalMetadata,
        effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

include transport unique projected assignmentTyped extension faithful observations diagnostics in
theorem reflects (functionTypes : FunctionRuntimeViews functions) (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults budget)
    (tail : CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages invocation faults
      administrative scope rest test postItems statements expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationForInitialBounds.ReflectsAt (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages invocation faults
      administrative scope (.assignValue assignment operator rhs :: rest) test postItems statements expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger
    initial admitted authority physical owner sameLocation ready completed
  have result := CellAwareInvocationProjectedAssignmentHeads.reflects_bounded (compiled := compiled)
    (invocation := invocation)
    (context := context) (scope := scope) (administrative := administrative) bridge functions extension transport faithful observations
    head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
    budget children functionTypes
      (diagnostics assignmentTyped initial) completed within
  cases result with
  | keyFault ready keyTrace same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
      cases same
      refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [_]], _, _, _, _,
        CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready keyTrace, .fault matched,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge reached stable
  | getterFault keyTrace failed same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
      cases same
      refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [_]], _, _, _, _,
        CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_getter_fault projected keyTrace failed, .fault matched,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable
  | rhsFault keyTrace snapshot childTrace same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
      cases same
      refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [_, _]], _, _, _, _,
        CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_rhs_fault projected keyTrace snapshot childTrace, .fault matched,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge reached stable
  | writeFault keyTrace snapshot childTrace failed same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
      cases same
      refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [_, _]], _, _, _, _,
        CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_write_fault projected keyTrace snapshot childTrace failed, .fault matched,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable
  | success keyTrace snapshot childTrace write middleHeaps maps worlds preservation metadata effect count typed reached related nextAdmitted strict remaining =>
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
          finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
        tail _ (Nat.le_trans (Nat.le_of_lt strict) within)
          (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees _) typed runtime covers sameLedger
          reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready
          (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
      exact ⟨Staging.Recursive.Size.stepSize [_, _, sourceSize], outcome, after, finalMap, finalWorld,
        CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_projected_assignment projected keyTrace snapshot childTrace write trace, represented,
        finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
        metadata.trans finalMetadata, effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialProjectedAssignment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialBitNot
/-! Actual bare bit-not initializers preserve and reflect the same mixed heap.
The original invocation, seven administrative slots and remaining loop are
retained through the write, including unrelated generalized closure cells. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialBitNot
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedImperativeFlow (fault_post)
open CallableIndexedOwnedAdmittedStagedForInitializerSource
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
  {expected : TypeSystem.Ty} {type : Ty} {assignment : AssignmentResolution}
  {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}
  {rest : List ForItemForm} {body : Expr}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (head : CompatibleBitNotStatements.Head context scope assignment)
  (assignmentTyped : SourceBitNotAssignmentValid invocation.source context assignment)
  (errors : head.Errors (fun reason token => faults (.semantic reason) token))

include transport assignmentTyped errors in
theorem preserves (budget : Nat)
    (tail : CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment)
      bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      bodyIndex producer stages invocation faults administrative scope rest test postItems statements expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationForInitialBounds.PreservesAt (attachment := attachment)
      bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      bodyIndex producer stages invocation faults administrative scope (.assignBitNot assignment :: rest)
      test postItems statements expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger
    initial admitted authority physical owner sameLocation ready outcome after trace
  rcases CallableIndexedOwnedAdmittedStagedForInitializerSource.bitNot head.bare trace with
    ⟨reason, _sameSize, outcomeEq, heapEq, failed⟩ |
    ⟨tailSize, target, updated, written, sameSize, snapshot, write, remainingTrace⟩
  · subst outcome
    subst after
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
        preservation, effect, reached, related, stable⟩ :=
      CellAwareBareBitNotHeads.preserves_fault (values := .initial compiled.compatible.checked)
        (instances := GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        bridge functions transport head environments GeneralizedLocalDescriptorHeap.ordinary_cells
        heaps locals agrees initial admitted errors failed body (LocalLoop.controlType type)
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
      preservation, .refl _, effect, reached, related, fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  · have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
        effect, count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
      CellAwareBareBitNotHeads.preserves_value (values := .initial compiled.compatible.checked)
        (instances := GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        bridge functions transport head environments GeneralizedLocalDescriptorHeap.ordinary_cells
        heaps locals agrees actualTyped initial admitted assignmentTyped snapshot write
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
        finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
      tail tailSize tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees slots) typed runtime covers sameLedger
        reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready remainingTrace
    have native := (continuation body (LocalLoop.controlType type)).wrap (by
      simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
        SourceCoreDataPlaces.shift] using evaluated)
    exact ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps,
      maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame, metadata.trans finalMetadata,
      effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

include transport assignmentTyped errors in
theorem reflects (budget : Nat)
    (tail : CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment)
      bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      bodyIndex producer stages invocation faults administrative scope rest test postItems statements expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationForInitialBounds.ReflectsAt (attachment := attachment)
      bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      bodyIndex producer stages invocation faults administrative scope (.assignBitNot assignment :: rest)
      test postItems statements expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger
    initial admitted authority physical owner sameLocation ready completed
  have result := CellAwareBareBitNotHeads.reflects_bounded (values := .initial compiled.compatible.checked)
        (instances := GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
    bridge functions transport head environments GeneralizedLocalDescriptorHeap.ordinary_cells
    heaps locals agrees actualTyped initial admitted assignmentTyped errors completed
  cases result with
  | fault trace same matched finalHeaps maps worlds preservation effect reached related stable =>
    cases same
    exact ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize []], _, _, _, _,
      bitNot_fault head.bare trace, .fault matched,
      finalHeaps, maps, worlds, preservation, .refl _, effect, reached, related, fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  | success snapshot write middleHeaps maps worlds preservation metadata effect count typed reached related nextAdmitted strict remaining =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
        finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
      tail _ (Nat.le_trans (Nat.le_of_lt strict) within) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees _) typed runtime covers sameLedger
        reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready
        (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
          SourceCoreDataPlaces.shift] using remaining)
    exact ⟨Staging.Recursive.Size.stepSize [sourceSize], outcome, after, finalMap, finalWorld,
      prepend_bitNot snapshot write trace, represented,
      finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
      metadata.trans finalMetadata, effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialBitNot
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialProjectedBitNot
/-! Projected unary headers execute the ordered keys, getter and write
before continuing through the same actual invocation and mixed scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialProjectedBitNot
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedImperativeFlow (fault_post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
  {expected : TypeSystem.Ty} {type : Ty}
  {assignment : AssignmentResolution}
  {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}
  {rest : List ForItemForm} {body : Expr}
variable
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (sourceEq : invocation.source = bodyIndex.source)
  (unique : NodeOccurrencesUnique invocation.source)
  (head : CompatibleProjectedBitNotStatements.Head (.initial compiled.compatible.checked) invocation.source context certificate
    scope administrative compiled.indexed.layouts.definitions assignment)
  (projected : assignment.target.projections ≠ [])
  (assignmentTyped : SourceBitNotAssignmentValid invocation.source context assignment)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  (diagnostics : SourceBitNotAssignmentValid invocation.source context assignment →
    ∀ {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
      (initial : protocol.State initialIndex),
      CompatibleProjectedBitNotStatements.Head.ReachedErrors
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        functions protocol head environment initial (fun reason token => faults (.semantic reason) token)
        (registry := registry))

include transport unique projected assignmentTyped extension faithful observations diagnostics in
theorem preserves (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults budget)
    (tail : CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages invocation faults
      administrative scope rest test postItems statements expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationForInitialBounds.PreservesAt (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages invocation faults
      administrative scope (.assignBitNot assignment :: rest) test postItems statements expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger
    initial admitted authority physical owner sameLocation ready outcome after trace
  have splitTrace := CallableIndexedOwnedAdmittedStagedForInitializerProjectedBitNotInversion.projected_bitNot projected trace
  cases splitTrace with
  | rootFault failed => exact False.elim (failed.excluded head.writable locals)
  | keysFault ready keyTrace =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
          preservation, metadata, effect, reached, related, stable⟩ :=
        CellAwareInvocationProjectedBitNotHeads.preserves_key_fault
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children ready keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge reached stable⟩
  | getterFault keyTrace failed =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
          preservation, metadata, effect, reached, related, stable⟩ :=
        CellAwareInvocationProjectedBitNotHeads.preserves_getter_fault
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children (diagnostics assignmentTyped initial)
          keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) failed body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  | success keyTrace snapshot write remainingTrace =>
      obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
          effect, count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
        CellAwareInvocationProjectedBitNotHeads.preserves_value
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot write
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
          finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
        tail _ (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed runtime covers sameLedger
          reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready remainingTrace
      have native := (continuation body (LocalLoop.controlType type)).wrap (by
        simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
          SourceCoreDataPlaces.shift] using evaluated)
      exact ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps,
        maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame, metadata.trans finalMetadata,
        effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

include transport unique projected assignmentTyped extension faithful observations diagnostics in
theorem reflects (functionTypes : FunctionRuntimeViews functions) (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults budget)
    (tail : CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages invocation faults
      administrative scope rest test postItems statements expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationForInitialBounds.ReflectsAt (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages invocation faults
      administrative scope (.assignBitNot assignment :: rest) test postItems statements expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger
    initial admitted authority physical owner sameLocation ready completed
  have result := CellAwareInvocationProjectedBitNotHeads.reflects_bounded (compiled := compiled)
    (invocation := invocation)
    (context := context) (scope := scope) (administrative := administrative) bridge functions extension transport faithful observations
    head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
    budget children functionTypes
      (diagnostics assignmentTyped initial) completed within
  cases result with
  | keyFault ready keyTrace same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
      cases same
      refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [_]], _, _, _, _,
        CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_bitNot_keys_fault projected ready keyTrace, .fault matched,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge reached stable
  | getterFault keyTrace failed same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
      cases same
      refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [_]], _, _, _, _,
        CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_bitNot_getter_fault projected keyTrace failed, .fault matched,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable
  | success keyTrace snapshot write middleHeaps maps worlds preservation metadata effect count typed reached related nextAdmitted strict remaining =>
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
          finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
        tail _ (Nat.le_trans (Nat.le_of_lt strict) within)
          (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees _) typed runtime covers sameLedger
          reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready
          (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
      exact ⟨Staging.Recursive.Size.stepSize [_, sourceSize], outcome, after, finalMap, finalWorld,
        CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_projected_bitNot projected keyTrace snapshot write trace, represented,
        finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
        metadata.trans finalMetadata, effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialProjectedBitNot
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForState
/-! A live loop carries its actual self closure, the mixed Source heap and the
same caller frame. Child computation keeps its reached protocol state while
transporting every generalized descriptor through its concrete effect. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForState
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open TypedLexicalWhile (installedStore installedWorld)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index whole bodyRelation}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))

structure State (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (administrative actualContext : Core.Context) (environment : Dynamic.Environment)
    (canonical actual : Environment) (location : Location) (type : Ty)
    (condition body post : Expr) (reason : Word)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) where
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    mapping world administrative scope environment canonical whole.indexed.layouts.definitions
  heaps : GenericHeap.CellHeapRepresents
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)) mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions
  authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
    bodyIndex.owner bodyIndex.active mapping world heap store environment
  physical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole bodyIndex context scope canonical mapping world heap store environment
  owner : CallableIndexedOwnedFunctionValues.OwnedKey keys
  ownerAt : owner.key.frameLocation = physical.location
  ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native
  selfTyped : world[location]? = some (OptionalCell.cellType (LocalLoop.functionType type))
  selfRead : store.read? location = some (.inRight .unit
    (LocalLoop.installedClosure type condition body post reason location actual))
  selfUnmapped : location ∉ mapping
  retained : protocol.State ⟨scope,mapping,world,heap,store,canonical⟩

variable {producer} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {location : Location} {type : Ty}
  {condition body post : Expr} {reason : Word}
  {mapping nextMap : LocationMap} {world nextWorld : StoreTyping}
  {heap after : Dynamic.Heap} {store finalStore : Store}

/-- Retain the exact child post-state, rather than reconstructing an unrelated
state with the same heap. The loop's recursive closure remains unchanged. -/
def State.reach
    (state : State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type condition body post reason mapping world heap store)
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)) nextMap nextWorld after finalStore)
    (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
      mapping world heap store nextMap nextWorld after finalStore)
    (frame : AdministrativePreserved mapping store nextMap finalStore)
    (reached : protocol.State ⟨scope,nextMap,nextWorld,after,finalStore,canonical⟩) :
    State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type condition body post reason nextMap nextWorld after finalStore :=
  { environments := state.environments.extend effect.maps effect.worlds,
    heaps := heaps, locals := state.locals.mono effect.metadata, actualTyped := state.actualTyped.weaken effect.worlds,
    authority := state.authority.transport effect, physical := state.physical.transport effect frame,
    owner := state.owner, ownerAt := state.ownerAt, ready := state.ready,
    selfTyped := effect.worlds.lookup state.selfTyped,
    selfRead := (TypedLexicalWhile.retain state.selfUnmapped state.selfRead frame).2,
    selfUnmapped := (TypedLexicalWhile.retain state.selfUnmapped state.selfRead frame).1,
    retained := reached }

variable (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    mapping world administrative scope environment canonical whole.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)) mapping world heap store)
  (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
    bodyIndex.owner bodyIndex.active mapping world heap store environment)
  (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole bodyIndex context scope canonical mapping world heap store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (ownerAt : owner.key.frameLocation = physical.location)
  (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
  (typed : HasType actualContext (LocalLoop.iterate type condition body post reason)
    (LocalLoop.resultType type) whole.indexed.layouts.definitions)
  (initial : protocol.State ⟨scope,mapping,world,heap,store,canonical⟩)

/-- Installing the real for self cell changes only administrative storage. -/
def install : State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
    store.length type condition body post reason mapping (installedWorld world type) heap
    (installedStore store type condition body post reason actual) := by
  have allocation := CellAwareForAllocation.install reason heaps actualTyped typed
  have worlds := allocation.2.1
  have frame := allocation.2.2.2.2.2.1
  have effect := allocation.2.2.2.2.2.2
  exact {
    environments := environments.extend (.refl mapping) worlds,
    heaps := allocation.1, locals := locals, actualTyped := actualTyped.weaken worlds,
    authority := authority.transport effect, physical := physical.transport effect frame,
    owner := owner, ownerAt := ownerAt, ready := ready,
    selfTyped := allocation.2.2.2.1, selfRead := allocation.2.2.2.2.1,
    selfUnmapped := allocation.2.2.1,
    retained := transport.extend initial (.refl mapping) worlds frame (.refl heap) }

theorem install_related : protocol.Relates initial
    (install transport environments heaps locals actualTyped authority physical owner ownerAt ready typed initial).retained := by
  unfold install
  apply transport.related

theorem install_records : protocol.records
    (install transport environments heaps locals actualTyped authority physical owner ownerAt ready typed initial).retained =
    protocol.records initial := by
  unfold install
  apply transport.records_eq

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForState
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForEdges
/-! Actual condition and body children execute under the installed self cell.
The reached mixed heap, exact descriptor effect and caller admission survive
both Source preservation and native reflection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForEdges
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds (PostAdmission)
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CellAwareLoopState (Progress)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    projects compiled.indexed.layouts.definitions)
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) callerProtocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  {administrative actualContext : Core.Context} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {location : Location} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before after : Dynamic.Heap} {store : Store}
  {certificate : GenericExpressionMeaning.Certificate} {body : Expr}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

theorem condition_preserves_at {size : Nat}
    (meaning : CellAwareInvocationExpressionBounds.PreservesAt (attachment := attachment) bridge context model bodyIndex stages invocation certificate faults size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : invocation.source.lookupExpression? condition = some node)
    (typed : ExpressionHasType invocation.source context condition node.type)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type (conditionCode.rename ξ) body postCode selfReason mapping world before store)
    (ready : Admission bridge context state.retained)
    {outcome : Staging.Recursive.Outcome}
    (trace : Staging.Recursive.Size.Expression program stages size invocation context environment before condition outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
        (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
        location type (conditionCode.rename ξ) body postCode selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        PostAdmission bridge context node.type outcome reached.retained := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, preserved, metadata, effect, last, retained, post⟩ :=
    meaning tree found typed state.environments state.heaps state.locals actualAgrees
      (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped)) state.retained ready state.authority state.physical state.owner state.ownerAt trace
  have progress : Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata, effect⟩
  let reached : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type (conditionCode.rename ξ) body postCode selfReason finalMap finalWorld after finalStore :=
    state.reach heaps effect preserved last
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated,
    related, progress, reached, retained, post⟩

theorem condition_reflects_at {size : Nat}
    (reflection : CellAwareInvocationExpressionBounds.ReflectsAt (attachment := attachment) bridge context model bodyIndex stages invocation certificate faults size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : invocation.source.lookupExpression? condition = some node)
    (typed : ExpressionHasType invocation.source context condition node.type)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type (conditionCode.rename ξ) body postCode selfReason mapping world before store)
    (ready : Admission bridge context state.retained)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before condition outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
        location type (conditionCode.rename ξ) body postCode selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        PostAdmission bridge context node.type outcome reached.retained := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, preserved, metadata, effect, last, retained, post⟩ :=
    reflection tree found typed state.environments state.heaps state.locals actualAgrees
      (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped)) state.retained ready state.authority state.physical state.owner state.ownerAt
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated)
  have progress : Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata, effect⟩
  let reached : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type (conditionCode.rename ξ) body postCode selfReason finalMap finalWorld after finalStore :=
    state.reach heaps effect preserved last
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, progress, reached, retained, post⟩



theorem body_preserves_at {budget size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope false statements expected type code budget)
    (within : size ≤ budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type conditionCode (code.rename ξ) postCode selfReason mapping world before store)
    (runtime : Dynamic.SourceRuntimeValid program context (bodyIndex.source))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = bodyIndex.compilation.solvedRequirements)
    (typed : ProtectedStateImperativeTypedSourceSites.Statements (bodyIndex.source) context statements)
    (ready : Admission bridge context state.retained)
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome}
    (trace : Staging.Recursive.Size.StatementsIn program stages false size invocation context environment before statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
        (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
        location type conditionCode (code.rename ξ) postCode selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        Post bridge context expected outcome reached.retained := by
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)))
      canonical (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, preserved, metadata, effect, last, retained, post⟩ :=
    correct size within state.environments state.heaps state.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped)))
      runtime covers sameLedger typed state.retained ready state.authority state.physical state.owner state.ownerAt state.ready trace
  have progress : Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata, effect⟩
  let reached : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type conditionCode (code.rename ξ) postCode selfReason finalMap finalWorld after finalStore :=
    state.reach heaps effect preserved last
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode,
      Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated,
    represented, progress, reached, retained, post⟩

theorem body_reflects_at {budget size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope false statements expected type code budget)
    (within : size ≤ budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type conditionCode (code.rename ξ) postCode selfReason mapping world before store)
    (runtime : Dynamic.SourceRuntimeValid program context (bodyIndex.source))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = bodyIndex.compilation.solvedRequirements)
    (typed : ProtectedStateImperativeTypedSourceSites.Statements (bodyIndex.source) context statements)
    (ready : Admission bridge context state.retained)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program stages false sourceSize invocation context environment before statements finalContext outcome after ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
        location type conditionCode (code.rename ξ) postCode selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        Post bridge context expected outcome reached.retained := by
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)))
      canonical (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, preserved, metadata, effect, last, retained, post⟩ :=
    correct size within state.environments state.heaps state.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped)))
      runtime covers sameLedger typed state.retained ready state.authority state.physical state.owner state.ownerAt state.ready
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode,
        Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated)
  have progress : Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata, effect⟩
  let reached : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type conditionCode (code.rename ξ) postCode selfReason finalMap finalWorld after finalStore :=
    state.reach heaps effect preserved last
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace,
    represented, progress, reached, retained, post⟩


end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForEdges
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostEdges
/-! Actual condition and body children execute under the installed self cell.
The reached mixed heap, exact descriptor effect and caller admission survive
both Source preservation and native reflection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostEdges
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds (PostAdmission)
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CellAwareLoopState (Progress)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    projects compiled.indexed.layouts.definitions)
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) callerProtocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  {administrative actualContext : Core.Context} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {location : Location} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before after : Dynamic.Heap} {store : Store}
  {certificate : GenericExpressionMeaning.Certificate} {body : Expr}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

open CallableIndexedOwnedAdmittedStagedForPostContracts (restoredOutcome)

theorem preserves_at {continuing : Bool} {budget size : Nat} {items : List ForItemForm} {expected : TypeSystem.Ty}
    (correct : CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope items expected type code budget)
    (within : size ≤ budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type conditionCode body (code.rename ξ) selfReason mapping world before store)
    (runtime : Dynamic.SourceRuntimeValid program context (bodyIndex.source))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = bodyIndex.compilation.solvedRequirements)
    (postTyped : ∃ control final, ForItemsHaveType (bodyIndex.source) control context items final)
    (ready : Admission bridge context state.retained)
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.ForItemsOutcome}
    (trace : Staging.Recursive.Size.ForItems program stages size invocation context environment before items finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (TypedImperativeFor.postValues type location continuing ++ actual) store
        (ForLoop.postCode (code.rename ξ)) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults (restoredOutcome environment outcome) value ∧
      Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
        location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        Post bridge context expected (restoredOutcome environment outcome) reached.retained := by
  have postAgrees : EnvironmentsAgree ((fun index => index + 6).comp ξ) canonical
      (TypedImperativeFor.postValues type location continuing ++ actual) :=
    TypedImperativeFor.postValues_agree agrees type location continuing
  obtain ⟨postContext, actualPostTyped⟩ := TypedImperativeFor.postValues_typed continuing state.selfTyped state.actualTyped
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, preserved, metadata, effect, last, retained, post⟩ :=
    correct size within state.environments state.heaps state.locals postAgrees actualPostTyped
      runtime covers sameLedger postTyped state.retained ready state.authority state.physical state.owner state.ownerAt state.ready trace
  have progress : Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata, effect⟩
  let reached : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore :=
    state.reach heaps effect preserved last
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [TypedImperativeFor.post_rename] using evaluated,
    represented, progress, reached, retained, post⟩

theorem reflects_at {continuing : Bool} {budget size : Nat} {items : List ForItemForm} {expected : TypeSystem.Ty}
    (correct : CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope items expected type code budget)
    (within : size ≤ budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type conditionCode body (code.rename ξ) selfReason mapping world before store)
    (runtime : Dynamic.SourceRuntimeValid program context (bodyIndex.source))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = bodyIndex.compilation.solvedRequirements)
    (postTyped : ∃ control final, ForItemsHaveType (bodyIndex.source) control context items final)
    (ready : Admission bridge context state.retained)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (TypedImperativeFor.postValues type location continuing ++ actual) store
      (ForLoop.postCode (code.rename ξ)) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.ForItems program stages sourceSize invocation context environment before items finalContext outcome after ∧
      Represents model finalMap finalWorld false expected type faults (restoredOutcome environment outcome) value ∧
      Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
        location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        Post bridge context expected (restoredOutcome environment outcome) reached.retained := by
  have postAgrees : EnvironmentsAgree ((fun index => index + 6).comp ξ) canonical
      (TypedImperativeFor.postValues type location continuing ++ actual) :=
    TypedImperativeFor.postValues_agree agrees type location continuing
  obtain ⟨postContext, actualPostTyped⟩ := TypedImperativeFor.postValues_typed continuing state.selfTyped state.actualTyped
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, preserved, metadata, effect, last, retained, post⟩ :=
    correct size within state.environments state.heaps state.locals postAgrees actualPostTyped
      runtime covers sameLedger postTyped state.retained ready state.authority state.physical state.owner state.ownerAt state.ready
      (by simpa only [TypedImperativeFor.post_rename] using evaluated)
  have progress : Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata, effect⟩
  let reached : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore :=
    state.reach heaps effect preserved last
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace,
    represented, progress, reached, retained, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostEdges
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForIterations
/-! Actual condition and body children execute under the installed self cell.
The reached mixed heap, exact descriptor effect and caller admission survive
both Source preservation and native reflection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForIterations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds (PostAdmission)
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CellAwareLoopState (Progress)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    projects compiled.indexed.layouts.definitions)
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) callerProtocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  {administrative actualContext : Core.Context} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {location : Location} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before after : Dynamic.Heap} {store : Store}
  {certificate : GenericExpressionMeaning.Certificate} {body : Expr}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

open CellAwareInvocationForEdges
variable {condition : ExpressionId} {node : ExpressionNode}
  {statements : List StatementId} {expected : TypeSystem.Ty} {post : List ForItemForm}

theorem reflects {budget : Nat}
    (children : ∀ childSize, childSize < budget → CellAwareInvocationExpressionBounds.ReflectsAt (attachment := attachment) bridge context model bodyIndex stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? condition = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context condition node.type)
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (correct : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope false statements expected type code budget)
    (postCorrect : CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope post expected type postCode budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (booleans : ∀ {mapping world sourceValue nativeValue},
      model.Represents mapping world .bool sourceValue nativeValue .bool →
      ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
    (runtime : Dynamic.SourceRuntimeValid program context (bodyIndex.source))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = bodyIndex.compilation.solvedRequirements)
    (bodyTyped : ProtectedStateImperativeTypedSourceSites.Statements (bodyIndex.source) context statements)
    (postTyped : ∃ control final, ForItemsHaveType (bodyIndex.source) control context post final) :
    ∀ size, size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
      {store finalStore : Store} {value : Value},
    ∀ state : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store,
      Admission bridge context state.retained →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.ForLoop program stages sourceSize invocation context environment before condition post statements outcome after ∧
        Represents model finalMap finalWorld false expected type faults outcome value ∧
        Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
        location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧ Post bridge context expected outcome reached.retained := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro bounded mapping world before store finalStore value state ready evaluation
    obtain ⟨conditionSize, conditionStore, conditionValue, conditionSmaller, conditionEval⟩ := evaluation.bind_computation
    obtain ⟨conditionSourceSize, conditionOutcome, conditionHeap, conditionMap, conditionWorld,
        conditionTrace, conditionRelated, conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
      condition_reflects_at bridge model producer (children _ (Nat.lt_of_lt_of_le conditionSmaller bounded))
        tree found typed agrees state ready conditionEval
    cases conditionRelated with
    | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_failure conditionEval.sound)
      exact ⟨_, _, conditionHeap, conditionMap, conditionWorld, .testFault conditionTrace, .fault matched,
        conditionProgress, conditionState, conditionRetained, conditionPost.at_fault_type⟩
    | value payload =>
      rw [nodeType] at payload
      obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
      subst sameSource
      subst sameCore
      cases boolean with
      | false =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_false conditionEval.sound)
        exact ⟨_, _, conditionHeap, conditionMap, conditionWorld, .finished conditionTrace, .fallthrough environment (.inl rfl),
          conditionProgress, conditionState, conditionRetained, conditionPost.at_value.2⟩
      | true =>
        obtain ⟨branchSize, branchSmaller, branch⟩ := evaluation.loop_true_branch conditionEval.sound
        obtain ⟨bodySize, bodyStore, bodyValue, bodySmaller, bodyEval⟩ := branch.bind_computation
        obtain ⟨bodySourceSize, bodyContext, bodyOutcome, bodyHeap, bodyMap, bodyWorld, bodyTrace,
            bodyRelated, bodyProgress, bodyState, bodyRetained, bodyPost⟩ :=
          body_reflects_at bridge model producer correct
            (Nat.le_trans (Nat.le_of_lt bodySmaller) (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded))
            agrees conditionState runtime covers sameLedger bodyTyped conditionPost.at_value.2 bodyEval
        have progress := conditionProgress.trans bodyProgress
        cases bodyRelated with
        | fault matched =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
            (Core.LoopExecution.body_failure conditionEval.sound bodyEval.sound)
          exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .bodyFailure conditionTrace bodyTrace, .fault matched,
            progress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
        | returned payload =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
            (Core.LoopExecution.body_returned conditionEval.sound bodyEval.sound)
          exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .returnedFromBody conditionTrace bodyTrace, .returned payload,
            progress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
        | fallthrough innerEnvironment allowed =>
          obtain ⟨postSize, postStore, postValue, postSmaller, postEval⟩ :=
            RecursiveNamedForContracts.post_computation_size false branch bodyEval.sound
          obtain ⟨postSourceSize, postContext, postOutcome, postHeap, postMap, postWorld, postTrace,
              postRelated, postProgress, postState, postRetained, postPost⟩ :=
            CellAwareInvocationForPostEdges.reflects_at (continuing := false) bridge model producer postCorrect
              (Nat.le_trans (Nat.le_of_lt postSmaller) (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded))
              agrees bodyState runtime covers sameLedger postTyped bodyPost postEval
          cases postOutcome with
          | fault failure =>
            cases postRelated with
            | fault matched =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (ForLoop.body_fallthrough_post_fault conditionEval.sound bodyEval.sound postEval.sound)
              exact ⟨_, _, postHeap, postMap, postWorld, .postFailure conditionTrace bodyTrace postTrace,
                .fault matched, progress.trans postProgress, postState,
                callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained, postPost⟩
          | done postEnvironment =>
            cases postRelated with
            | fallthrough _ _ =>
              have prefixProgress := progress.trans postProgress
              obtain ⟨nextSize, smaller, nextEval⟩ :=
                ForLoop.next_fallthrough branch bodyEval.sound postEval.sound postState.selfRead
              obtain ⟨nextSourceSize, outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress,
                  finalState, finalRetained, finalPost⟩ :=
                ih nextSize (Nat.lt_trans smaller branchSmaller)
                  (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) bounded) postState postPost nextEval
              exact ⟨_, _, after, finalMap, finalWorld, .iterate conditionTrace bodyTrace postTrace nextTrace, related,
                prefixProgress.trans nextProgress, finalState,
                callerProtocol.trans (callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩

        | breaking innerEnvironment =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
            (Core.LoopExecution.body_breaking conditionEval.sound bodyEval.sound)
          exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .forBreakFromBody conditionTrace bodyTrace,
            .fallthrough environment (.inl rfl), progress, bodyState,
            callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
        | continuing innerEnvironment =>
          obtain ⟨postSize, postStore, postValue, postSmaller, postEval⟩ :=
            RecursiveNamedForContracts.post_computation_size true branch bodyEval.sound
          obtain ⟨postSourceSize, postContext, postOutcome, postHeap, postMap, postWorld, postTrace,
              postRelated, postProgress, postState, postRetained, postPost⟩ :=
            CellAwareInvocationForPostEdges.reflects_at (continuing := true) bridge model producer postCorrect
              (Nat.le_trans (Nat.le_of_lt postSmaller) (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded))
              agrees bodyState runtime covers sameLedger postTyped bodyPost postEval
          cases postOutcome with
          | fault failure =>
            cases postRelated with
            | fault matched =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (ForLoop.body_continuing_post_fault conditionEval.sound bodyEval.sound postEval.sound)
              exact ⟨_, _, postHeap, postMap, postWorld, .continuePostFailure conditionTrace bodyTrace postTrace,
                .fault matched, progress.trans postProgress, postState,
                callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained, postPost⟩
          | done postEnvironment =>
            cases postRelated with
            | fallthrough _ _ =>
              have prefixProgress := progress.trans postProgress
              obtain ⟨nextSize, smaller, nextEval⟩ :=
                ForLoop.next_continuing branch bodyEval.sound postEval.sound postState.selfRead
              obtain ⟨nextSourceSize, outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress,
                  finalState, finalRetained, finalPost⟩ :=
                ih nextSize (Nat.lt_trans smaller branchSmaller)
                  (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) bounded) postState postPost nextEval
              exact ⟨_, _, after, finalMap, finalWorld, .continueIterate conditionTrace bodyTrace postTrace nextTrace, related,
                prefixProgress.trans nextProgress, finalState,
                callerProtocol.trans (callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩

theorem preserves {budget : Nat}
    (children : ∀ childSize, childSize < budget → CellAwareInvocationExpressionBounds.PreservesAt (attachment := attachment) bridge context model bodyIndex stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? condition = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context condition node.type)
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (correct : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope false statements expected type code budget)
    (postCorrect : CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope post expected type postCode budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (booleans : ∀ {mapping world sourceValue nativeValue},
      model.Represents mapping world .bool sourceValue nativeValue .bool →
      ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
    (runtime : Dynamic.SourceRuntimeValid program context (bodyIndex.source))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = bodyIndex.compilation.solvedRequirements)
    (bodyTyped : ProtectedStateImperativeTypedSourceSites.Statements (bodyIndex.source) context statements)
    (postTyped : ∃ control final, ForItemsHaveType (bodyIndex.source) control context post final) :
    ∀ size, size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
      {store : Store} {outcome : Staging.Recursive.BodyOutcome},
    ∀ state : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store,
      Admission bridge context state.retained →
      Staging.Recursive.Size.ForLoop program stages size invocation context environment before condition post statements outcome after →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        Represents model finalMap finalWorld false expected type faults outcome value ∧
        Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareInvocationForState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
        location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧ Post bridge context expected outcome reached.retained := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro bounded mapping world before after store outcome state ready trace
    cases trace with
    | finished testTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
          cases sameSource
          subst sameCore
          exact ⟨_, conditionStore, conditionMap, conditionWorld, Core.LoopExecution.condition_false conditionEval,
            .fallthrough environment (.inl rfl), conditionProgress, conditionState, conditionRetained, conditionPost.at_value.2⟩
    | testFault testTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | fault matched =>
          exact ⟨_, conditionStore, conditionMap, conditionWorld, Core.LoopExecution.condition_failure conditionEval,
            .fault matched, conditionProgress, conditionState, conditionRetained, conditionPost.at_fault_type⟩
    | returnedFromBody testTrace bodyTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge model producer correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees conditionState runtime covers sameLedger bodyTyped conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | returned payload =>
            exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_returned conditionEval bodyEval, .returned payload,
              conditionProgress.trans bodyProgress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
    | forBreakFromBody testTrace bodyTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge model producer correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees conditionState runtime covers sameLedger bodyTyped conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | breaking innerEnvironment =>
            exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_breaking conditionEval bodyEval, .fallthrough environment (.inl rfl),
              conditionProgress.trans bodyProgress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
    | bodyFailure testTrace bodyTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge model producer correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees conditionState runtime covers sameLedger bodyTyped conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | fault matched =>
            exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_failure conditionEval bodyEval, .fault matched,
              conditionProgress.trans bodyProgress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
    | postFailure testTrace bodyTrace postTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge model producer correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees conditionState runtime covers sameLedger bodyTyped conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | fallthrough innerEnvironment allowed =>
            have progress := conditionProgress.trans bodyProgress
            obtain ⟨postValue, postStore, postMap, postWorld, postEval, postRelated, postProgress,
                postState, postRetained, postPost⟩ :=
              CellAwareInvocationForPostEdges.preserves_at (continuing := false) bridge model producer postCorrect
                (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                agrees bodyState runtime covers sameLedger postTyped bodyPost postTrace
            cases postRelated with
            | fault matched =>
              exact ⟨_, postStore, postMap, postWorld,
                ForLoop.body_fallthrough_post_fault conditionEval bodyEval postEval, .fault matched,
                progress.trans postProgress, postState,
                callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained, postPost⟩
    | iterate testTrace bodyTrace postTrace next =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge model producer correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees conditionState runtime covers sameLedger bodyTyped conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | fallthrough innerEnvironment allowed =>
            have progress := conditionProgress.trans bodyProgress
            obtain ⟨postValue, postStore, postMap, postWorld, postEval, postRelated, postProgress,
                postState, postRetained, postPost⟩ :=
              CellAwareInvocationForPostEdges.preserves_at (continuing := false) bridge model producer postCorrect
                (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                agrees bodyState runtime covers sameLedger postTyped bodyPost postTrace
            cases postRelated with
            | fallthrough _ _ =>
              have prefixProgress := progress.trans postProgress
              obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress,
                  finalState, finalRetained, finalPost⟩ :=
                ih _ (Staging.Recursive.Size.child_lt_stepSize (by simp))
                  (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                  postState postPost next
              exact ⟨result, finalStore, finalMap, finalWorld,
                ForLoop.body_fallthrough conditionEval bodyEval postEval postState.selfRead nativeTrace,
                related, prefixProgress.trans finalProgress, finalState,
                callerProtocol.trans (callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩

    | continuePostFailure testTrace bodyTrace postTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge model producer correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees conditionState runtime covers sameLedger bodyTyped conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | continuing innerEnvironment =>
            have progress := conditionProgress.trans bodyProgress
            obtain ⟨postValue, postStore, postMap, postWorld, postEval, postRelated, postProgress,
                postState, postRetained, postPost⟩ :=
              CellAwareInvocationForPostEdges.preserves_at (continuing := true) bridge model producer postCorrect
                (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                agrees bodyState runtime covers sameLedger postTyped bodyPost postTrace
            cases postRelated with
            | fault matched =>
              exact ⟨_, postStore, postMap, postWorld,
                ForLoop.body_continuing_post_fault conditionEval bodyEval postEval, .fault matched,
                progress.trans postProgress, postState,
                callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained, postPost⟩
    | continueIterate testTrace bodyTrace postTrace next =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge model producer correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees conditionState runtime covers sameLedger bodyTyped conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | continuing innerEnvironment =>
            have progress := conditionProgress.trans bodyProgress
            obtain ⟨postValue, postStore, postMap, postWorld, postEval, postRelated, postProgress,
                postState, postRetained, postPost⟩ :=
              CellAwareInvocationForPostEdges.preserves_at (continuing := true) bridge model producer postCorrect
                (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                agrees bodyState runtime covers sameLedger postTyped bodyPost postTrace
            cases postRelated with
            | fallthrough _ _ =>
              have prefixProgress := progress.trans postProgress
              obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress,
                  finalState, finalRetained, finalPost⟩ :=
                ih _ (Staging.Recursive.Size.child_lt_stepSize (by simp))
                  (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                  postState postPost next
              exact ⟨result, finalStore, finalMap, finalWorld,
                ForLoop.body_continuing conditionEval bodyEval postEval postState.selfRead nativeTrace,
                related, prefixProgress.trans finalProgress, finalState,
                callerProtocol.trans (callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForIterations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForEntry
/-! The actual for-loop prelude supplies its mixed state and unchanged caller
records. Its code typing follows from the real lexical environment renaming. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForEntry
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open TypedLexicalWhile (installedStore installedWorld)
open CellAwareInvocationForState (State)
open CellAwareLoopState (Progress)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index whole bodyRelation}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {type : Ty} {condition body post : Expr} {reason : Word}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {embedding : Renaming}

include transport in
theorem install
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)) mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
      bodyIndex.owner bodyIndex.active mapping world heap store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole bodyIndex context scope canonical mapping world heap store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerAt : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type condition body post reason) (LocalLoop.resultType type) whole.indexed.layouts.definitions)
    (initial : protocol.State ⟨scope,mapping,world,heap,store,canonical⟩) :
    ∃ state : State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      store.length type (condition.rename embedding) (body.rename embedding) (post.rename embedding) reason mapping (installedWorld world type) heap
      (installedStore store type (condition.rename embedding) (body.rename embedding) (post.rename embedding) reason actual),
    Progress model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment) heap heap mapping mapping world (installedWorld world type)
      store (installedStore store type (condition.rename embedding) (body.rename embedding) (post.rename embedding) reason actual) ∧
    protocol.Relates initial state.retained ∧ protocol.records state.retained = protocol.records initial := by
  have actualCode := typed.rename (TypedLexicalWhile.environment_respects environments.runtime_hasTypes actualTyped agrees)
  rw [LoopRenaming.iterate] at actualCode
  let state := CellAwareInvocationForState.install transport environments heaps locals actualTyped authority physical owner ownerAt ready actualCode initial
  have allocation := CellAwareForAllocation.install reason heaps actualTyped actualCode
  refine ⟨state, ⟨allocation.1, .refl mapping, allocation.2.1, allocation.2.2.2.2.2.1, .refl heap,
    allocation.2.2.2.2.2.2⟩, ?_, ?_⟩
  · exact CellAwareInvocationForState.install_related transport environments heaps locals actualTyped authority physical owner ownerAt ready actualCode initial
  · exact CellAwareInvocationForState.install_records transport environments heaps locals actualTyped authority physical owner ownerAt ready actualCode initial

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForEntry
end
