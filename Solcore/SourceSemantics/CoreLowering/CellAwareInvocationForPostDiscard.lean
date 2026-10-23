import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostBounds
import Solcore.SourceSemantics.CoreLowering.LoopRenaming
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedForItemsTyping

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
