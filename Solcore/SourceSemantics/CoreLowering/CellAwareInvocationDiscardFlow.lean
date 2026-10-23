import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationFlowBounds
import Solcore.SourceSemantics.CoreLowering.LoopRenaming
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedDiscardSourceBodyInversion
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping

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
