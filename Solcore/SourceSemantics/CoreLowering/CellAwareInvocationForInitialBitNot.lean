import Solcore.SourceSemantics.CoreLowering.CellAwareBareBitNotHeads
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerBitNotSource
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerBitNotInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedImperativeFlow

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
