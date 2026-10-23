import Solcore.SourceSemantics.Staging.RecursiveProjectedTargetFacts
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationProjectedAssignmentPreservation
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationProjectedAssignmentReflection
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerProjectedInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerProjectedSource
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedForItemsTyping
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedImperativeFlow

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
