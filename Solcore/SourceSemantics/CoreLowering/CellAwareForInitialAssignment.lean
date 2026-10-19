import Solcore.SourceSemantics.CoreLowering.CellAwareScopeBareAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeForInitialBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedForItemsTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedImperativeFlow

/-! Mixed bare assignments execute the real target snapshot, RHS, modifier
and write before the remaining header items. Every reached descriptor survives
both successful updates and genuine failures. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForInitialAssignment
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
  {registry : SourceCoreRawMetadata.Registry} {named : SourceCoreGeneralFunctions.Function}
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
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)))
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
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
    (children : CellAwareScopeExpressionBounds.PreservesBelow bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    (tail : CellAwareScopeForInitialBounds.PreservesAtMost bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope rest test postItems statements expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeForInitialBounds.PreservesAt bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope (.assignValue assignment operator rhs :: rest) test postItems statements expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger
    initial admitted authority physical owner sameLocation ready outcome after trace
  obtain ⟨target, snapshot⟩ := CellAwareScopeBareAssignmentHeads.target_snapshot
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
      CellAwareScopeBareAssignmentHeads.preserves_fault bridge functions extension head bare
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
        (children childSize childStrict) childTrace body (LocalLoop.controlType type)
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
      preservation, metadata, effect, reached, related, fault_post bridge reached stable⟩
  · subst outcome
    have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega) within
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, stable⟩ :=
      CellAwareScopeBareAssignmentHeads.preserves_operands bridge functions extension head bare
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
      CellAwareScopeBareAssignmentHeads.preserves_value bridge functions extension transport head bare
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
    (children : CellAwareScopeExpressionBounds.ReflectsBelow bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    (tail : CellAwareScopeForInitialBounds.ReflectsAtMost bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope rest test postItems statements expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeForInitialBounds.ReflectsAt bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope (.assignValue assignment operator rhs :: rest) test postItems statements expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger
    initial admitted authority physical owner sameLocation ready completed
  have result := CellAwareScopeBareAssignmentHeads.reflects_bounded bridge functions extension transport
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

end Solcore.SourceSemantics.CoreLowering.CellAwareForInitialAssignment
