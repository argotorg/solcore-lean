import Solcore.SourceSemantics.CoreLowering.CellAwareScopeBareAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeFlowBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBareAssignmentSourceInversion
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedImperativeFlow

/-! Mixed bare assignments execute the real target snapshot, RHS, modifier
and write before the remaining statements. Every reached descriptor survives
both successful updates and genuine failures. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeBareAssignmentFlow
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
  {registry : SourceCoreRawMetadata.Registry} {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool}
  {expected : TypeSystem.Ty} {type : Ty} {id : StatementId} {node : StatementNode}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  {rest : List StatementId} {body : Expr}
variable
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)))
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
  (unique : NodeOccurrencesUnique invocation.source)
  (found : invocation.source.lookupStatement? id = some node)
  (form : node.form = .assignValue assignment operator rhs)
  (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context certificate
    scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
  (bare : assignment.target.projections = [])
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  (invalidToken : AssignmentOperandDiagnostics.OperandsLaw
    (fun reason token => faults (.semantic reason) token) operator head.invalid)

include transport sourceEq unique found form bare extension invalidToken in
theorem preserves (budget : Nat)
    (children : CellAwareScopeExpressionBounds.PreservesBelow bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    (tail : CellAwareScopeFlowBounds.PreservesAtMost bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeFlowBounds.PreservesAt bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope mode (id :: rest) expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready finalContext outcome after trace
  have assignmentTyped := ProtectedStateImperativeTypedSourceSites.assignment unique
    (sourceEq.symm ▸ ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
  have suffix := ProtectedStateImperativeStatementSuffixTyping.assignment
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ found) form
  obtain ⟨target, snapshot⟩ := CellAwareScopeBareAssignmentHeads.target_snapshot
    (invocation := invocation) bridge functions extension head bare environments heaps locals agrees initial admitted
  rcases CallableIndexedOwnedPreparedStagedScopedBareAssignmentSourceInversion.child_and_tail unique found form snapshot trace with
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
      CellAwareScopeBareAssignmentHeads.preserves_fault bridge functions extension head bare
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
      CellAwareScopeBareAssignmentHeads.preserves_operands bridge functions extension head bare
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
      CellAwareScopeBareAssignmentHeads.preserves_value bridge functions extension transport head bare
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

include transport sourceEq unique found form bare extension invalidToken in
theorem reflects (budget : Nat)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    (tail : CellAwareScopeFlowBounds.ReflectsAtMost bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeFlowBounds.ReflectsAt bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope mode (id :: rest) expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready completed
  have assignmentTyped := ProtectedStateImperativeTypedSourceSites.assignment unique
    (sourceEq.symm ▸ ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
  have suffix := ProtectedStateImperativeStatementSuffixTyping.assignment
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ found) form
  have result := CellAwareScopeBareAssignmentHeads.reflects_bounded bridge functions extension transport
    head bare environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
    budget children invalidToken completed within
  cases result with
  | fault snapshot trace same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
    cases same
    exact ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
      .assignBareFault (lookupStatement?_sound found) form snapshot trace, .fault matched,
      finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, fault_post bridge reached stable⟩
  | operands snapshot trace currentRead rootType initialized path invalid same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
    cases same
    exact ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
      .assignBareOperands (lookupStatement?_sound found) form snapshot trace currentRead rootType initialized path invalid,
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
      .assignBare (lookupStatement?_sound found) form snapshot childTrace write trace, represented,
      finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
      metadata.trans finalMetadata, effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeBareAssignmentFlow
