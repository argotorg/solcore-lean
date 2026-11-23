import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationElementCompoundReflects
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationElementBitNot

/-!
# Cell-aware invocations: the reflect flows of the writes to an element

The statement-level reflect flows of a write to one element of a local memory array, as companions of the
projected route's flows: an assignment `a[i] = v` or `a[i] op= v`, reflected by the plain or the compound head as
the operator is `=` or not (`CellAwareElementWriteHeads.reflects_plain_bounded`, `reflects_compound_bounded`),
and an in-place `~` `a[i] ~=;` (`reflects_bitNot_bounded`). Each gives the Source's sized `StatementsIn` trace with
the element rules, its faults at the statement, and its write followed by the remaining statements' reflected
trace. Main declarations: `CellAwareInvocationElementAssignmentFlow.reflects` and
`CellAwareInvocationElementBitNotFlow.reflects`.
-/

section
/-! An assignment to one element of a local array: the element target's faults, the right side's fault, the
compound write's fault, or the write, then the remaining statements under the write's binders. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationElementAssignmentFlow
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
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
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
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (sourceEq : invocation.source = bodyIndex.source)
  (unique : NodeOccurrencesUnique invocation.source)
  (found : invocation.source.lookupStatement? id = some node)
  (form : node.form = .assignValue assignment operator rhs)
  (head : CellAwareElementWriteHeads.Head (.initial compiled.compatible.checked) invocation.source context certificate
    scope assignment operator rhs)
  {identities : Dynamic.Value → Word → Prop}
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program stages)
  (uninitializedReason : ∀ location, faults (.semantic (.uninitializedLocation location)) head.invalidProjection)

include sourceEq unique found form observations selectedBodies uninitializedReason in
/-- An assignment to one element of a local array, `a[i] = v` or `a[i] op= v`, reflected: the plain head for
`=` and the compound head otherwise give, from the actual Core run of the code, the Source's element target, right
side and write, or the fault at the target, at the right side or at the compound write; the remaining statements'
reflected trace continues from the write's binders. The heads' runtime validity and coverage are the flow's own,
`selectedBodies` keeps the array's length across the right side, and `uninitializedReason` is the site's token at
a root not yet initialized. -/
theorem reflects [RecursiveStageMeaning.FaultTokens faults] (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation
      certificate faults budget)
    (tail : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages
      invocation faults administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationFlowBounds.ReflectsAt (attachment := attachment) bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages
      invocation faults administrative scope mode (id :: rest) expected type
      (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready completed
  have assignmentTyped := ProtectedStateImperativeTypedSourceSites.assignment unique
    (sourceEq.symm ▸ ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
  have suffix := ProtectedStateImperativeStatementSuffixTyping.assignment
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ found) form
  have sourceRuntime : Dynamic.SourceRuntimeValid program context invocation.source := sourceEq ▸ runtime
  have element : Staging.Recursive.ElementPlace assignment.target.projections := ⟨[], head.key, head.single⟩
  by_cases plain : operator = .equal
  · have result := CellAwareElementWriteHeads.reflects_plain_bounded bridge functions head environments heaps
      locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped budget
      plain children selectedBodies sourceRuntime covers uninitializedReason completed within
    cases result with
    | uninitialized failed same matched finalHeaps maps worlds frame metadata effect reached related stable =>
      cases same
      refine ⟨_, context, _, _, _, _,
        .assignElementTargetFault (lookupStatement?_sound found) form element failed, .fault matched,
        finalHeaps, maps, worlds, frame, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable
    | indexFault failed same matched finalHeaps maps worlds frame metadata effect reached related stable =>
      cases same
      refine ⟨_, context, _, _, _, _,
        .assignElementTargetFault (lookupStatement?_sound found) form element failed, .fault matched,
        finalHeaps, maps, worlds, frame, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge reached stable
    | outOfBounds failed same matched finalHeaps maps worlds frame metadata effect reached related stable =>
      cases same
      refine ⟨_, context, _, _, _, _,
        .assignElementTargetFault (lookupStatement?_sound found) form element failed, .fault matched,
        finalHeaps, maps, worlds, frame, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable
    | rhsFault resolved childTrace same matched finalHeaps maps worlds frame metadata effect reached related stable =>
      cases same
      refine ⟨_, context, _, _, _, _,
        .assignElementRhsFault (lookupStatement?_sound found) form element resolved childTrace, .fault matched,
        finalHeaps, maps, worlds, frame, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge reached stable
    | success resolved childTrace write middleHeaps maps worlds frame metadata effect count typed reached related
        nextAdmitted strict remaining =>
      obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
          finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
        tail _ (Nat.le_trans (Nat.le_of_lt strict) within)
          (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees _) typed runtime covers sameLedger suffix
          reached nextAdmitted (authority.transport effect) (physical.transport effect frame) owner sameLocation ready
          (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
            SourceCoreDataPlaces.shift] using remaining)
      exact ⟨Staging.Recursive.Size.stepSize [_, _, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
        .assignElement (lookupStatement?_sound found) form element resolved childTrace write trace, represented,
        finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, frame.trans finalFrame,
        metadata.trans finalMetadata, effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩
  · have result := CellAwareElementWriteHeads.reflects_compound_bounded bridge functions observations head
      environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique
      assignmentTyped budget plain children selectedBodies sourceRuntime covers uninitializedReason completed within
    cases result with
    | uninitialized failed same matched finalHeaps maps worlds frame metadata effect reached related stable =>
      cases same
      refine ⟨_, context, _, _, _, _,
        .assignElementTargetFault (lookupStatement?_sound found) form element failed, .fault matched,
        finalHeaps, maps, worlds, frame, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable
    | indexFault failed same matched finalHeaps maps worlds frame metadata effect reached related stable =>
      cases same
      refine ⟨_, context, _, _, _, _,
        .assignElementTargetFault (lookupStatement?_sound found) form element failed, .fault matched,
        finalHeaps, maps, worlds, frame, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge reached stable
    | outOfBounds failed same matched finalHeaps maps worlds frame metadata effect reached related stable =>
      cases same
      refine ⟨_, context, _, _, _, _,
        .assignElementTargetFault (lookupStatement?_sound found) form element failed, .fault matched,
        finalHeaps, maps, worlds, frame, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable
    | rhsFault resolved childTrace same matched finalHeaps maps worlds frame metadata effect reached related stable =>
      cases same
      refine ⟨_, context, _, _, _, _,
        .assignElementRhsFault (lookupStatement?_sound found) form element resolved childTrace, .fault matched,
        finalHeaps, maps, worlds, frame, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge reached stable
    | writeFault resolved childTrace failed same matched finalHeaps maps worlds frame metadata effect reached related
        stable =>
      cases same
      refine ⟨_, context, _, _, _, _,
        .assignElementWriteFault (lookupStatement?_sound found) form element resolved childTrace failed,
        .fault matched, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable
    | success resolved childTrace write middleHeaps maps worlds frame metadata effect count typed reached related
        nextAdmitted strict remaining =>
      obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
          finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
        tail _ (Nat.le_trans (Nat.le_of_lt strict) within)
          (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees _) typed runtime covers sameLedger suffix
          reached nextAdmitted (authority.transport effect) (physical.transport effect frame) owner sameLocation ready
          (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
            SourceCoreDataPlaces.shift] using remaining)
      exact ⟨Staging.Recursive.Size.stepSize [_, _, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
        .assignElement (lookupStatement?_sound found) form element resolved childTrace write trace, represented,
        finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, frame.trans finalFrame,
        metadata.trans finalMetadata, effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationElementAssignmentFlow
end

section
/-! An in-place `~` at one element of a local array: the element target's faults, or the write, then the
remaining statements under the write's binders. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationElementBitNotFlow
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
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool}
  {expected : TypeSystem.Ty} {type : Ty} {id : StatementId} {node : StatementNode}
  {assignment : AssignmentResolution}
  {rest : List StatementId} {body : Expr}
variable
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (sourceEq : invocation.source = bodyIndex.source)
  (unique : NodeOccurrencesUnique invocation.source)
  (found : invocation.source.lookupStatement? id = some node)
  (form : node.form = .assignBitNot assignment)
  (head : CellAwareElementWriteHeads.BitNotHead (.initial compiled.compatible.checked) invocation.source context
    certificate scope assignment)
  (uninitializedReason : ∀ location, faults (.semantic (.uninitializedLocation location)) head.invalidProjection)

include sourceEq unique found form uninitializedReason in
/-- An in-place `~` at one element of a local array, `a[i] ~=;`, reflected: the head gives, from the actual Core
run of the code, the Source's element target and write, or the target's fault; the remaining statements' reflected
trace continues from the write's eight binders. `uninitializedReason` is the site's token at a root not yet
initialized. -/
theorem reflects [RecursiveStageMeaning.FaultTokens faults] (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation
      certificate faults budget)
    (tail : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages
      invocation faults administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationFlowBounds.ReflectsAt (attachment := attachment) bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages
      invocation faults administrative scope mode (id :: rest) expected type
      (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready completed
  have assignmentTyped := ProtectedStateImperativeTypedSourceSites.bit_not unique
    (sourceEq.symm ▸ ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
  have suffix := ProtectedStateImperativeStatementSuffixTyping.bitNot
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ found) form
  have element : Staging.Recursive.ElementPlace assignment.target.projections := ⟨[], head.key, head.single⟩
  have result := CellAwareElementWriteHeads.reflects_bitNot_bounded bridge functions head environments heaps locals
    agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped budget children
    uninitializedReason completed within
  cases result with
  | targetFault failed same matched finalHeaps maps worlds frame metadata effect reached related stable =>
    cases same
    refine ⟨_, context, _, _, _, _,
      .bitNotElementTargetFault (lookupStatement?_sound found) form element failed, .fault matched,
      finalHeaps, maps, worlds, frame, metadata, effect, reached, related, ?_⟩
    exact fault_post bridge reached stable
  | success resolved write middleHeaps maps worlds frame metadata effect count typed reached related nextAdmitted
      strict remaining =>
    obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
        finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
      tail _ (Nat.le_trans (Nat.le_of_lt strict) within)
        (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees _) typed runtime covers sameLedger suffix
        reached nextAdmitted (authority.transport effect) (physical.transport effect frame) owner sameLocation ready
        (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
          SourceCoreDataPlaces.shift] using remaining)
    exact ⟨Staging.Recursive.Size.stepSize [_, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
      .bitNotElement (lookupStatement?_sound found) form element resolved write trace, represented,
      finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, frame.trans finalFrame,
      metadata.trans finalMetadata, effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationElementBitNotFlow
end
