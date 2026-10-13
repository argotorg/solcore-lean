import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectHeadBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationDirectSourceTypes
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationDirectArgumentRows
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCallerSlotForgetting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationExpressionSequence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExpressionHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectArgumentRows
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedInvocationPreservation

/-! A direct call uses its actual compiler-selected global slot after the
ordered arguments have run. That slot comes from the caller's canonical
receipt; the reached pool supplies its current capture. The same named-body
ports retain independent Source and native grades and restore the caller. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationDirectBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (Port EvidenceAt)
universe u

open CallableIndexedOwnedPreparedStagedDirectHeadBounds (Point)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation (.initial compiled.compatible.checked)
    invocation.source scope id callee ids instantiation reasonAt lowered)
  (port : Port receipt headers)
  (evidenceAt : EvidenceAt receipt port context invocation.evidence)
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (certified : SelectedCompilationNamedSourceTyping.Certified port.header)
  (shaped : SelectedCompilationSourceSignatureFacts.Shape port.header)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)

local notation "bridge" => callerBridge.forgetSlots
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

private theorem result_type : lowered.type = port.header.output :=
  receipt.result.symm.trans ((congrArg SourceCoreCalls.Signature.resultType port.signature).symm.trans port.header.resultType)

private theorem parameter_type : port.header.named.signature.parameterType =
    (SourceCoreCalls.packArguments receipt.codes).type := by
  rw [port.signature]
  exact receipt.parameter

section Preservation
variable {stages : Staging.Recursive.Registry}

include owner receipt port evidenceAt callerBridge functions faults unique owners certified shaped runtime in
theorem preserves {children : GenericExpressionMeaning.Certificate}
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids
      (port.header.bindings.map (fun binding => binding.1.scheme.body)) receipt.codes)
    (childMeaning : PreservesBelow bridge context model stages invocation children faults size)
    (bodyMeaning : ∀ {child : Staging.Recursive.Scope}, stages.Closure port.header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.PreservesBelow (headers := headers) (keys := keys)
        port.header model stages child faults size) :
    PreservesAt bridge context model stages invocation (Point scope id lowered) faults size := by
  intro current child code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  obtain ⟨sourceTypes, calleeValid, application, typing⟩ :=
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique receipt.metadata.found
      receipt.form receipt.metadata.coercions typed
  have rows := SelectedCompilationDirectSourceTypes.source_types receipt port.toReady shaped runtime.signatures application
  have orderedTyping := rows.1 ▸ typing
  have nativeResult := result_type receipt port
  have parameter := parameter_type receipt port
  rcases CallableIndexedOwnedPreparedStagedDirectSourceInversion.children
      unique receipt.metadata.found receipt.form receipt.metadata.coercions trace with
    ⟨sequenceSize, invocationSize, argumentsHeap, sources, name, evidence, sameSize,
      calleeOccurrence, valid, sourceTrace, produced, invoked⟩ |
    ⟨sequenceSize, failure, sameSize, outcomeEq, sourceTrace⟩
  · have argumentsWithin : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    have invocationWithin : invocationSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨values, middleStore, middleMap, middleWorld, argumentsEvaluated, represented, middleHeaps,
        argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, reached, related, post⟩ :=
      SelectedCompilationExpressionSequence.preserves_values bridge size sequence unique orderedTyping
        childMeaning environments heaps locals agrees actualTyped initial admitted sourceTrace argumentsWithin
    obtain ⟨parameters, headerHeap, headerArguments, supports⟩ :=
      SelectedCompilationDirectArgumentRows.at_successful_arguments receipt port
        certified runtime post.at_values.heap post.values_typed represented
    have sourceEq := CallableIndexedOwnedPreparedStagedDirectArgumentRows.global_eq receipt port evidenceAt produced
    rw [sourceEq] at invoked
    obtain ⟨capture⟩ := CallableIndexedOwnedFunctionEntries.capture_from_pool
      (callerBridge.pool reached) owner port.member
    let nativeCapture := CallableIndexedOwnedFunctionValues.NamedCapture.of_capture capture
    obtain ⟨value, finalStore, finalMap, finalWorld, bodyEvaluated, result, finalHeaps,
        bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, finalState, bodyRelated, bodyPost⟩ :=
      SelectedCompilationNamedInvocationPreservation.preserves_invocation
        functions owner (callerBridge.pool reached) port.header nativeCapture port.sourceAt
        port.aligned.layouts port.member owners certified post.at_values.rows headerHeap headerArguments
        parameters middleHeaps supports size bodyMeaning invoked invocationWithin
    have selected := OptionalCell.read_success compilation.internalReason
      (show Evaluates (packValues values :: actual) middleStore
        (.var (ξ (current.length + compilation.administrativePrefix + port.header.slot) + 1))
        (.cellRef (OptionalCell.cellType port.header.named.signature.functionType)
          (owner.key.locations port.header)) middleStore from
        .var (agrees (callerBridge.slots initial port.header port.member))) capture.read
    obtain ⟨returned, _samePool, returnedRelated⟩ := callerBridge.restore initial finalState
      (argumentMaps.trans bodyMaps) (argumentWorlds.trans bodyWorlds)
      (argumentFrame.trans bodyFrame) (argumentMetadata.trans bodyMetadata)
      ((callerBridge.related related).trans bodyRelated)
    refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
      argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds,
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, returned, returnedRelated, ?_⟩
    · rw [receipt.emitted, NamedCalls.Arguments.call_rename, ← port.signature, ← port.slot]
      exact SourceCoreCalls.call_success argumentsEvaluated selected bodyEvaluated
    · simpa only [rows.2, nativeResult] using result
    · have rowsStable := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
        (callerBridge.pool initial) (callerBridge.pool returned) admitted.rows (argumentFrame.trans bodyFrame)
      cases outcome with
      | value value =>
          refine ⟨rowsStable, ?_⟩
          intro actual same
          cases same
          exact ⟨rows.2 ▸ bodyPost.at_value.1, bodyPost.at_value.2.heap⟩
      | fault failure => cases failure with
          | semantic reason => exact ⟨rowsStable, by intro _ impossible; cases impossible⟩
          | stage origin call reason => exact rowsStable
  · subst outcome
    have argumentsWithin : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨token, finalStore, finalMap, finalWorld, argumentsEvaluated, matched, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post⟩ :=
      SelectedCompilationExpressionSequence.preserves_fault bridge size sequence unique orderedTyping
        childMeaning environments heaps locals agrees actualTyped initial admitted sourceTrace argumentsWithin
    refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
      maps, worlds, frame, metadata, reached, related, ?_⟩
    · rw [receipt.emitted, NamedCalls.Arguments.call_rename]
      simpa only [receipt.result] using SourceCoreCalls.call_argument_failure
        (signature := receipt.signature) (index := ξ (current.length + compilation.administrativePrefix + receipt.index))
        (internalReason := compilation.internalReason) (receipt.parameter.symm ▸ argumentsEvaluated)
    · exact post.fault
end Preservation

section Reflection
variable {native : SourceCoreGeneralFunctions.CallableContext}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named port.header.named.signature.key))

include owner receipt port evidenceAt callerBridge functions faults unique certified shaped runtime stagePrepared descriptor in
theorem reflects {children : GenericExpressionMeaning.Certificate}
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids
      (port.header.bindings.map (fun binding => binding.1.scheme.body)) receipt.codes)
    (childMeaning : ReflectsBelow bridge context model (RecursiveNamedPreparedStageScopes.registry stagePrepared)
      invocation children faults size)
    (bodyMeaning : ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure port.header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        port.header model (RecursiveNamedPreparedStageScopes.registry stagePrepared) child faults size) :
    ReflectsAt bridge context model (RecursiveNamedPreparedStageScopes.registry stagePrepared)
      invocation (Point scope id lowered) faults size := by
  intro current child code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  obtain ⟨sourceTypes, calleeValid, application, typing⟩ :=
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique receipt.metadata.found
      receipt.form receipt.metadata.coercions typed
  have rows := SelectedCompilationDirectSourceTypes.source_types receipt port.toReady shaped runtime.signatures application
  have orderedTyping := rows.1 ▸ typing
  have nativeResult := result_type receipt port
  have parameter := parameter_type receipt port
  have occurrence : Staging.Recursive.Occurrence invocation child (.call callee ids (.declaration instantiation)) receipt.node.requirements :=
    ⟨receipt.node, lookupExpression?_sound receipt.metadata.found, receipt.form,
      rfl, receipt.metadata.coercions⟩
  obtain ⟨name, calleeOccurrence, valid⟩ :=
    CallableIndexedOwnedPreparedStagedDirectArgumentRows.callee_receipt receipt runtime calleeValid
  rw [receipt.emitted, NamedCalls.Arguments.call_rename, ← port.signature, ← port.slot] at completed
  obtain ⟨sequenceSize, argumentValue, middleStore, smaller, argumentEvaluation⟩ :=
    RecursiveNamedCallBounds.call_arguments completed
  obtain ⟨sourceSize, sourceOutcome, argumentsHeap, middleMap, middleWorld, sourceTrace, represented, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, reached, related, post⟩ :=
    SelectedCompilationExpressionSequence.reflects bridge size sequence unique orderedTyping childMeaning
      environments heaps locals agrees actualTyped initial admitted argumentEvaluation smaller
  cases represented with
  | fault matched =>
    have evaluated := SourceCoreCalls.call_argument_failure
      (signature := port.header.named.signature)
      (index := ξ (current.length + compilation.administrativePrefix + port.header.slot))
      (internalReason := compilation.internalReason) (parameter.symm ▸ argumentEvaluation.sound)
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound evaluated
    have trace := Staging.Recursive.Size.Expression.directArgumentsFault occurrence calleeOccurrence sourceTrace
    refine ⟨_, _, argumentsHeap, middleMap, middleWorld, trace, ?_, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, reached, related, ?_⟩
    · rw [← receipt.result, ← port.signature]
      exact .fault matched
    · exact post.fault
  | @values sources values payloads =>
    obtain ⟨parameters, headerHeap, headerArguments, supports⟩ :=
      SelectedCompilationDirectArgumentRows.at_successful_arguments receipt port
        certified runtime post.at_values.heap post.values_typed payloads
    obtain ⟨capture⟩ := CallableIndexedOwnedFunctionEntries.capture_from_pool
      (callerBridge.pool reached) owner port.member
    let nativeCapture := CallableIndexedOwnedFunctionValues.NamedCapture.of_capture capture
    obtain ⟨bodySize, bodySmaller, bodyEvaluation⟩ := RecursiveNamedCallBounds.call_body
      argumentEvaluation.sound (agrees (callerBridge.slots initial port.header port.member)) capture.read completed
    obtain ⟨invocationSize, outcome, after, finalMap, finalWorld, invoked, _bodyEvaluated, result, finalHeaps,
        bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, finalState, bodyRelated, bodyPost⟩ :=
      SelectedCompilationNamedInvocationBounds.reflects_invocation functions owner (callerBridge.pool reached)
        port.header nativeCapture port.prepared port.aligned stagePrepared descriptor port.sourceAt
        port.aligned.layouts port.member certified post.at_values.rows headerHeap headerArguments
        parameters middleHeaps supports size bodyMeaning bodyEvaluation (Nat.le_of_lt bodySmaller)
    have produced := evidenceAt.produces
    have sourceEq := CallableIndexedOwnedPreparedStagedDirectArgumentRows.global_eq receipt port evidenceAt produced
    rw [← sourceEq] at invoked
    have trace := Staging.Recursive.Size.Expression.directApplied occurrence calleeOccurrence valid sourceTrace produced invoked
    obtain ⟨returned, _samePool, returnedRelated⟩ := callerBridge.restore initial finalState
      (argumentMaps.trans bodyMaps) (argumentWorlds.trans bodyWorlds)
      (argumentFrame.trans bodyFrame) (argumentMetadata.trans bodyMetadata)
      ((callerBridge.related related).trans bodyRelated)
    refine ⟨_, outcome, after, finalMap, finalWorld, trace, ?_, finalHeaps,
      argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds,
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, returned, returnedRelated, ?_⟩
    · simpa only [rows.2, nativeResult] using result
    · have rowsStable := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
        (callerBridge.pool initial) (callerBridge.pool returned) admitted.rows (argumentFrame.trans bodyFrame)
      cases outcome with
      | value value =>
          refine ⟨rowsStable, ?_⟩
          intro actual same
          cases same
          exact ⟨rows.2 ▸ bodyPost.at_value.1, bodyPost.at_value.2.heap⟩
      | fault failure => cases failure with
          | semantic reason => exact ⟨rowsStable, by intro _ impossible; cases impossible⟩
          | stage origin call reason => exact rowsStable
end Reflection

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationDirectBounds
