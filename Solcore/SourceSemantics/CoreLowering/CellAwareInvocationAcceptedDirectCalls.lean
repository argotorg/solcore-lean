import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationExpressionSequence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalDirectHeadBounds
import Solcore.SourceSemantics.CoreLowering.SelectedStagedPostAdmission

/-! Direct declaration calls at accepted cell-aware sites. The argument vector,
the issued global cell read and the restoration of the caller carrier are
proved here from the actual compiler receipt. Applying the selected named
closure is an explicit input below the Source (or native) grade of the call:
the size induction across bodies discharges it from the callee's own accepted
body. As in the plain-heap direct head, the caller carrier retains every
ordinary global slot, and every reached caller retains the physical cache. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedDirectCalls
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey NamedSourceAt)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (Port EvidenceAt)
open CallableIndexedOwnedPreparedStagedPhysicalDirectHeadBounds (Point)
universe u

section Application
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  (registry : Staging.Recursive.Registry) (faults : RecursiveStageMeaning.FaultRep)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))

/-- Applying the issued closure of `header` to packed arguments from a reached
caller pool with its physical capture and cache: callee entry, body and the
restoration of the same pool over accepted cells, with the Source grade of the
application. This is the cross-body input of a direct-call site. -/
def PreservesAt (size : Nat) : Prop :=
  ∀ {scope mapping world before store canonical} (owner : OwnedKey keys)
    (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (capture : CallableIndexedOwnedNamedPhysicalCaptures.Capture headers owner.key header mapping world store),
    CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store → header ∈ headers → StableRows caller →
  ∀ {context arguments payloads}, Dynamic.TypeContextSupports header.context context →
    Dynamic.HeapWellTyped header.function.context before →
    Dynamic.ValuesHaveTypes header.function.context before arguments header.types →
    CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads →
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
      (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store →
  ∀ {rawD function}, NamedSourceAt header rawD function →
  ∀ {invocation outcome after},
    Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) registry size invocation context
      before (.global function) arguments outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: capture.named.captured) store
        (header.code.rename capture.named.embedding.lift) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        header.function.resultType header.output faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates caller returned

/-- Native completion of the same issued closure from the same caller pool
reconstructs an independent Source application and the restored pool. -/
def ReflectsAt (size : Nat) : Prop :=
  ∀ {scope mapping world before store canonical} (owner : OwnedKey keys)
    (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (capture : CallableIndexedOwnedNamedPhysicalCaptures.Capture headers owner.key header mapping world store),
    CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store → header ∈ headers → StableRows caller →
  ∀ {context arguments payloads}, Dynamic.TypeContextSupports header.context context →
    Dynamic.HeapWellTyped header.function.context before →
    Dynamic.ValuesHaveTypes header.function.context before arguments header.types →
    CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads →
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
      (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store →
  ∀ {rawD function}, NamedSourceAt header rawD function →
  ∀ {invocation value finalStore},
    EvaluationSize size (DataPatternValues.packValues payloads :: capture.named.captured) store
      (header.code.rename capture.named.embedding.lift) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) registry sourceSize invocation
        context before (.global function) arguments outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        header.function.resultType header.output faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates caller returned

def PreservesBelow (budget : Nat) : Prop :=
  ∀ size, size < budget →
    PreservesAt (attachment := attachment) (headers := headers) (keys := keys) model registry faults header size

def ReflectsBelow (budget : Nat) : Prop :=
  ∀ size, size < budget →
    ReflectsAt (attachment := attachment) (headers := headers) (keys := keys) model registry faults header size

end Application

section Head
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : OwnedKey keys)
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
    (fun current => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix current.scope current.canonical) callerProtocol)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (cache : ∀ {current}, callerProtocol.State current →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled current.mapping current.store)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  {bodyRelation : ActualBodyInvocation.BodyRelation} (index : ActualBodyInvocation.Index compiled bodyRelation)
  (registry : Staging.Recursive.Registry) (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)

private theorem result_type : lowered.type = port.header.output :=
  receipt.result.symm.trans ((congrArg SourceCoreCalls.Signature.resultType port.signature).symm.trans
    port.header.resultType)

private theorem parameter_type : port.header.named.signature.parameterType =
    (SourceCoreCalls.packArguments receipt.codes).type := by
  rw [port.signature]
  exact receipt.parameter

include owner receipt port evidenceAt callerBridge keyPhysical cache unique wellFormed runtime covers in
/-- A direct call at an accepted site preserves its staged execution when the
selected callee's application does below the same Source grade. Argument
faults stop before the global read, as in the original helper. -/
theorem preserves {children : GenericExpressionMeaning.Certificate} (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids
      (port.header.bindings.map (fun binding => binding.1.scheme.body)) receipt.codes)
    (childMeaning : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment)
      callerBridge.forgetSlots context model index registry invocation children faults size)
    (application : PreservesBelow (attachment := attachment) (headers := headers) (keys := keys)
      model registry faults port.header size) :
    CellAwareInvocationExpressionBounds.PreservesAt (attachment := attachment) callerBridge.forgetSlots context model
      index registry invocation (Point scope id lowered) faults size := by
  intro current child code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  obtain ⟨sourceTypes, calleeValid, applicationValid, typing⟩ :=
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique receipt.metadata.found
      receipt.form receipt.metadata.coercions typed
  have rows := CallableIndexedOwnedPreparedStagedDirectCallAuthority.Ready.source_types receipt port.toReady
    wellFormed runtime.signatures applicationValid
  have orderedTyping := rows.1 ▸ typing
  have nativeResult := result_type receipt port
  have originalTrace := trace
  rcases CallableIndexedOwnedPreparedStagedDirectSourceInversion.children
      unique receipt.metadata.found receipt.form receipt.metadata.coercions trace with
    ⟨sequenceSize, invocationSize, argumentsHeap, sources, name, evidence, sameSize,
      _calleeOccurrence, _valid, sourceTrace, produced, invoked⟩ |
    ⟨sequenceSize, failure, sameSize, outcomeEq, sourceTrace⟩
  · have argumentsWithin : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    have invocationBelow : invocationSize < size := by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)
    obtain ⟨values, middleStore, middleMap, middleWorld, argumentsEvaluated, represented, middleHeaps,
        argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, argumentEffect, reached, related, post⟩ :=
      CellAwareInvocationExpressionSequence.preserves_values callerBridge.forgetSlots size sequence unique
        orderedTyping childMeaning environments heaps locals agrees actualTyped initial admitted authority physical
        frameOwner ownerFrame sourceTrace argumentsWithin
    obtain ⟨parameters, headerHeap, headerArguments, supports⟩ :=
      CallableIndexedOwnedPreparedStagedDirectArgumentRows.at_successful_arguments receipt port evidenceAt
        wellFormed runtime covers locals admitted.heap calleeValid applicationValid sourceTrace represented typing
    have sourceEq := CallableIndexedOwnedPreparedStagedDirectArgumentRows.global_eq receipt port evidenceAt produced
    rw [sourceEq] at invoked
    obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt
      port.prepared port.aligned port.member keyPhysical (cache reached) middleHeaps.runtime_hasTypes
    obtain ⟨value, finalStore, finalMap, finalWorld, bodyEvaluated, result, finalHeaps,
        bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyEffect, finalState, bodyRelated⟩ :=
      application invocationSize invocationBelow owner (callerBridge.pool reached) capture (cache reached)
        port.member post.rows supports headerHeap headerArguments parameters middleHeaps port.sourceAt invoked
    have selected := OptionalCell.read_success compilation.internalReason
      (show Evaluates (DataPatternValues.packValues values :: actual) middleStore
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
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, argumentEffect.trans bodyEffect,
      returned, returnedRelated, ?_⟩
    · rw [receipt.emitted, NamedCalls.Arguments.call_rename, ← port.signature, ← port.slot]
      exact SourceCoreCalls.call_success argumentsEvaluated selected bodyEvaluated
    · simpa only [rows.2, nativeResult] using result
    · exact SelectedStagedPostAdmission.after_expression_sized initial returned admitted
        (Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) runtime covers locals typed
        originalTrace (argumentFrame.trans bodyFrame)
  · subst outcomeEq
    have argumentsWithin : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨token, finalStore, finalMap, finalWorld, argumentsEvaluated, matched, finalHeaps,
        maps, worlds, frame, metadata, effect, reached, related, _post⟩ :=
      CellAwareInvocationExpressionSequence.preserves_fault callerBridge.forgetSlots size sequence unique
        orderedTyping childMeaning environments heaps locals agrees actualTyped initial admitted authority physical
        frameOwner ownerFrame sourceTrace argumentsWithin
    refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, ?_⟩
    · rw [receipt.emitted, NamedCalls.Arguments.call_rename]
      simpa only [receipt.result] using SourceCoreCalls.call_argument_failure
        (signature := receipt.signature)
        (index := ξ (current.length + compilation.administrativePrefix + receipt.index))
        (internalReason := compilation.internalReason) (receipt.parameter.symm ▸ argumentsEvaluated)
    · exact SelectedStagedPostAdmission.after_expression_sized initial reached admitted
        (Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) runtime covers locals typed
        originalTrace frame

include owner receipt port evidenceAt callerBridge keyPhysical cache unique wellFormed runtime covers in
/-- Native completion of a direct call at an accepted site reconstructs its
staged execution when the selected callee's application does below the native
grade of the call. -/
theorem reflects {children : GenericExpressionMeaning.Certificate} (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids
      (port.header.bindings.map (fun binding => binding.1.scheme.body)) receipt.codes)
    (childMeaning : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment)
      callerBridge.forgetSlots context model index registry invocation children faults size)
    (application : ReflectsBelow (attachment := attachment) (headers := headers) (keys := keys)
      model registry faults port.header size) :
    CellAwareInvocationExpressionBounds.ReflectsAt (attachment := attachment) callerBridge.forgetSlots context model
      index registry invocation (Point scope id lowered) faults size := by
  intro current child code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame completed
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  obtain ⟨sourceTypes, calleeValid, applicationValid, typing⟩ :=
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique receipt.metadata.found
      receipt.form receipt.metadata.coercions typed
  have rows := CallableIndexedOwnedPreparedStagedDirectCallAuthority.Ready.source_types receipt port.toReady
    wellFormed runtime.signatures applicationValid
  have orderedTyping := rows.1 ▸ typing
  have nativeResult := result_type receipt port
  have parameter := parameter_type receipt port
  have occurrence : Staging.Recursive.Occurrence invocation child (.call callee ids (.declaration instantiation))
      receipt.node.requirements :=
    ⟨receipt.node, lookupExpression?_sound receipt.metadata.found, receipt.form, rfl, receipt.metadata.coercions⟩
  obtain ⟨name, calleeOccurrence, valid⟩ :=
    CallableIndexedOwnedPreparedStagedDirectArgumentRows.callee_receipt receipt runtime calleeValid
  rw [receipt.emitted, NamedCalls.Arguments.call_rename, ← port.signature, ← port.slot] at completed
  obtain ⟨sequenceSize, argumentValue, middleStore, smaller, argumentEvaluation⟩ :=
    RecursiveNamedCallBounds.call_arguments completed
  obtain ⟨sourceSize, sourceOutcome, argumentsHeap, middleMap, middleWorld, sourceTrace, represented, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, argumentEffect, reached, related, post⟩ :=
    CellAwareInvocationExpressionSequence.reflects callerBridge.forgetSlots size sequence unique orderedTyping
      childMeaning environments heaps locals agrees actualTyped initial admitted authority physical frameOwner
      ownerFrame argumentEvaluation smaller
  cases represented with
  | fault matched =>
    have evaluated := SourceCoreCalls.call_argument_failure
      (signature := port.header.named.signature)
      (index := ξ (current.length + compilation.administrativePrefix + port.header.slot))
      (internalReason := compilation.internalReason) (parameter.symm ▸ argumentEvaluation.sound)
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound evaluated
    have trace := Staging.Recursive.Size.Expression.directArgumentsFault occurrence calleeOccurrence sourceTrace
    refine ⟨_, _, argumentsHeap, middleMap, middleWorld, trace, ?_, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, argumentEffect, reached, related, ?_⟩
    · rw [← receipt.result, ← port.signature]
      exact .fault matched
    · exact SelectedStagedPostAdmission.after_expression_sized initial reached admitted
        (Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) runtime covers locals typed
        trace argumentFrame
  | @values sources values payloads =>
    obtain ⟨parameters, headerHeap, headerArguments, supports⟩ :=
      CallableIndexedOwnedPreparedStagedDirectArgumentRows.at_successful_arguments receipt port evidenceAt
        wellFormed runtime covers locals admitted.heap calleeValid applicationValid sourceTrace payloads typing
    obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt
      port.prepared port.aligned port.member keyPhysical (cache reached) middleHeaps.runtime_hasTypes
    obtain ⟨bodySize, bodySmaller, bodyEvaluation⟩ := RecursiveNamedCallBounds.call_body
      argumentEvaluation.sound (agrees (callerBridge.slots initial port.header port.member)) capture.read completed
    obtain ⟨invocationSize, outcome, after, finalMap, finalWorld, invoked, result, finalHeaps,
        bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyEffect, finalState, bodyRelated⟩ :=
      application bodySize bodySmaller owner (callerBridge.pool reached) capture (cache reached) port.member
        post.rows supports headerHeap headerArguments parameters middleHeaps port.sourceAt bodyEvaluation
    have produced := evidenceAt.produces
    have sourceEq := CallableIndexedOwnedPreparedStagedDirectArgumentRows.global_eq receipt port evidenceAt produced
    rw [← sourceEq] at invoked
    have trace := Staging.Recursive.Size.Expression.directApplied occurrence calleeOccurrence valid sourceTrace
      produced invoked
    obtain ⟨returned, _samePool, returnedRelated⟩ := callerBridge.restore initial finalState
      (argumentMaps.trans bodyMaps) (argumentWorlds.trans bodyWorlds)
      (argumentFrame.trans bodyFrame) (argumentMetadata.trans bodyMetadata)
      ((callerBridge.related related).trans bodyRelated)
    refine ⟨_, outcome, after, finalMap, finalWorld, trace, ?_, finalHeaps,
      argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds,
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, argumentEffect.trans bodyEffect,
      returned, returnedRelated, ?_⟩
    · simpa only [rows.2, nativeResult] using result
    · exact SelectedStagedPostAdmission.after_expression_sized initial returned admitted
        (Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) runtime covers locals typed
        trace (argumentFrame.trans bodyFrame)

end Head

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedDirectCalls
