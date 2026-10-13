import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalScopedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaCanonicalEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCanonicalState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedImperativePreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedImperativeFlow
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFooter
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMarkedAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaParameterAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds

/-! The retained canonical packet supplies the existing scoped flow engine
with the actual retained nested frame and global slots. Local allocation, mutation and finite loops
keep those slots and the reached pool throughout every direct or index child. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNestedBranchingLambdaBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Branching NestedBranchingSupport parameterScope)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (ordinary : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry semanticFaults)
  (origin : CallableIndexedOwnedOrdinaryLambdaSupport.SourceOrigin ordinary history)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) ordinary.caller)
  (packet : Branching code stages)
  (support : NestedBranchingSupport headers keys ordinary stages packet)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments ordinary.body.types)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "inputs" => ordinary.body.toContext
local notation "canonicalBridge" =>
  CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner ordinary.caller
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

private theorem forget_post {index : ProtectedStateTransition.Index}
    {context : SourceSemantics.Context} {type : TypeSystem.Ty} {outcome : Staging.Recursive.Outcome}
    (state : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner ordinary.caller).State index)
    (post : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      canonicalBridge
      context type outcome state) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys))
      context type outcome state.val := by
  cases outcome with
  | value value => exact ⟨post.rows, post.successful⟩
  | fault failure =>
    cases failure with
    | semantic reason => exact ⟨post.rows, post.successful⟩
    | stage origin call reason => exact post

include support observed origin prefixContext stable beforeTyped argumentsTyped in
/-- Preservation receives the actual Source-selected scope and allocation.
The already constructed parameter admission feeds the strict recursive whole-body port. -/
theorem source_body_at
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions completion.result.context.registry
      arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (spine : entry.entry.canonical = added ++ captured.canonical)
    (reached : State headers keys
      ⟨parameterScope code, entry.entry.mapping, entry.entry.world, entry.entry.heap,
        entry.entry.store, entry.entry.canonical⟩)
    {budget : Nat}
    (recursiveChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {bodySize : Nat} (within : bodySize ≤ budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.SourceBodyAt
      (stages := stages) (faults := callFaults)
      captured code history inputs functions owner caller entry reached bodySize := by
  intro child finalContext bodyOutcome outcome after selected valid trace matched
  have admitted := CallableIndexedOwnedPreparedLambdaParameterAdmission.at_parameters
    captured code history inputs functions owner caller entry reached valid beforeTyped argumentsTyped stable
  obtain ⟨sourceFinal, sourceFacts, sourceTyped, _sourceComplete⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters valid ordinary.body.extended
  rw [← stages.source selected] at sourceTyped
  have originalTyping : ProtectedStateImperativeTypedSourceSites.Statements child.source ordinary.body.context function.body :=
    ⟨_, _, _, sourceTyped⟩
  have tree := support.tree child selected
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape child.source true function.body := by
    rw [stages.source selected]
    exact packet.shape
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact ordinary.body.frame.code.graph.nodeOccurrencesUnique
  have actualPacket := CallableIndexedOwnedLambdaNestedEntries.source_packet
    captured code history inputs functions owner ordinary.caller observed prefixContext origin.metadata
    caller entry added length spine reached
  let initial : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers)
      owner ordinary.caller).State
      ⟨parameterScope code, entry.entry.mapping, entry.entry.world, entry.entry.heap,
        entry.entry.store, entry.entry.canonical⟩ := ⟨reached, actualPacket⟩
  have canonicalAdmitted : CallableIndexedOwnedSourceAdmission.Admission canonicalBridge ordinary.body.context initial :=
    ⟨admitted.heap, admitted.rows⟩
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position entry.nextHistory
  obtain ⟨flowValue, bodyStore, finalMap, finalWorld, evaluated, represented, heaps,
      maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedScopedImperativePreservation.preserves_at
      canonicalBridge
      (CallableIndexedOwnedNestedCanonicalState.bindings owner ordinary.caller)
      (CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner ordinary.caller)
      functions completion.result.extension rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
      (CallableIndexedOwnedNestedCanonicalState.markedProducer owner ordinary.caller
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner
        (headers := headers) owner ordinary.caller (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) stable)
      (fun context size smaller =>
        CallableIndexedOwnedPreparedStagedCanonicalScopedExpressionBounds.preserves_children
          support.complete support.zero support.wellFormed support.globals profile
          ((stages.source selected).trans ordinary.source)
          (by rw [stages.source selected]; exact ordinary.body.unique)
          (by
            intro size smaller context child scope expression lowered root
            exact recursiveChildren size smaller root)
          children owner context smaller)
      unique tree (support.sites child selected completion.result.context.registry
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) rfl shape originalTyping ordinary.body.projection within entry.entry.environments entry.entry.heaps
      entry.entry.locals entry.entry.lookups entry.entry.actualTyped entry.entry.reference entry.entry.read
      entry.entry.unmapped initial conditioned canonicalAdmitted trace
  have post := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post
  have represented := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents.to_function ordinary.body.projection represented
  obtain ⟨value, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented evaluated
      packet.fellThrough packet.escaped entry.entry.embedding
  have outcomeEq := CallableIndexedOwnedAdmittedStagedLexicalFooter.outcome_eq matched
  subst outcome
  refine ⟨value, bodyStore, finalMap, finalWorld, ?_, representedBody, heaps,
    maps, worlds, frame, metadata, returned.val, related, forget_post (captured := captured) (code := code) ordinary owner returned post⟩
  simpa only [packet.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] using evaluatedBody

include support observed origin prefixContext stable beforeTyped argumentsTyped in
/-- Reflection uses the literal chosen scope and real prefix allocation. It
constructs the original body trace and full post without a new body callback. -/
theorem native_body_at
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions completion.result.context.registry arguments before store
      owner.key.frameLocation (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨parameterScope code, entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    {budget : Nat}
    (recursiveChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {nativeSize : Nat} (within : nativeSize ≤ budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.NativeBodyAt
      (stages := stages) (faults := callFaults)
      captured code history inputs functions owner caller entry reached packet.child nativeSize := by
  intro value bodyStore completed
  have rawTypes := Dynamic.MonoBindersExtend.bodyTypes_eq ordinary.body.extended
  have rawArguments : Dynamic.ValuesHaveTypes function.context before arguments
      (function.parameters.map (fun binder => binder.scheme.body)) := by
    simpa only [rawTypes] using argumentsTyped
  have allocated := Dynamic.BindersAllocate.preservesHeapTyping beforeTyped rawArguments entry.allocation
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields ordinary.body.extended
  have heapTyped : Dynamic.HeapWellTyped ordinary.body.context entry.heap :=
    allocated.transportClosed fields.signatures valid.code.closed (fields.targetClosed valid.code.closed)
      valid.code.variables_closed (fields.targetResidualVariablesOpen valid.code.residual_variables_open)
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable entry.nextHistory entry.frame
  have admitted : CallableIndexedOwnedSourceAdmission.Admission
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      ordinary.body.context reached := ⟨heapTyped, rows⟩
  obtain ⟨sourceFinal, sourceFacts, sourceTyped, _sourceComplete⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters valid ordinary.body.extended
  rw [← stages.source packet.selected] at sourceTyped
  have originalTyping : ProtectedStateImperativeTypedSourceSites.Statements packet.child.source ordinary.body.context function.body :=
    ⟨_, _, _, sourceTyped⟩
  have graph : OccurrenceGraphWellFormed packet.child.source := by
    rw [stages.source packet.selected]
    exact valid.code.graph
  have tree := support.tree packet.child packet.selected
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape packet.child.source true function.body := by
    rw [stages.source packet.selected]
    exact packet.shape
  have actualPacket := CallableIndexedOwnedLambdaNestedEntries.native_packet
    captured code history inputs functions owner ordinary.caller observed prefixContext origin.metadata
    caller entry reached
  let initial : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers)
      owner ordinary.caller).State
      ⟨parameterScope code, entry.mapping, entry.world, entry.heap,
        entry.store, entry.canonical⟩ := ⟨reached, actualPacket⟩
  have canonicalAdmitted : CallableIndexedOwnedSourceAdmission.Admission canonicalBridge ordinary.body.context initial :=
    ⟨admitted.heap, admitted.rows⟩
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position entry.nextHistory
  have bodyTrace := completed
  rw [packet.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] at bodyTrace
  obtain ⟨flowSize, flowValue, flowStore, flowTrace, strict⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.flow_prefix bodyTrace within
  obtain ⟨sourceSize, finalContext, bodyOutcome, after, finalMap, finalWorld, trace, represented, heaps,
      maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedScopedImperativeFlow.reflects_at
      canonicalBridge
      (CallableIndexedOwnedNestedCanonicalState.bindings owner ordinary.caller)
      (CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner ordinary.caller)
      functions completion.result.extension rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
      (CallableIndexedOwnedNestedCanonicalState.markedProducer owner ordinary.caller
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner
        (headers := headers) owner ordinary.caller (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) stable)
      (fun context size smaller =>
        CallableIndexedOwnedPreparedStagedCanonicalScopedExpressionBounds.reflects_children
          support.complete support.zero support.wellFormed support.globals profile
          ((stages.source packet.selected).trans ordinary.source)
          (by rw [stages.source packet.selected]; exact ordinary.body.unique)
          (by
            intro size smaller context child scope expression lowered root
            exact recursiveChildren size smaller root)
          children owner context smaller)
      graph tree (support.sites packet.child packet.selected completion.result.context.registry
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) rfl shape originalTyping ordinary.body.projection (Nat.le_of_lt strict) entry.environments entry.heaps
      entry.locals entry.lookups entry.actualTyped entry.reference entry.read entry.unmapped initial
      conditioned canonicalAdmitted flowTrace
  have post := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post
  have represented := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents.to_function ordinary.body.projection represented
  obtain ⟨bodyValue, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented flowTrace.sound
      packet.fellThrough packet.escaped entry.embedding
  obtain ⟨sameValue, sameStore⟩ := evaluation_deterministic bodyTrace.sound evaluatedBody
  subst bodyValue
  subst flowStore
  exact ⟨sourceSize, finalContext, bodyOutcome, _, after, finalMap, finalWorld, trace,
    represented.body_result, representedBody, heaps, maps, worlds, frame, metadata, returned.val, related, forget_post (captured := captured) (code := code) ordinary owner returned post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNestedBranchingLambdaBodyBounds
