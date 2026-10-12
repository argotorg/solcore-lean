import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFooter
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMarkedAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaParameterAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds

/-! The chosen lexical packet supplies the existing shape-independent body
ports at the genuine parameter entry. Original parameter admission and native
allocation typing are reused literally. Strong numeric Root induction supplies
the evaluated children; no whole-body meaning is a static packet field. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Lexical LexicalSupport parameterScope)

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
  (inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
  (packet : Lexical code stages)
  (support : LexicalSupport code inputs stages packet semanticFaults)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include support stable beforeTyped argumentsTyped in
/-- Preservation receives the actual Source-selected scope and allocation.
The already constructed parameter admission feeds the strict recursive whole-body port. -/
theorem source_body_at
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions completion.result.context.registry
      arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (reached : State headers keys
      ⟨parameterScope code, entry.entry.mapping, entry.entry.world, entry.entry.heap,
        entry.entry.store, entry.entry.canonical⟩)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {bodySize : Nat} (within : bodySize ≤ budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.SourceBodyAt
      (stages := stages) (faults := callFaults)
      captured code history inputs functions owner caller entry reached bodySize := by
  intro child finalContext bodyOutcome outcome after selected valid trace matched
  have admitted := CallableIndexedOwnedPreparedLambdaParameterAdmission.at_parameters
    captured code history inputs functions owner caller entry reached valid beforeTyped argumentsTyped stable
  have tree := support.tree child selected
  have shape : CallableIndexedOwnedPreparedStagedLexicalTree.Shape child.source function.body := by
    rw [stages.source selected]
    exact packet.shape
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact support.frame.code.graph.nodeOccurrencesUnique
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position entry.nextHistory
  obtain ⟨flowValue, bodyStore, finalMap, finalWorld, evaluated, represented, heaps,
      maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalPreservation.preserves
      CallableIndexedOwnedBodyRestorationAdmission.bridge
      (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
      functions rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
      (CallableIndexedOwnedMarkedAllocation.producer headers keys
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)).toOrdinary
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner
        (headers := headers) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) stable)
      (fun context size smaller scope id lowered certified => by
        obtain ⟨root⟩ := certified
        exact children size smaller root ⟨rfl, rfl, rfl⟩)
      unique tree rfl shape support.projection within entry.entry.environments entry.entry.heaps
      entry.entry.locals entry.entry.lookups entry.entry.actualTyped entry.entry.reference entry.entry.read
      entry.entry.unmapped reached conditioned admitted trace
  obtain ⟨value, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented evaluated
      packet.fellThrough packet.escaped entry.entry.embedding
  have outcomeEq := CallableIndexedOwnedAdmittedStagedLexicalFooter.outcome_eq matched
  subst outcome
  refine ⟨value, bodyStore, finalMap, finalWorld, ?_, representedBody, heaps,
    maps, worlds, frame, metadata, returned, related, post⟩
  simpa only [packet.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] using evaluatedBody

include support stable beforeTyped argumentsTyped in
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
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {nativeSize : Nat} (within : nativeSize ≤ budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.NativeBodyAt
      (stages := stages) (faults := callFaults)
      captured code history inputs functions owner caller entry reached packet.child nativeSize := by
  intro value bodyStore completed
  have rawTypes := Dynamic.MonoBindersExtend.bodyTypes_eq inputs.extended
  have rawArguments : Dynamic.ValuesHaveTypes function.context before arguments
      (function.parameters.map (fun binder => binder.scheme.body)) := by
    simpa only [rawTypes] using argumentsTyped
  have allocated := Dynamic.BindersAllocate.preservesHeapTyping beforeTyped rawArguments entry.allocation
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended
  have heapTyped : Dynamic.HeapWellTyped inputs.context entry.heap :=
    allocated.transportClosed fields.signatures valid.code.closed (fields.targetClosed valid.code.closed)
      valid.code.variables_closed (fields.targetResidualVariablesOpen valid.code.residual_variables_open)
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable entry.nextHistory entry.frame
  have admitted : CallableIndexedOwnedSourceAdmission.Admission
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      inputs.context reached := ⟨heapTyped, rows⟩
  have tree := support.tree packet.child packet.selected
  have shape : CallableIndexedOwnedPreparedStagedLexicalTree.Shape packet.child.source function.body := by
    rw [stages.source packet.selected]
    exact packet.shape
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position entry.nextHistory
  have bodyTrace := completed
  rw [packet.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] at bodyTrace
  obtain ⟨flowSize, flowValue, flowStore, flowTrace, strict⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.flow_prefix bodyTrace within
  obtain ⟨sourceSize, finalContext, bodyOutcome, after, finalMap, finalWorld, trace, represented, heaps,
      maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFlow.reflects
      CallableIndexedOwnedBodyRestorationAdmission.bridge
      (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
      functions rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
      (CallableIndexedOwnedMarkedAllocation.producer headers keys
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)).toOrdinary
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner
        (headers := headers) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) stable)
      (fun context size smaller scope id lowered certified => by
        obtain ⟨root⟩ := certified
        exact children size smaller root ⟨rfl, rfl, rfl⟩)
      tree rfl shape support.projection (Nat.le_of_lt strict) entry.environments entry.heaps
      entry.locals entry.lookups entry.actualTyped entry.reference entry.read entry.unmapped reached
      conditioned admitted flowTrace
  obtain ⟨bodyValue, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented flowTrace.sound
      packet.fellThrough packet.escaped entry.embedding
  obtain ⟨sameValue, sameStore⟩ := evaluation_deterministic bodyTrace.sound evaluatedBody
  subst bodyValue
  subst flowStore
  exact ⟨sourceSize, finalContext, bodyOutcome, _, after, finalMap, finalWorld, trace,
    represented.body_result, representedBody, heaps, maps, worlds, frame, metadata, returned, related, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaBodyBounds
