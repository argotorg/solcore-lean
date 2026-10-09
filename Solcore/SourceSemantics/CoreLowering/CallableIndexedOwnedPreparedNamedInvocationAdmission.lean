import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedParameterReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyRestorationAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedInvocationBounds

/-! The strong named parameter result supplies the exit and admission at the
actual completed body pool. The generic invocation core retains that same
witness through its sole caller restoration. This downstream adapter adds
caller admission using only the pure post helper. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedInvocationAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedParameterMeaning
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open RecursiveNamedBoundedContracts

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}

/-- The real lexical exit and post share the completed body's actual pool.
The lexical environment uses the whole parameter administrative suffix. -/
def exit_admission_extra : NamedInvocationFaultPostContracts.BodyExtra
    (headers := headers) (keys := keys) (functions := functions)
    (registry := registry) (header := header) :=
  fun {_locations} {_capturePrefix} {_arguments} {_before} {_initialStore}
    {_initialMap} {_initialWorld} {administrative} {_actualContext} {_actual}
    {_ξ} {_frameLocation} {_current} {_ghost}
    entry _parameterState outcome after _value finalMap finalWorld _bodyStore bodyState =>
    TypedMixedNamedBody.ReachedExit compiled.compatible.checked
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions
      finalMap finalWorld
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      program header.function header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      entry.environment entry.heap after outcome ∧
    PostAdmission CallableIndexedOwnedBodyRestorationAdmission.bridge
      header.context header.function.resultType outcome bodyState

/-- Caller admission concerns the original returned body pool, with its saved
caller cell and source spine restored. The body exit and post remain retained. -/
def restored_exit_admission_extra {initial : ProtectedStateTransition.Index}
    (saved : State headers keys initial) (callerContext : SourceSemantics.Context)
    (selected : Fin keys.length) : NamedInvocationFaultPostContracts.BodyExtra
      (headers := headers) (keys := keys) (functions := functions)
      (registry := registry) (header := header) :=
  fun {_locations} {_capturePrefix} {_arguments} {_before} {_initialStore}
    {_initialMap} {_initialWorld} {_administrative} {_actualContext} {_actual}
    {_ξ} {_frameLocation} {_current} {_ghost}
    entry parameterState outcome after value finalMap finalWorld bodyStore bodyState =>
    exit_admission_extra (functions := functions) (registry := registry) (header := header)
      entry parameterState outcome after value finalMap finalWorld bodyStore bodyState ∧
    PostAdmission CallableIndexedOwnedBodyRestorationAdmission.bridge
      callerContext header.function.resultType outcome
      (CallableIndexedOwnedBodyRestoration.returned saved bodyState selected)

section Pointwise
variable {owner : CallableIndexedOwnedFunctionValues.OwnedKey keys}
  {initial : ProtectedStateTransition.Index} {caller : State headers keys initial}
  {arguments : List Dynamic.Value} {faults : FunctionCalls.FaultRep}

/-- Consume the strong Source receipt once and retain its same body witness. -/
theorem source_body_with_extra_at_receipt
    (receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt
      (registry := registry) functions owner caller header arguments)
    {size : Nat}
    (meaning : CallableIndexedOwnedPreparedNamedParameterReceipts.PreservesAt
      receipt (faults := faults) size) :
    CallableIndexedOwnedInvocationBounds.SourceBodyAtWithExtra
      NamedInvocationFaultPostContracts.Trivial
      (exit_admission_extra (functions := functions) (registry := registry) (header := header))
      (faults := faults) receipt.body receipt.reached size := by
  intro outcome after trace
  obtain ⟨value, bodyStore, finalMap, finalWorld, evaluated, represented, heaps,
    maps, worlds, frame, metadata, exit, bodyState, related, post⟩ := meaning trace
  have bodyPost : PostAdmission CallableIndexedOwnedBodyRestorationAdmission.bridge
      header.context header.function.resultType outcome bodyState := post
  exact ⟨value, bodyStore, finalMap, finalWorld, evaluated, represented, heaps,
    maps, worlds, frame, metadata, ⟨bodyState, related, exit, bodyPost⟩,
    NamedInvocationFaultPostContracts.trivial_of_result represented⟩

/-- The native input returns its independent Source grade and actual body pool. -/
theorem native_body_with_extra_at_receipt
    (receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt
      (registry := registry) functions owner caller header arguments)
    {size : Nat}
    (meaning : CallableIndexedOwnedPreparedNamedParameterReceipts.ReflectsAt
      receipt (faults := faults) size) :
    CallableIndexedOwnedInvocationBounds.NativeBodyAtWithExtra
      NamedInvocationFaultPostContracts.Trivial
      (exit_admission_extra (functions := functions) (registry := registry) (header := header))
      (faults := faults) receipt.body receipt.reached size := by
  intro value bodyStore completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, _evaluated,
    represented, heaps, maps, worlds, frame, metadata, exit, bodyState, related, post⟩ :=
    meaning completed
  have bodyPost : PostAdmission CallableIndexedOwnedBodyRestorationAdmission.bridge
      header.context header.function.resultType outcome bodyState := post
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
    heaps, maps, worlds, frame, metadata, ⟨bodyState, related, exit, bodyPost⟩,
    NamedInvocationFaultPostContracts.trivial_of_result represented⟩

end Pointwise

section Continuations
variable (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store} {canonical : Environment}
  (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  {arguments : List Dynamic.Value} {faults : FunctionCalls.FaultRep}
  (condition : BodyCondition (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (headers := headers) (locations := owner.key.locations)
    (capturePrefix := owner.key.capturePrefix) functions registry header)

/-- The actual hook and parameter callback construct one genuine receipt;
independent raw argument admission and saved rows belong to this caller. -/
theorem source_continuation_with_extra (budget : Nat)
    (savedRows : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context heap arguments header.types)
    (bodies : CallableIndexedOwnedPreparedNamedParameterReceipts.SourceBodiesFor
      (headers := headers) (functions := functions) (owner := owner)
      (registry := registry) (faults := faults) header budget) :
    CallableIndexedOwnedInvocationBounds.SourceContinuationWithExtra
      (post := NamedInvocationFaultPostContracts.Trivial)
      (extra := exit_admission_extra (functions := functions) (registry := registry) (header := header))
      (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) owner caller condition budget := by
  intro origin index metadata administrative actualContext actual ξ frameLocation
    physical selected history emitted entry agreement parameterState related _allowed child strict
  let receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt
      (registry := registry) functions owner caller header arguments :=
    { origin := origin, index := index, metadata := metadata,
      administrative := administrative, actualContext := actualContext, actual := actual,
      embedding := ξ, frameLocation := frameLocation, physical := physical,
      selected := selected, history := history, emitted := emitted, body := entry,
      reached := parameterState, related := related, stable := savedRows,
      heapTyped := heapTyped, argumentsTyped := argumentsTyped }
  intro outcome after trace
  exact source_body_with_extra_at_receipt receipt
    (bodies receipt agreement child strict) trace

/-- Keep the original measured native prefix and its restoration equation.
No parameter action or saved-cell restoration is repeated. -/
theorem native_continuation_with_extra (budget : Nat)
    (savedRows : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context heap arguments header.types)
    (bodies : CallableIndexedOwnedPreparedNamedParameterReceipts.NativeBodiesFor
      (headers := headers) (functions := functions) (owner := owner)
      (registry := registry) (faults := faults) header budget) :
    CallableIndexedOwnedInvocationBounds.NativeContinuationWithExtra
      (post := NamedInvocationFaultPostContracts.Trivial)
      (extra := exit_admission_extra (functions := functions) (registry := registry) (header := header))
      (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) owner caller condition budget := by
  intro origin index metadata administrative actualContext actual ξ frameLocation
    prefixSize bodyStore value finalStore physical selected history emitted prefixRun
    prefixWithin restored entry parameterState related _allowed child strict
  let receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt
      (registry := registry) functions owner caller header arguments :=
    { origin := origin, index := index, metadata := metadata,
      administrative := administrative, actualContext := actualContext, actual := actual,
      embedding := ξ, frameLocation := frameLocation, physical := physical,
      selected := selected, history := history, emitted := emitted, body := entry,
      reached := parameterState, related := related, stable := savedRows,
      heapTyped := heapTyped, argumentsTyped := argumentsTyped }
  intro bodyValue completedStore completed
  exact native_body_with_extra_at_receipt receipt
    (bodies receipt prefixRun prefixWithin restored child strict) completed

end Continuations

section Returned
variable {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store} {canonical : Environment}
  {owner : CallableIndexedOwnedFunctionValues.OwnedKey keys}
  {caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩}
  {callerContext : SourceSemantics.Context}
  {post : NamedInvocationFaultPostContracts.BodyFaultPost}
  {sourceParent : Nat} {nativeBudget : Option Nat}
  {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
  {value : Value} {finalMap : LocationMap} {finalWorld : StoreTyping} {finalStore : Store}

/-- Extend only the fact inside the existing causal receipt. The original
restored frame authenticates every saved/reached row at that same returned pool. -/
theorem returned_at_with_admission
    (savedRows : StableRows caller)
    (supports : Dynamic.TypeContextSupports header.context callerContext)
    (receipt : NamedInvocationFaultPostContracts.ReturnedAtWithExtra
      (header := header) (functions := functions) (registry := registry) post
      (exit_admission_extra (functions := functions) (registry := registry) (header := header))
      sourceParent nativeBudget owner caller arguments outcome after value finalMap finalWorld finalStore) :
    NamedInvocationFaultPostContracts.ReturnedAtWithExtra
      (header := header) (functions := functions) (registry := registry) post
      (restored_exit_admission_extra (functions := functions) (registry := registry)
        (header := header) caller callerContext owner.position)
      sourceParent nativeBudget owner caller arguments outcome after value finalMap finalWorld finalStore := by
  obtain ⟨origin, index, metadata, administrative, actualContext, actual, ξ,
    entry, parameterState, sourceSize, bodyStore, bodyState, selected, history, emitted,
    parameterRelated, bodyRelated, trace, smaller, evaluated, bodyPost, measured,
    related, sameStore, restoredCell, fromBody, fromCaller, sameRecords, extra, restoredFrame⟩ := receipt
  have postAtBody : PostAdmission CallableIndexedOwnedBodyRestorationAdmission.bridge
      header.context header.function.resultType outcome bodyState := extra.2
  have postAtCaller := CallableIndexedOwnedBodyRestorationAdmission.restore_post
    caller bodyState owner.position savedRows postAtBody supports restoredFrame
  exact ⟨origin, index, metadata, administrative, actualContext, actual, ξ,
    entry, parameterState, sourceSize, bodyStore, bodyState, selected, history, emitted,
    parameterRelated, bodyRelated, trace, smaller, evaluated, bodyPost, measured,
    related, sameStore, restoredCell, fromBody, fromCaller, sameRecords,
    ⟨extra, postAtCaller⟩, restoredFrame⟩

/-- Faults add only the returned stable-row post; no context support or
successful raw value/deep heap typing is inferred. The original exit is retained. -/
theorem returned_fault_at_with_admission {reason : Dynamic.SemanticFault}
    (savedRows : StableRows caller)
    (receipt : NamedInvocationFaultPostContracts.ReturnedAtWithExtra
      (header := header) (functions := functions) (registry := registry) post
      (exit_admission_extra (functions := functions) (registry := registry) (header := header))
      sourceParent nativeBudget owner caller arguments (.fault reason) after value finalMap finalWorld finalStore) :
    NamedInvocationFaultPostContracts.ReturnedAtWithExtra
      (header := header) (functions := functions) (registry := registry) post
      (restored_exit_admission_extra (functions := functions) (registry := registry)
        (header := header) caller callerContext owner.position)
      sourceParent nativeBudget owner caller arguments (.fault reason) after value finalMap finalWorld finalStore := by
  obtain ⟨origin, index, metadata, administrative, actualContext, actual, ξ,
    entry, parameterState, sourceSize, bodyStore, bodyState, selected, history, emitted,
    parameterRelated, bodyRelated, trace, smaller, evaluated, bodyPost, measured,
    related, sameStore, restoredCell, fromBody, fromCaller, sameRecords, extra, restoredFrame⟩ := receipt
  have postAtCaller : PostAdmission CallableIndexedOwnedBodyRestorationAdmission.bridge
      callerContext header.function.resultType (.fault reason)
      (CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position) :=
    CallableIndexedOwnedBodyRestorationAdmission.restore_fault_post
      caller bodyState owner.position savedRows restoredFrame
  exact ⟨origin, index, metadata, administrative, actualContext, actual, ξ,
    entry, parameterState, sourceSize, bodyStore, bodyState, selected, history, emitted,
    parameterRelated, bodyRelated, trace, smaller, evaluated, bodyPost, measured,
    related, sameStore, restoredCell, fromBody, fromCaller, sameRecords,
    ⟨extra, postAtCaller⟩, restoredFrame⟩

end Returned

section Invocations
variable {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store}

/-- The original invocation core consumes the strong body callback once.
Caller admission is added purely inside its same returned causal receipt. -/
theorem invocation_preserves_bounded_at_with_admission
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (condition : BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header)
    (authorized : CallableIndexedOwnedInvocationBounds.BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header owner.key.frameLocation condition)
    (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (_member : header ∈ headers)
    (capture : Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix (caller.rows owner.position).authority.frameLocation header mapping world heap store)
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    (callerContext : SourceSemantics.Context)
    (savedRows : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context heap arguments header.types)
    (supports : Dynamic.TypeContextSupports header.context callerContext)
    (bodies : CallableIndexedOwnedPreparedNamedParameterReceipts.SourceBodiesFor
      (headers := headers) (functions := functions) (owner := owner)
      (registry := registry) (faults := faults) header budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome program size header.sourceBody header.function.evidence heap arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
        (header.code.rename capture.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      NamedInvocationFaultPostContracts.ReturnedAtWithExtra (header := header) (functions := functions)
        (registry := registry) NamedInvocationFaultPostContracts.Trivial
        (restored_exit_admission_extra (functions := functions) (registry := registry)
          (header := header) caller callerContext owner.position) size (none) owner caller arguments outcome after value finalMap finalWorld finalStore := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
    finalHeaps, maps, worlds, frame, metadata, transition, returned⟩ :=
    CallableIndexedOwnedInvocationBounds.invocation_preserves_bounded_at_with_extra
      (faults := faults) owner sameLayouts condition authorized budget caller
      _member capture represented heaps NamedInvocationFaultPostContracts.Trivial
      (exit_admission_extra (functions := functions) (registry := registry) (header := header))
      (source_continuation_with_extra owner caller condition budget
        savedRows heapTyped argumentsTyped bodies) trace within
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
    finalHeaps, maps, worlds, frame, metadata, transition,
    returned_at_with_admission savedRows supports returned⟩

/-- The original invocation core consumes the strong body callback once.
Caller admission is added purely inside its same returned causal receipt. -/
theorem invocation_reflects_bounded_at_with_admission
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (condition : BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header)
    (authorized : CallableIndexedOwnedInvocationBounds.BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header owner.key.frameLocation condition)
    (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (_member : header ∈ headers)
    (capture : Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix (caller.rows owner.position).authority.frameLocation header mapping world heap store)
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    (callerContext : SourceSemantics.Context)
    (savedRows : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context heap arguments header.types)
    (supports : Dynamic.TypeContextSupports header.context callerContext)
    (bodies : CallableIndexedOwnedPreparedNamedParameterReceipts.NativeBodiesFor
      (headers := headers) (functions := functions) (owner := owner)
      (registry := registry) (faults := faults) header budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome program sourceSize header.sourceBody header.function.evidence heap arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      NamedInvocationFaultPostContracts.ReturnedAtWithExtra (header := header) (functions := functions)
        (registry := registry) NamedInvocationFaultPostContracts.Trivial
        (restored_exit_admission_extra (functions := functions) (registry := registry)
          (header := header) caller callerContext owner.position) sourceSize (some size) owner caller arguments outcome after value finalMap finalWorld finalStore := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
    finalHeaps, maps, worlds, frame, metadata, transition, returned⟩ :=
    CallableIndexedOwnedInvocationBounds.invocation_reflects_bounded_at_with_extra
      (faults := faults) owner sameLayouts condition authorized budget caller
      _member capture represented heaps NamedInvocationFaultPostContracts.Trivial
      (exit_admission_extra (functions := functions) (registry := registry) (header := header))
      (native_continuation_with_extra owner caller condition budget
        savedRows heapTyped argumentsTyped bodies) completed within
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
    finalHeaps, maps, worlds, frame, metadata, transition,
    returned_at_with_admission savedRows supports returned⟩

end Invocations
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedInvocationAdmission
