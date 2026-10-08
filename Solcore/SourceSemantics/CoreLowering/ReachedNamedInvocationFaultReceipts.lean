import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedInvocationBounds

/-! Finite projections of the same actual body receipt. The fault token is
unchanged by caller restoration; the body post remains at its original store. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedNamedInvocationFaultReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open CallableIndexedOwnedInvocationBounds NamedInvocationFaultPostContracts

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {post : BodyFaultPost}

section Body
variable {locations : CallableIndexedOwnedFunctionValues.Header compiled program → Location}
  {capturePrefix : Nat} {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  {entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost}
  {reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩} {size : Nat}

theorem source_body_forget (meaning : SourceBodyAtWithPost post (faults := faults) entry reached size) :
    SourceBodyAt (faults := faults) entry reached size := by
  intro outcome after trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluation, result, heaps,
    maps, worlds, frame, metadata, returned, _post⟩ := meaning trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluation, result, heaps,
    maps, worlds, frame, metadata, returned⟩

theorem native_body_forget (meaning : NativeBodyAtWithPost post (faults := faults) entry reached size) :
    NativeBodyAt (faults := faults) entry reached size := by
  intro value finalStore completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps,
    maps, worlds, frame, metadata, returned, _post⟩ := meaning completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps,
    maps, worlds, frame, metadata, returned⟩
end Body

section Continuation
variable {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment} {arguments : List Dynamic.Value}
  {owner : CallableIndexedOwnedFunctionValues.OwnedKey keys}
  {caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩}
  {condition : BodyCondition (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header}
  {budget : Nat}

theorem source_continuation_forget
    (meaning : SourceContinuationWithPost (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) (post := post) owner caller condition budget) :
    SourceContinuation (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) owner caller condition budget := by
  intro origin index metadata administrative actualContext actual ξ frameLocation
    physical owned history emitted entry agreement reached related allowed child strict
  exact source_body_forget (meaning physical owned history emitted entry agreement reached related allowed child strict)

theorem native_continuation_forget
    (meaning : NativeContinuationWithPost (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) (post := post) owner caller condition budget) :
    NativeContinuation (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) owner caller condition budget := by
  intro origin index metadata administrative actualContext actual ξ frameLocation prefixSize bodyStore value finalStore
    physical owned history emitted prefixCompleted prefixWithin restored entry reached related allowed child strict
  exact native_body_forget (meaning physical owned history emitted prefixCompleted prefixWithin restored
    entry reached related allowed child strict)
end Continuation

section Returned
variable {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store} {canonical : Environment}
  {owner : CallableIndexedOwnedFunctionValues.OwnedKey keys}
  {caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩}
  {arguments : List Dynamic.Value} {sourceParent : Nat} {nativeBudget : Option Nat}
  {after : Dynamic.Heap} {value : Value} {finalMap : LocationMap} {finalWorld : StoreTyping} {finalStore : Store}

/-- The same body word passes through the original frame restoration. No
primitive origin is inferred from the ordinary result relation. -/
theorem fault_word {reason : Dynamic.SemanticFault}
    (receipt : ReturnedAt (header := header) (functions := functions) (registry := registry)
      post sourceParent nativeBudget owner caller arguments (.fault reason) after value finalMap finalWorld finalStore) :
    ∃ token, value = .inLeft header.output (.word token) := by
  obtain ⟨origin, index, metadata, administrative, actualContext, actual, ξ, entry, parameterState,
    sourceSize, bodyStore, bodyState, owned, history, emitted, parameterRelated, bodyRelated,
    trace, smaller, evaluation, bodyPost, measured, related, restored, cell, returnedRelated,
    callerRelated, records⟩ := receipt
  exact ⟨bodyPost.choose, bodyPost.choose_spec.1⟩

/-- The same retained receipt supplies a real restored pool and its unchanged
ordered records. The body post is still indexed by the pre-restoration store. -/
theorem restored_pool {outcome : Dynamic.ExpressionOutcome}
    (receipt : ReturnedAt (header := header) (functions := functions) (registry := registry)
      post sourceParent nativeBudget owner caller arguments outcome after value finalMap finalWorld finalStore) :
    ∃ (bodyScope : SourceCoreLocalCell.Scope) (bodyCanonical : Environment) (bodyStore : Store)
      (bodyState : State headers keys ⟨bodyScope, finalMap, finalWorld, after, bodyStore, bodyCanonical⟩),
      finalStore = (CallableIndexedOwnedBodyRestoration.finalIndex caller owner.position
        (body := ⟨bodyScope, finalMap, finalWorld, after, bodyStore, bodyCanonical⟩)).store ∧
      Relates bodyState (CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position) ∧
      Relates caller (CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position) ∧
      records (CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position) = records bodyState := by
  obtain ⟨origin, index, metadata, administrative, actualContext, actual, ξ, entry, parameterState,
    sourceSize, bodyStore, bodyState, owned, history, emitted, parameterRelated, bodyRelated,
    trace, smaller, evaluation, bodyPost, measured, related, restored, cell, returnedRelated,
    callerRelated, records⟩ := receipt
  exact ⟨_, entry.canonical, bodyStore, bodyState, restored, returnedRelated, callerRelated, records⟩
end Returned
end Solcore.SourceSemantics.CoreLowering.ReachedNamedInvocationFaultReceipts
