import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCanonicalState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedInvocationBounds

/-! A real named hook and its exact specialization record authorize the full
Source metadata at the selected physical frame. The actual parameter entry
then supplies the frame reference, argument bundle and original global slots
beside the same reached pool used by the body. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedCanonicalEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedFunctionState
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (header : CallableIndexedOwnedFunctionValues.Header compiled program)

/-- This condition retains the physical selected owner and the complete
original named Source seed. It makes no assertion about body execution. -/
def condition : BodyCondition (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
    functions registry header :=
  fun {_ _ _ _ _ _ _ _ _ frameLocation current ghost} _ =>
    frameLocation = owner.key.frameLocation ∧
    Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table current ghost
      (some (CallableIndexedNamedGeneration.state header.named))

/-- The genuine compiler record fixes the Source seed retained by the actual
hook's named history, including its original source and substitution. -/
theorem authorized :
    CallableIndexedOwnedInvocationBounds.BodyAuthorizationAt
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header owner.key.frameLocation (condition functions owner header) := by
  intro origin index metadata arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation
    physical selected carried _emitted _entry
  have record := CallableIndexedActualNamedSourceReceipts.header_record compiled header
  have generated := CallableIndexedNamedGeneration.seed compiled.indexed selected record
  have authenticated := carried.authenticates
  cases authenticated with
  | named actual =>
    have same : metadata = CallableIndexedNamedGeneration.state header.named :=
      Option.some.inj (actual.symm.trans generated)
    exact ⟨physical, same ▸ carried⟩

/-- The same physical and Source receipts supply the original allocation gate. -/
theorem stable_owner
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    (allowed : condition functions owner header entry) :
    CallableIndexedOwnedAllocationProducer.StableOwner keys frameLocation current :=
  ⟨owner.position, ghost, some (CallableIndexedNamedGeneration.state header.named), allowed.1.symm, allowed.2⟩

variable {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations owner.key.capturePrefix functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)
  (initial : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)

/-- A complete real parameter entry supplies every nested formation observation.
The Source metadata comes from the genuine hook condition, not pool ownership. -/
theorem packet (captureZero : owner.key.capturePrefix = 0)
    (globals : header.globals = compiled.indexed.base.globals.length)
    (allowed : condition functions owner header entry) :
    CallableIndexedOwnedNestedCanonicalState.Packet owner header _ initial := by
  apply CallableIndexedOwnedNestedCanonicalState.packet_of_stable_read owner header initial
  · refine ⟨?_, ?_⟩
    · intro target member
      simpa only [captureZero, Nat.zero_add] using entry.catalog.globals target member
    · simpa only [List.length_map, List.length_reverse, globals, allowed.1] using entry.reference
  · exact entry.environments
  · rw [header.parameterType]
    rfl
  · exact allowed.2
  · simpa only [allowed.1] using entry.state.read

/-- The proof wrapper contains the original reached pool verbatim. -/
def wrap (captureZero : owner.key.capturePrefix = 0)
    (globals : header.globals = compiled.indexed.base.globals.length)
    (allowed : condition functions owner header entry) :
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header).State
      ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ :=
  ⟨initial, packet functions owner header entry initial captureZero globals allowed⟩

theorem wrap_pool (captureZero : owner.key.capturePrefix = 0)
    (globals : header.globals = compiled.indexed.base.globals.length)
    (allowed : condition functions owner header entry) :
    (wrap functions owner header entry initial captureZero globals allowed).val = initial := rfl

section Meaning
variable {faults : FunctionCalls.FaultRep}

/-- Specialize the nested body proof at its complete actual parameter input,
then return the same reached base pool after forgetting only the packet. -/
theorem preserves_of_nested (captureZero : owner.key.capturePrefix = 0)
    (globals : header.globals = compiled.indexed.base.globals.length) (size : Nat)
    (meaning : RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
      (condition functions owner header) size) :
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys) (condition functions owner header) size := by
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
    entry initial outcome after allowed trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, returned, related⟩ :=
    meaning entry (wrap functions owner header entry initial captureZero globals allowed) allowed trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, returned.val, related⟩

/-- The independent Source grade and complete actual native post survive the
same proof-wrapper projection. -/
theorem reflects_of_nested (captureZero : owner.key.capturePrefix = 0)
    (globals : header.globals = compiled.indexed.base.globals.length) (size : Nat)
    (meaning : RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
      (condition functions owner header) size) :
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys) (condition functions owner header) size := by
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
    entry initial value finalStore allowed completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, returned, related⟩ :=
    meaning entry (wrap functions owner header entry initial captureZero globals allowed) allowed completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, returned.val, related⟩

end Meaning

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedCanonicalEntries
