import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaViewHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCanonicalState

/-! The emitted compiler function supplies a bundle type and full named seed.
Its independent Source origin remains in the authentic higher receipt. Actual
reached pools and their own ghosts remain intact through allocation and scope
restoration; no top-level Source Header is required. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOriginCanonicalState
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedExpressionHeads (Globals)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (principal : SourceCoreGeneralFunctions.Function)

/-- Full canonical frame and bundle observations remain independent of pool
ownership. Authentication uses the reached selected row's own ghost. -/
structure Packet (index : ProtectedStateTransition.Index)
    (initial : State headers keys index) : Prop where
  globals : Globals (headers := headers) owner 1 index.scope index.canonical
  reference : index.canonical[index.scope.length + 1 + compiled.indexed.base.globals.length]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation)
  bundle : (index.canonical.map Value.type)[index.scope.length]? = some principal.signature.parameterType
  carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (initial.rows owner.position).authority.current (initial.rows owner.position).authority.ghost
    (some (CallableIndexedNamedGeneration.state principal))

def protocol : ProtectedStateTransition.Protocol (Records keys) where
  State := fun index => { initial : State headers keys index // Packet owner principal index initial }
  records := fun initial => records initial.val
  Relates := fun initial reached => Relates initial.val reached.val
  refl := fun initial => Relates.refl initial.val
  trans := fun first last => first.trans last

/-- Only proofs are added: these are the original complete ordered lists. -/
theorem records_eq {index : ProtectedStateTransition.Index}
    (initial : (protocol (headers := headers) owner principal).State index) :
    (protocol owner principal).records initial = records initial.val := rfl

/-- The actual metadata/read packet supplies the original formation input. -/
theorem Packet.observed {index : ProtectedStateTransition.Index} {initial : State headers keys index}
    (packet : Packet owner principal index initial) :
    CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 index.scope index.canonical owner.key.frameLocation :=
  ⟨packet.globals, packet.reference⟩

/-- An authentic original stable read and the real environment prefix build
the entire packet at the selected actual pool, including its own ghost. -/
theorem packet_of_stable_read {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {administrative : Core.Context} {environment : Dynamic.Environment}
    (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope canonical owner.key.frameLocation)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (leading : administrative[0]? = some principal.signature.parameterType)
    {native : NativeFrame} {ghost : GhostFrame}
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost
      (some (CallableIndexedNamedGeneration.state principal)))
    (read : store.read? owner.key.frameLocation = some (encode compiled.indexed.ancestry.layout.frame native)) :
    Packet owner principal _ initial :=
  ⟨observed.globals, observed.reference,
    (by
      rw [related.runtime_hasTypes.type_tags]
      simpa [SourceCoreLocalCell.coreContext, List.getElem?_append] using leading),
    CallableIndexedOwnedLambdaViewHeads.carries_of_stable_read initial owner stable read⟩

/-- A real administrative effect keeps the actual input frame read. The
returned pool's own Current proof authenticates its full original metadata. -/
theorem Packet.after {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
    {heap after : Dynamic.Heap} {store futureStore : Store}
    {initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩}
    (packet : Packet owner principal _ initial)
    (reached : State headers keys ⟨scope, futureMap, futureWorld, after, futureStore, canonical⟩)
    (frame : AdministrativePreserved mapping store futureMap futureStore) :
    Packet owner principal _ reached := by
  have read := CallableIndexedOwnedFunctionEntries.reached_frame_read initial owner.position
  have unmapped : owner.key.frameLocation ∉ mapping := by
    have original := (initial.rows owner.position).authority.unmapped
    rw [(initial.rows owner.position).frame_eq] at original
    exact original
  have bound := (List.getElem?_eq_some_iff.mp read).1
  obtain ⟨_unmapped, unchanged⟩ := frame owner.key.frameLocation unmapped bound
  exact ⟨packet.globals, packet.reference, packet.bundle,
    CallableIndexedOwnedLambdaViewHeads.carries_of_stable_read reached owner packet.carried (unchanged.trans read)⟩

/-- Prepending the actual lexical value shifts all original canonical slots
and the bundle together; the actual pool and history are the same witness. -/
theorem Packet.prepend {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩}
    (packet : Packet owner principal _ initial) (id : Resolved.LocalId) (type : Ty) (value : Value) :
    Packet owner principal ⟨(id, type) :: scope, mapping, world, heap, store, value :: canonical⟩ initial := by
  refine ⟨CallableIndexedOwnedCanonicalState.globals_prepend owner 1 packet.globals id type value, ?_, ?_, packet.carried⟩
  · have offset : ((id, type) :: scope).length + 1 + compiled.indexed.base.globals.length =
        scope.length + 1 + compiled.indexed.base.globals.length + 1 := by simp; omega
    rw [offset]
    exact packet.reference
  · simpa only [List.map_cons, List.length_cons, List.getElem?_cons_succ] using packet.bundle

/-- Removing that same lexical slot restores the original observations while
retaining the actual reached pool, history and complete record lists. -/
theorem Packet.restore {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {id : Resolved.LocalId} {type : Ty} {value : Value}
    {initial : State headers keys ⟨(id, type) :: scope, mapping, world, heap, store, value :: canonical⟩}
    (packet : Packet owner principal _ initial) :
    Packet owner principal ⟨scope, mapping, world, heap, store, canonical⟩ initial := by
  refine ⟨CallableIndexedOwnedCanonicalState.globals_restore owner 1 packet.globals, ?_, ?_, packet.carried⟩
  · have offset : ((id, type) :: scope).length + 1 + compiled.indexed.base.globals.length =
        scope.length + 1 + compiled.indexed.base.globals.length + 1 := by simp; omega
    have reference := packet.reference
    rw [offset] at reference
    exact reference
  · have bundle := packet.bundle
    simpa only [List.map_cons, List.length_cons, List.getElem?_cons_succ] using bundle

/-- An existing actual transition is wrapped at the same returned pool; its
real administrative preservation supplies the additional observations. -/
theorem transition_of_reached {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
    {heap after : Dynamic.Heap} {store futureStore : Store}
    (initial : (protocol (headers := headers) owner principal).State ⟨scope, mapping, world, heap, store, canonical⟩)
    (transition : ProtectedStateTransition.Transition (CallableIndexedOwnedFunctionState.protocol headers keys) initial.val
      ⟨scope, futureMap, futureWorld, after, futureStore, canonical⟩)
    (frame : AdministrativePreserved mapping store futureMap futureStore) :
    ProtectedStateTransition.Transition (protocol owner principal) initial
      ⟨scope, futureMap, futureWorld, after, futureStore, canonical⟩ := by
  obtain ⟨reached, related⟩ := transition
  exact ⟨⟨reached, initial.property.after owner principal reached frame⟩, related⟩

def administrativeTransport : ProtectedStateTransition.AdministrativeTransport (protocol (headers := headers) owner principal) where
  extend := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata =>
    let reached := (CallableIndexedOwnedFunctionState.administrativeTransport headers keys).extend state.val maps worlds frame metadata
    ⟨reached, Packet.after owner principal state.property reached frame⟩
  related := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata =>
    (CallableIndexedOwnedFunctionState.administrativeTransport headers keys).related state.val maps worlds frame metadata
  records_eq := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata =>
    (CallableIndexedOwnedFunctionState.administrativeTransport headers keys).records_eq state.val maps worlds frame metadata

def bindings : ProtectedStateTransition.Bindings (protocol (headers := headers) owner principal) where
  prepend := fun state id type value => ⟨state.val, Packet.prepend owner principal state.property id type value⟩
  prepend_related := fun state _ _ _ => Relates.refl state.val
  prepend_records := fun _ _ _ _ => rfl
  restore := fun state => ⟨state.val, Packet.restore owner principal state.property⟩
  restore_related := fun state => Relates.refl state.val
  restore_records := fun _ => rfl

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)

/-- The genuine marked allocator's real reached pool and actual prepended
reference supply the new packet. Its complete record-producing post is kept. -/
def markedProducer : ProtectedStateTransition.MarkedAllocation.Producer
    (protocol (headers := headers) owner principal) compiled.indexed.layouts compiled.indexed.ancestry.layout.frame model where
  Ready := fun state location native => (CallableIndexedOwnedMarkedAllocation.producer headers keys model).Ready state.val location native
  complete := by
    intro allocationOwner active request globals allocate allocation annotation same definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native sourceType payload sourceValue sourceLocation
      environments agrees heaps reference read payloadAt cell allocated initial ready
    obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame, transition⟩ :=
      (CallableIndexedOwnedMarkedAllocation.producer headers keys model).complete allocation annotation same definitions registered
        environments agrees heaps reference read payloadAt cell allocated initial.val ready
    obtain ⟨reached, related⟩ := transition
    have retained : Packet owner principal ⟨request.scope, _, _, after, _, canonical⟩ reached :=
      Packet.after owner principal initial.property reached frame
    exact ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame,
      ⟨⟨reached, Packet.prepend owner principal retained request.binder.id request.payloadType
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))⟩, related⟩⟩

theorem readyAt_of_stableOwner {location : Location} {native : NativeFrame}
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt (markedProducer (headers := headers) owner principal model).toOrdinary location native := by
  intro index state read
  exact CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner (headers := headers) model stable state.val read

/-- The caller bridge restores the same actual pool using its real retained
frame read, preserving all complete ordered records. -/
def carrier : CallableIndexedOwnedNamedCallerProtocol.Carrier
    (headers := headers) (fun index => Globals (headers := headers) owner 1 index.scope index.canonical) (protocol (headers := headers) owner principal) where
  pool := fun state => state.val
  records_eq := fun _ => rfl
  related := fun related => related
  slots := fun state => state.property.globals
  restore := by
    intro index initial mapping world heap store reached maps worlds frame metadata related
    exact ⟨⟨reached, Packet.after owner principal initial.property reached frame⟩, rfl, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOriginCanonicalState
