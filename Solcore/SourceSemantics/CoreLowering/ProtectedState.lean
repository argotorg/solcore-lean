import Solcore.SourceSemantics.CoreLowering.TypedGenericExpressionMeaning

/-! Protected state is carried by an actual dependent witness. Expression
results relate that witness to the reached witness, so state created by a child
can be passed to the next child. The same index also covers lexical and body
states. Administrative transport preserves the complete record observation.
These contracts use the existing Source and Core grades and supply no execution
theorem or induction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof

universe u v

structure Index where
  scope : SourceCoreLocalCell.Scope
  mapping : LocationMap
  world : StoreTyping
  heap : Dynamic.Heap
  store : Store
  canonical : Environment

def Index.extend (initial : Index) (mapping : LocationMap) (world : StoreTyping)
    (heap : Dynamic.Heap) (store : Store) : Index :=
  { initial with mapping := mapping, world := world, heap := heap, store := store }

/-- A relation keeps its concrete endpoint witnesses. Its record observation
may, for example, be all ordered record lists in an authority pool. -/
structure Protocol (Records : Type v) where
  State : Index → Type u
  records : {index : Index} → State index → Records
  Relates : {initial reached : Index} → State initial → State reached → Prop
  refl : ∀ {index} (state : State index), Relates state state
  trans : ∀ {initial middle reached} {first : State initial} {second : State middle}
    {last : State reached}, Relates first second → Relates second last → Relates first last

variable {Records : Type v} (protocol : Protocol.{u, v} Records)

def entry : SourceCoreLocalCell.Scope → LocationMap → StoreTyping →
    Dynamic.Heap → Store → Environment → Prop :=
  fun scope mapping world heap store canonical =>
    Nonempty (protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)

/-- The reached witness is retained together with its relation to this input. -/
def Transition {initial : Index} (state : protocol.State initial) (reached : Index) : Prop :=
  ∃ final : protocol.State reached, protocol.Relates state final

theorem Transition.refl {index : Index} (state : protocol.State index) :
    Transition protocol state index := ⟨state, protocol.refl state⟩

theorem Transition.of_related {initial reached : Index}
    {state : protocol.State initial} {final : protocol.State reached}
    (related : protocol.Relates state final) : Transition protocol state reached :=
  ⟨final, related⟩

theorem Transition.entry {initial reached : Index} {state : protocol.State initial}
    (transition : Transition protocol state reached) :
    entry protocol reached.scope reached.mapping reached.world reached.heap reached.store reached.canonical := by
  obtain ⟨final, _⟩ := transition
  exact ⟨final⟩

/-- Sequential composition consumes the actual first post-witness. -/
theorem Transition.then {initial middle reached : Index} {state : protocol.State initial}
    (first : Transition protocol state middle)
    (next : ∀ final : protocol.State middle, protocol.Relates state final →
      Transition protocol final reached) : Transition protocol state reached := by
  obtain ⟨middleState, related⟩ := first
  obtain ⟨final, last⟩ := next middleState related
  exact ⟨final, protocol.trans related last⟩

/-- Ordinary administrative effects transport one witness and preserve its
complete record observation. Record-producing transitions are proved directly
with `Protocol.Relates`, rather than defined by this transport operation. -/
structure AdministrativeTransport where
  extend : ∀ {initial : Index} (_state : protocol.State initial)
    {mapping world heap store},
    LocationMap.Extends initial.mapping mapping → WorldExtends initial.world world →
    AdministrativePreserved initial.mapping initial.store mapping store →
    Dynamic.HeapMetadataExtend initial.heap heap →
    protocol.State (initial.extend mapping world heap store)
  related : ∀ {initial : Index} (state : protocol.State initial)
    {mapping world heap store}
    (maps : LocationMap.Extends initial.mapping mapping) (worlds : WorldExtends initial.world world)
    (frame : AdministrativePreserved initial.mapping initial.store mapping store)
    (metadata : Dynamic.HeapMetadataExtend initial.heap heap),
    protocol.Relates state (extend state maps worlds frame metadata)
  records_eq : ∀ {initial : Index} (state : protocol.State initial)
    {mapping world heap store}
    (maps : LocationMap.Extends initial.mapping mapping) (worlds : WorldExtends initial.world world)
    (frame : AdministrativePreserved initial.mapping initial.store mapping store)
    (metadata : Dynamic.HeapMetadataExtend initial.heap heap),
    protocol.records (extend state maps worlds frame metadata) = protocol.records state

theorem AdministrativeTransport.transition (transport : AdministrativeTransport protocol)
    {initial : Index} (state : protocol.State initial) {mapping world heap store}
    (maps : LocationMap.Extends initial.mapping mapping) (worlds : WorldExtends initial.world world)
    (frame : AdministrativePreserved initial.mapping initial.store mapping store)
    (metadata : Dynamic.HeapMetadataExtend initial.heap heap) :
    Transition protocol state (initial.extend mapping world heap store) :=
  ⟨transport.extend state maps worlds frame metadata, transport.related state maps worlds frame metadata⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
