import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalGlobals
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedCallerProtocol
import Solcore.SourceSemantics.CoreLowering.ProtectedStateMarkedAllocation

/-! A physical cache layer retains the original caller and its exact ordered
history. It can wrap ordinary or stronger canonical callers. Existing pool
and semantic Header interfaces remain available by projection. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalState
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedHistory
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

structure State (caller : ProtectedStateTransition.Protocol.{u, 0} (Records keys))
    (index : ProtectedStateTransition.Index) where
  base : caller.State index
  physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store

def protocol (caller : ProtectedStateTransition.Protocol.{u, 0} (Records keys)) :
    ProtectedStateTransition.Protocol.{u, 0} (Records keys) where
  State := State caller
  records := fun state => caller.records state.base
  Relates := fun first last => caller.Relates first.base last.base
  refl := fun state => caller.refl state.base
  trans := fun first last => caller.trans first last

variable {caller : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}

def administrativeTransport (transport : ProtectedStateTransition.AdministrativeTransport caller) :
    ProtectedStateTransition.AdministrativeTransport (protocol caller) where
  extend := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata =>
    ⟨transport.extend state.base maps worlds frame metadata, state.physical.extend frame⟩
  related := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata => transport.related state.base maps worlds frame metadata
  records_eq := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata => transport.records_eq state.base maps worlds frame metadata

/-- Lexical slots affect the canonical environment only. The actual store and
Source map remain unchanged at these administrative scope operations. -/
def bindings (bindings : ProtectedStateTransition.Bindings caller) :
    ProtectedStateTransition.Bindings (protocol caller) where
  prepend := fun state id type value => ⟨bindings.prepend state.base id type value, state.physical⟩
  prepend_related := fun state id type value => bindings.prepend_related state.base id type value
  prepend_records := fun state id type value => bindings.prepend_records state.base id type value
  restore := fun state => ⟨bindings.restore state.base, state.physical⟩
  restore_related := fun state => bindings.restore_related state.base
  restore_records := fun state => bindings.restore_records state.base

/-- The same genuine marked allocation keeps its new snapshot and Source
cell, while its proved administrative frame preserves all cached globals. -/
def markedProducer {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {layouts : SourceCoreAllocationLayouts.Prepared}
    {layout : SourceCoreCallableIndexedFrames.Layout}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (producer : ProtectedStateTransition.MarkedAllocation.Producer caller layouts layout model) :
    ProtectedStateTransition.MarkedAllocation.Producer (protocol caller) layouts layout model where
  Ready := fun state location native => producer.Ready state.base location native
  complete := by
    intro owner active request globals allocate allocation annotation same definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native sourceType payload sourceValue sourceLocation
      environments agrees heaps reference read payloadAt cell allocated initial ready
    obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame, final, related⟩ :=
      producer.complete allocation annotation same definitions registered
        environments agrees heaps reference read payloadAt cell allocated initial.base ready
    exact ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame,
      ⟨final, initial.physical.extend frame⟩, related⟩

/-- Returning uses the actual reached pool and genuine administrative frame
receipt. Physical cells are never inferred from an arbitrary pool. -/
def carrier {slots : ProtectedStateTransition.Index → Prop}
    (original : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) slots caller) :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun index => slots index ∧ CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store)
      (protocol caller) where
  pool := fun state => original.pool state.base
  records_eq := fun state => original.records_eq state.base
  related := original.related
  slots := fun state => ⟨original.slots state.base, state.physical⟩
  restore := by
    intro index initial mapping world heap store reached maps worlds frame metadata related
    obtain ⟨returned, same, related⟩ := original.restore initial.base reached maps worlds frame metadata related
    exact ⟨⟨returned, initial.physical.extend frame⟩, same, related⟩

abbrev PoolState (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program))
    (index : ProtectedStateTransition.Index) :=
  State (CallableIndexedOwnedFunctionState.protocol headers keys) index

/-- Actual frame writes retain complete physical cache reads as well as the
reached ordinary pool records. -/
def install {index : ProtectedStateTransition.Index} (state : PoolState headers keys index)
    (selected : Fin keys.length) {next : NativeFrame} {nextGhost : GhostFrame}
    (history : Current compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table next nextGhost) :
    PoolState headers keys (index.extend index.mapping index.world index.heap
      (index.store.set keys[selected.val].frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame next))) := by
  have frameRead := (state.base.rows selected).authority.frame.read
  rw [(state.base.rows selected).frame_eq] at frameRead
  exact ⟨CallableIndexedOwnedFunctionState.install state.base selected history,
    state.physical.install frameRead next⟩

theorem install_records {index : ProtectedStateTransition.Index} (state : PoolState headers keys index)
    (selected : Fin keys.length) {next : NativeFrame} {nextGhost : GhostFrame}
    (history : Current compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table next nextGhost) :
    records (install state selected history).base = records state.base :=
  CallableIndexedOwnedFunctionState.install_records state.base selected history

/-- Restoring the saved frame uses the reached physical store and pool; every
new Source cell and every reached snapshot stays in place. -/
def restored {initial reached : ProtectedStateTransition.Index}
    (saved : PoolState headers keys initial) (after : PoolState headers keys reached) (selected : Fin keys.length) :
    PoolState headers keys (reached.extend reached.mapping reached.world reached.heap
      (reached.store.set keys[selected.val].frameLocation
        (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame
          (saved.base.rows selected).authority.current))) := by
  have frameRead := (after.base.rows selected).authority.frame.read
  rw [(after.base.rows selected).frame_eq] at frameRead
  exact ⟨CallableIndexedOwnedFunctionState.restored saved.base after.base selected,
    after.physical.install frameRead (saved.base.rows selected).authority.current⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalState
