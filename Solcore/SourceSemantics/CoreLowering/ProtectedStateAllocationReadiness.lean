import Solcore.SourceSemantics.CoreLowering.ProtectedStateOrdinaryAllocation

/-! The lexical tree uses one fixed physical frame and stable native token.
Every allocation consumes its actual reached-state witness and a real live
read. Readiness is supplied by a logical acquisition family, independently of
source/native expression or body execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.OrdinaryAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory
universe u v

variable {Records : Type v} {protocol : Protocol.{u, v} Records}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
  {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
  {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}

def ReadyAt (producer : Producer protocol layouts frame model)
    (location : Location) (native : NativeFrame) : Prop :=
  ∀ {index : Index} (reached : protocol.State index),
    index.store.read? location = some (SourceCoreCallableIndexedFrames.encode frame native) →
    producer.Ready reached location native

/-- The certified administrative effect supplies the reached read, including
after expression children and completed source allocations. -/
theorem ReadyAt.after_administrative {producer : Producer protocol layouts frame model}
    {location : Location} {native : NativeFrame}
    (ready : ReadyAt producer location native)
    {initial reached : Index} (state : protocol.State reached)
    (read : initial.store.read? location = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : location ∉ initial.mapping)
    (preserved : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    producer.Ready state location native := by
  exact ready state ((preserved location unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)

theorem administrative_readyAt (protocol : Protocol.{u, v} Records)
    (transport : AdministrativeTransport protocol) (bindings : Bindings protocol)
    (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout)
    (model : GenericHeap.PayloadModel catalog projects nativeDefinitions)
    (location : Location) (native : NativeFrame) :
    ReadyAt (of_administrative protocol transport bindings layouts frame model) location native :=
  fun _state _read => True.intro

theorem unit_readyAt (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout)
    (model : GenericHeap.PayloadModel catalog projects nativeDefinitions)
    (location : Location) (native : NativeFrame) :
    ReadyAt (unitProducer layouts frame model) location native :=
  fun _state _read => True.intro

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.OrdinaryAllocation
