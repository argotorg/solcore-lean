import Solcore.Frontend.RustHull.RuntimeChildCallStateCorrespondence
import Solcore.Frontend.RustHull.RuntimeCallModeSemantics
import Solcore.Frontend.RustHull.AccountCallModeHandlersCorrespondence

/-! Mode-specific handlers are concrete immutable captures. The existing linked
caller model carries their reads alongside the captured initialization context. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallModeEffectsCorrespondence
open Core Correspondence
open RuntimeCallEffectsCorrespondence (Layout Handlers mutable localLocations)
open RuntimeChildCallEffectsCorrespondence (Anchors Context)
open RuntimeCallModeSemantics (Operation)

structure ExtraHandler (layout : Layout) (source : Word) (mode : AccountCallSemantics.Mode) where
  location : Nat
  below : location < layout.boundary
  outside : location ∉ mutable layout
  value : Value
  closure : AccountCallModeCorrespondence.CallHandlerClosure mode source layout.dispatcher value

structure ModeHandlers (layout : Layout) where
  ordinary : Handlers layout
  callCode : ExtraHandler layout ordinary.source .callCode
  delegateCall : ExtraHandler layout ordinary.source .delegateCall

def ModeHandlers.context {layout : Layout} (handlers : ModeHandlers layout) (captured : Context layout) : Context layout where
  valid read := captured.valid read ∧
    read handlers.callCode.location = some (.inRight .unit handlers.callCode.value) ∧
    read handlers.delegateCall.location = some (.inRight .unit handlers.delegateCall.value)
  frame := by
    intro before after kept valid
    exact ⟨captured.frame kept valid.1,
      (kept _ handlers.callCode.outside).trans valid.2.1,
      (kept _ handlers.delegateCall.outside).trans valid.2.2⟩

def model (layout : Layout) (baseline : Nat → Option Value) (slots : List EffectSlot)
    (image : Option (List UInt8)) (handlers : ModeHandlers layout) (anchors : Anchors) (context : Context layout) :
    StateModel RuntimeCallModeSemantics.State :=
  RuntimeChildCallEffectsCorrespondence.model layout baseline slots image handlers.ordinary anchors (handlers.context context)

def ModeHandlers.location {layout : Layout} (handlers : ModeHandlers layout) : Operation → Nat
  | .ordinary | .staticCall => layout.callHandler
  | .callCode => handlers.callCode.location
  | .delegateCall => handlers.delegateCall.location

def ModeHandlers.value {layout : Layout} (handlers : ModeHandlers layout) : Operation → Value
  | .ordinary | .staticCall => handlers.ordinary.handlerValue
  | .callCode => handlers.callCode.value
  | .delegateCall => handlers.delegateCall.value

def ModeHandlers.closure {layout : Layout} (handlers : ModeHandlers layout) (operation : Operation) :
    AccountCallModeCorrespondence.CallHandlerClosure operation.mode handlers.ordinary.source layout.dispatcher (handlers.value operation) := by
  cases operation with
  | ordinary | staticCall => exact .of_ordinary handlers.ordinary.handler
  | callCode => exact handlers.callCode.closure
  | delegateCall => exact handlers.delegateCall.closure

def transportModel (layout : Layout) (handlers : ModeHandlers layout) (anchors : Anchors) (context : Context layout) :=
  RuntimeChildCallEffectsCorrespondence.transportModel layout handlers.ordinary anchors (handlers.context context)

def CallbackPreservation (layout : Layout) (handlers : ModeHandlers layout) (anchors : Anchors) (context : Context layout)
    (children : RuntimeCallModeSemantics.State → AccountCallSemantics.Children)
    (operation : Operation) (parent : RuntimeCallModeSemantics.State) : Prop :=
  CallTransportCorrespondence.CallbackPreservation (transportModel layout handlers anchors context)
    (AccountCallSemantics.Dispatch (children parent) operation.mode parent.runtime.runtime.runtime.runtime.runtime.storage.address)
    (handlers.value operation)

theorem base_related {layout : Layout} {baseline : Nat → Option Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : ModeHandlers layout} {anchors : Anchors} {context : Context layout} {world : World}
    {state : Semantics.State RuntimeCallModeSemantics.State} {store : Store}
    (related : StateRel (model layout baseline slots image handlers anchors context) world state store) :
    StateRel (RuntimeCallEffectsCorrespondence.model layout baseline slots image handlers.ordinary) world state store :=
  RuntimeChildCallEffectsCorrespondence.base_related related

theorem handler_read {layout : Layout} {baseline : Nat → Option Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : ModeHandlers layout} {anchors : Anchors} {context : Context layout} {world : World}
    {state : Semantics.State RuntimeCallModeSemantics.State} {store : Store}
    (related : StateRel (model layout baseline slots image handlers anchors context) world state store)
    (operation : Operation) : store.read? (handlers.location operation) = some (.inRight .unit (handlers.value operation)) := by
  cases operation with
  | ordinary | staticCall =>
      exact (RuntimeCallEffectsCorrespondence.shared_resources (base_related related)).2.1
  | callCode =>
      simpa only [ModeHandlers.location, ModeHandlers.value, prefixRead, handlers.callCode.below, ↓reduceIte]
        using related.external.2.2.1.2.2.1
  | delegateCall =>
      simpa only [ModeHandlers.location, ModeHandlers.value, prefixRead, handlers.delegateCall.below, ↓reduceIte]
        using related.external.2.2.1.2.2.2

theorem ModeHandlers.local_outside {layout : Layout} (handlers : ModeHandlers layout) (operation : Operation) :
    handlers.location operation ∉ (localLocations layout).all := by
  cases operation with
  | ordinary | staticCall => exact RuntimeCallEffectsCorrespondence.shared_local_separation layout _ (by simp [ModeHandlers.location])
  | callCode =>
      intro member
      apply handlers.callCode.outside
      simp only [ModeHandlers.location, localLocations, CallTransportCorrespondence.Locations.all,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same <;> rw [same] <;>
        simp [mutable, RuntimeLogEffectsCorrespondence.mutable, RuntimeEffectsCorrespondence.mutable,
          StorageBuiltinCorrespondence.Locations.mutable]
  | delegateCall =>
      intro member
      apply handlers.delegateCall.outside
      simp only [ModeHandlers.location, localLocations, CallTransportCorrespondence.Locations.all,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same <;> rw [same] <;>
        simp [mutable, RuntimeLogEffectsCorrespondence.mutable, RuntimeEffectsCorrespondence.mutable,
          StorageBuiltinCorrespondence.Locations.mutable]

end Solcore.Frontend.RustHull.RuntimeCallModeEffectsCorrespondence
