import Solcore.ContractRuntime.ParentIndexedFrameTrapPropagationPayload
import Solcore.ContractRuntime.ParentIndexedFrameContinuationConstruction

/-! Definition-only tests for parent-indexed trap propagation payloads. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive TrapPropagationEvent where
  | parent
  | nested

private inductive TrapPropagationReason where
  | marker
  | other

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def address : Address := ⟨0, by decide⟩
private def slot : Core.Word := ⟨0x11, by decide⟩
private def parentValue : Core.Word := ⟨0xaa, by decide⟩
private def nestedValue : Core.Word := ⟨0xbb, by decide⟩

private def stateWith (value : Core.Word) : WorldState :=
  WorldState.empty.putAccount address (Account.empty.storageWrite slot value)

private def observedValue? (state : WorldState) : Option Core.Word := do
  let account ← state.account? address
  account.storageValue? slot

private def parentTrace : FrameTrace TrapPropagationEvent :=
  FrameTrace.record FrameTrace.empty .parent

private def parentWorking :
    WorldState × FrameEffectJournal Nat (FrameTrace TrapPropagationEvent) :=
  (stateWith parentValue, ⟨10, parentTrace⟩)

private def extension : FrameTrace.ExtensionFrom parentWorking.2.trace :=
  (FrameTrace.ExtensionFrom.start parentWorking.2.trace).record .nested

private def contextWith (outcome : FrameOutcome TrapPropagationReason) :
    ParentIndexedFrameContinuationContext Nat TrapPropagationEvent
      TrapPropagationReason parentWorking :=
  ParentIndexedFrameContinuationContext.fromTraceExtension
    parentWorking 20 extension ⟨stateWith nestedValue, outcome⟩

private def isNone {α : Type} : Option α → Bool
  | none => true
  | some _ => false

private def isMarkerTrap : FrameOutcome TrapPropagationReason → Bool
  | .trapped .marker => true
  | _ => false

private def isExtendedTrace : List TrapPropagationEvent → Bool
  | [.parent, .nested] => true
  | _ => false

private def matchesTrapPropagationPayload :
    Option
      (FrameRunResult TrapPropagationReason ×
        FrameEffectJournal Nat (FrameTrace TrapPropagationEvent)) → Bool
  | some (result, effects) =>
      observedValue? result.working == some parentValue &&
        isMarkerTrap result.outcome && effects.rollback == 10 &&
        isExtendedTrace effects.trace.toList
  | none => false

def testParentIndexedFrameTrapPropagationPayload : IO Unit := do
  assertTrue
    (isNone
      (contextWith (.returned [0x12].toByteArray)).trapPropagationPayload?)
    "return must not select a trap propagation payload"

  assertTrue
    (isNone
      (contextWith (.reverted [0x34].toByteArray)).trapPropagationPayload?)
    "revert must not select a trap propagation payload"

  assertTrue
    (matchesTrapPropagationPayload
      (contextWith (.trapped .marker)).trapPropagationPayload?)
    "trap must select parent state and rollback with its reason and exact trace"

end Tests
