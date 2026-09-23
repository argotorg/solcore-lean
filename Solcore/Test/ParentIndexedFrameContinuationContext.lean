import Solcore.ContractRuntime.ParentIndexedFrameContinuationContext
import Solcore.ContractRuntime.FrameTrace

/-! Definition-only tests for parent-indexed frame continuation contexts. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive ParentIndexedEvent where
  | parent
  | nested

private inductive ParentIndexedReason where
  | marker

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

private def parentTrace : FrameTrace ParentIndexedEvent :=
  FrameTrace.record FrameTrace.empty .parent

private def parentWorking :
    WorldState × FrameEffectJournal Nat (FrameTrace ParentIndexedEvent) :=
  (stateWith parentValue, ⟨10, parentTrace⟩)

private def extension : FrameTrace.ExtensionFrom parentWorking.2.trace :=
  (FrameTrace.ExtensionFrom.start parentWorking.2.trace).record .nested

private def contextWith (outcome : FrameOutcome ParentIndexedReason) :
    ParentIndexedFrameContinuationContext Nat ParentIndexedEvent
      ParentIndexedReason parentWorking :=
  let base :
      FrameContinuationContext Nat (FrameTrace ParentIndexedEvent)
        ParentIndexedReason :=
    ⟨parentWorking.1, parentWorking.2, ⟨20, extension.toTrace⟩,
      ⟨stateWith nestedValue, outcome⟩⟩
  let prefixed :
      FrameContinuationContextWithTracePrefix Nat ParentIndexedEvent
        ParentIndexedReason :=
    ⟨base, extension.earlier_isPrefixOf_toTrace⟩
  ⟨prefixed, rfl⟩

private def matchesTrace : List ParentIndexedEvent → Bool
  | [.parent, .nested] => true
  | _ => false

private def matchesReturn? :
    FrameResolutionResult Nat (FrameTrace ParentIndexedEvent)
      ParentIndexedReason → Bool
  | .returned state effects data =>
      observedValue? state == some nestedValue &&
        effects.rollback == 20 && matchesTrace effects.trace.toList &&
        data == [0x12].toByteArray
  | _ => false

private def matchesRevert? :
    FrameResolutionResult Nat (FrameTrace ParentIndexedEvent)
      ParentIndexedReason → Bool
  | .reverted state effects data =>
      observedValue? state == some parentValue &&
        effects.rollback == 10 && matchesTrace effects.trace.toList &&
        data == [0x34].toByteArray
  | _ => false

private def matchesTrap? :
    FrameResolutionResult Nat (FrameTrace ParentIndexedEvent)
      ParentIndexedReason → Bool
  | .trapped .marker => true
  | _ => false

def testParentIndexedFrameContinuationContext : IO Unit := do
  assertTrue
    (matchesReturn? (contextWith (.returned [0x12].toByteArray)).resolve)
    "return must select nested working state, effects, trace, and payload"

  assertTrue
    (matchesRevert? (contextWith (.reverted [0x34].toByteArray)).resolve)
    "revert must restore the indexed parent pair and keep the accumulated trace"

  assertTrue
    (matchesTrap? (contextWith (.trapped .marker)).resolve)
    "trap must preserve only the concrete reason"

end Tests
