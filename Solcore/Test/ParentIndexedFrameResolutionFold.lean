import Solcore.Semantics.ParentIndexedFrameResolutionFold

/-! Definition-only tests for the parent-indexed resolution fold. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Semantics

private inductive ResolutionFoldEvent where
  | parent
  | nested

private inductive ResolutionFoldReason where
  | marker
  | other

private inductive ResolutionFoldMarker where
  | returned
  | reverted
  | trapped
  | mismatch
  deriving BEq

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def address : Address := ⟨0, by decide⟩
private def slot : Core.Word := ⟨0x11, by decide⟩
private def parentValue : Core.Word := ⟨0xaa, by decide⟩
private def workingValue : Core.Word := ⟨0xbb, by decide⟩

private def stateWith (value : Core.Word) : WorldState :=
  WorldState.empty.putAccount address (Account.empty.storageWrite slot value)

private def observedValue? (state : WorldState) : Option Core.Word := do
  let account ← state.account? address
  account.storageValue? slot

private def parentTrace : FrameTrace ResolutionFoldEvent :=
  FrameTrace.record FrameTrace.empty .parent

private def nestedFragment : FrameTrace ResolutionFoldEvent :=
  FrameTrace.record FrameTrace.empty .nested

private def nestedTrace : FrameTrace ResolutionFoldEvent :=
  FrameTrace.append parentTrace nestedFragment

private def parentJournal :
    FrameEffectJournal Nat (FrameTrace ResolutionFoldEvent) :=
  ⟨10, parentTrace⟩

private def workingJournal :
    FrameEffectJournal Nat (FrameTrace ResolutionFoldEvent) :=
  ⟨20, nestedTrace⟩

private def parentWorking :
    WorldState × FrameEffectJournal Nat (FrameTrace ResolutionFoldEvent) :=
  (stateWith parentValue, parentJournal)

private theorem tracePrefix :
    FrameTrace.IsPrefixOf parentTrace nestedTrace :=
  ⟨nestedFragment, rfl⟩

private def contextWith (outcome : FrameOutcome ResolutionFoldReason) :
    ParentIndexedFrameContinuationContext Nat ResolutionFoldEvent
      ResolutionFoldReason parentWorking :=
  ⟨⟨⟨parentWorking.1, parentWorking.2, workingJournal,
        ⟨stateWith workingValue, outcome⟩⟩,
      tracePrefix⟩,
    rfl⟩

private def isNestedTrace : List ResolutionFoldEvent → Bool
  | [.parent, .nested] => true
  | _ => false

private def matchesValues
    (expectedValue : Core.Word) (expectedRollback : Nat)
    (values :
      WorldState ×
        FrameEffectJournal Nat (FrameTrace ResolutionFoldEvent)) : Bool :=
  observedValue? values.1 == some expectedValue &&
    values.2.rollback == expectedRollback &&
    isNestedTrace values.2.trace.toList

private def onReturned
    (values :
      WorldState ×
        FrameEffectJournal Nat (FrameTrace ResolutionFoldEvent))
    (data : Bytes) : ResolutionFoldMarker :=
  if matchesValues workingValue 20 values && data == [0x12].toByteArray then
    .returned
  else
    .mismatch

private def onReverted
    (values :
      WorldState ×
        FrameEffectJournal Nat (FrameTrace ResolutionFoldEvent))
    (data : Bytes) : ResolutionFoldMarker :=
  if matchesValues parentValue 10 values && data == [0x34].toByteArray then
    .reverted
  else
    .mismatch

private def onTrapped
    (values :
      WorldState ×
        FrameEffectJournal Nat (FrameTrace ResolutionFoldEvent))
    (reason : ResolutionFoldReason) : ResolutionFoldMarker :=
  if matchesValues parentValue 10 values then
    match reason with
    | .marker => .trapped
    | .other => .mismatch
  else
    .mismatch

def testParentIndexedFrameResolutionFold : IO Unit := do
  assertTrue
    ((contextWith (.returned [0x12].toByteArray)).foldResolutionWithTrapRollback
        onReturned onReverted onTrapped == .returned)
    "return must select the terminal working pair and exact bytes"

  assertTrue
    ((contextWith (.reverted [0x34].toByteArray)).foldResolutionWithTrapRollback
        onReturned onReverted onTrapped == .reverted)
    "revert must select the parent rollback pair, working trace, and bytes"

  assertTrue
    ((contextWith (.trapped .marker)).foldResolutionWithTrapRollback
        onReturned onReverted onTrapped == .trapped)
    "trap must select the parent rollback pair and exact reason"

end Tests
