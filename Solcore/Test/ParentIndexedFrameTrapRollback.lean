import Solcore.ContractRuntime.ParentIndexedFrameTrapRollback
import Solcore.ContractRuntime.ParentIndexedFrameContinuationConstruction

/-! Definition-only tests for parent-indexed trapped-frame rollback selection. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive TrapRollbackEvent where
  | parent
  | nested

private inductive TrapRollbackReason where
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

private def parentTrace : FrameTrace TrapRollbackEvent :=
  FrameTrace.record FrameTrace.empty .parent

private def parentWorking :
    WorldState × FrameEffectJournal Nat (FrameTrace TrapRollbackEvent) :=
  (stateWith parentValue, ⟨10, parentTrace⟩)

private def extension : FrameTrace.ExtensionFrom parentWorking.2.trace :=
  (FrameTrace.ExtensionFrom.start parentWorking.2.trace).record .nested

private def contextWith (outcome : FrameOutcome TrapRollbackReason) :
    ParentIndexedFrameContinuationContext Nat TrapRollbackEvent
      TrapRollbackReason parentWorking :=
  ParentIndexedFrameContinuationContext.fromTraceExtension
    parentWorking 20 extension ⟨stateWith nestedValue, outcome⟩

private def isNone {α : Type} : Option α → Bool
  | none => true
  | some _ => false

private def isExtendedTrace : List TrapRollbackEvent → Bool
  | [.parent, .nested] => true
  | _ => false

private def matchesTrapRollback :
    Option
      (WorldState ×
        FrameEffectJournal Nat (FrameTrace TrapRollbackEvent)) → Bool
  | some (state, effects) =>
      observedValue? state == some parentValue &&
        effects.rollback == 10 && isExtendedTrace effects.trace.toList
  | none => false

def testParentIndexedFrameTrapRollback : IO Unit := do
  assertTrue
    (isNone
      (contextWith (.returned [0x12].toByteArray)).trapRollback?)
    "return must not select a trapped-frame rollback pair"

  assertTrue
    (isNone
      (contextWith (.reverted [0x34].toByteArray)).trapRollback?)
    "revert must not select a trapped-frame rollback pair"

  assertTrue
    (matchesTrapRollback (contextWith (.trapped .marker)).trapRollback?)
    "trap must select parent state and rollback with the working trace"

end Tests
