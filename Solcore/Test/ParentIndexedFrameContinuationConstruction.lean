import Solcore.Semantics.ParentIndexedFrameContinuationConstruction

/-! Definition-only tests for trace-extension parent-context construction. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Semantics

private inductive ConstructionEvent where
  | parent
  | nested

private inductive ConstructionReason where
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

private def parentTrace : FrameTrace ConstructionEvent :=
  FrameTrace.record FrameTrace.empty .parent

private def parentWorking :
    WorldState × FrameEffectJournal Nat (FrameTrace ConstructionEvent) :=
  (stateWith parentValue, ⟨10, parentTrace⟩)

private def extension : FrameTrace.ExtensionFrom parentWorking.2.trace :=
  (FrameTrace.ExtensionFrom.start parentWorking.2.trace).record .nested

private def result : FrameRunResult ConstructionReason :=
  ⟨stateWith nestedValue, .returned [0x12].toByteArray⟩

private def context :
    ParentIndexedFrameContinuationContext Nat ConstructionEvent
      ConstructionReason parentWorking :=
  ParentIndexedFrameContinuationContext.fromTraceExtension
    parentWorking 20 extension result

private def isParentTrace : List ConstructionEvent → Bool
  | [.parent] => true
  | _ => false

private def isExtendedTrace : List ConstructionEvent → Bool
  | [.parent, .nested] => true
  | _ => false

private def matchesCheckpoints : Bool :=
  observedValue? context.stateCheckpoint == some parentValue &&
    context.effectCheckpoint.rollback == 10 &&
    isParentTrace context.effectCheckpoint.trace.toList

private def matchesWorkingEffects : Bool :=
  context.effectWorking.rollback == 20 &&
    isExtendedTrace context.effectWorking.trace.toList

private def matchesResult : Bool :=
  observedValue? context.result.working == some nestedValue &&
    match context.result.outcome with
    | .returned data => data == [0x12].toByteArray
    | _ => false

def testParentIndexedFrameContinuationConstruction : IO Unit := do
  assertTrue matchesCheckpoints
    "construction must copy the observed parent checkpoints"

  assertTrue matchesWorkingEffects
    "construction must combine working rollback with one exact trace extension"

  assertTrue matchesResult
    "construction must preserve the supplied frame result"

end Tests
