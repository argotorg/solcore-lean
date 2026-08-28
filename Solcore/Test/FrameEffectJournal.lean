import Solcore.Semantics.FrameEffectJournal

/-! Executable tests for rollback-scoped and surviving effect snapshots. -/

set_option autoImplicit false

namespace Tests

open Solcore.Semantics

private inductive JournalTrapReason where
  | invalidOperation

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def parentCheckpoint : FrameEffectJournal Nat Nat :=
  ⟨10, 100⟩

private def childCheckpoint : FrameEffectJournal Nat Nat :=
  ⟨20, 200⟩

private def childWorking : FrameEffectJournal Nat Nat :=
  ⟨30, 300⟩

private def matches?
    (journal? : Option (FrameEffectJournal Nat Nat))
    (rollback trace : Nat) : Bool :=
  match journal? with
  | some journal => journal.rollback == rollback && journal.trace == trace
  | none => false

def testFrameEffectJournal : IO Unit := do
  let returnData := [0x12, 0].toByteArray
  let revertData := [].toByteArray
  let returned : FrameOutcome JournalTrapReason := .returned returnData
  let reverted : FrameOutcome JournalTrapReason := .reverted revertData
  let trapped : FrameOutcome JournalTrapReason := .trapped .invalidOperation
  assertTrue
    (matches? (FrameEffectJournal.resolved?
      parentCheckpoint childWorking returned) 30 300)
    "a returned frame must keep both working rollback and trace snapshots"
  assertTrue
    (matches? (FrameEffectJournal.resolved?
      parentCheckpoint childWorking reverted) 10 300)
    "a reverted frame must restore checkpoint rollback while keeping working trace"
  assertTrue
    (FrameEffectJournal.resolved? parentCheckpoint childWorking trapped).isNone
    "a trapped frame must leave effect-journal disposition unresolved"
  let childReturned :=
    FrameEffectJournal.resolved? childCheckpoint childWorking returned
  let childReturnThenParentRevert := childReturned.bind fun childResolved =>
    FrameEffectJournal.resolved? parentCheckpoint childResolved reverted
  assertTrue (matches? childReturnThenParentRevert 10 300)
    "a parent revert must roll back a returned child while preserving its trace"
  let childReverted :=
    FrameEffectJournal.resolved? childCheckpoint childWorking reverted
  let childRevertThenParentRevert := childReverted.bind fun childResolved =>
    FrameEffectJournal.resolved? parentCheckpoint childResolved reverted
  assertTrue (matches? childRevertThenParentRevert 10 300)
    "child and parent reverts must restore parent rollback and preserve child trace"

end Tests
