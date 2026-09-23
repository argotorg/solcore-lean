import Solcore.ContractRuntime.FrameTrace

/-! Executable tests for finite chronological frame traces. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

private inductive TraceEvent where
  | entered
  | child
  | finished

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def matchesEmpty : List TraceEvent → Bool
  | [] => true
  | _ => false

private def matchesEntered : List TraceEvent → Bool
  | [.entered] => true
  | _ => false

private def matchesRepeated : List TraceEvent → Bool
  | [.entered, .child, .child] => true
  | _ => false

private def matchesAppended : List TraceEvent → Bool
  | [.entered, .child, .finished] => true
  | _ => false

private def matchesCombined : List TraceEvent → Bool
  | [.entered, .child, .child, .finished] => true
  | _ => false

private def empty : FrameTrace TraceEvent :=
  FrameTrace.empty

private def entered : FrameTrace TraceEvent :=
  empty.record .entered

private def repeated : FrameTrace TraceEvent :=
  (entered.record .child).record .child

private def later : FrameTrace TraceEvent :=
  (FrameTrace.empty.record .child).record .finished

def testFrameTrace : IO Unit := do
  assertTrue
    (matchesEmpty empty.toList)
    "an empty frame trace must expose no events"

  assertTrue
    (matchesEntered entered.toList)
    "record must place one event at the chronological tail"

  assertTrue
    (matchesRepeated repeated.toList)
    "record must preserve order and duplicate events"

  let journal : FrameEffectJournal Nat (FrameTrace TraceEvent) :=
    ⟨7, entered.append later⟩
  assertTrue
    (journal.rollback == 7 && matchesAppended journal.trace.toList)
    "append must place the earlier journal trace before the later fragment"

  let emptyLeft := FrameTrace.append FrameTrace.empty repeated
  let emptyRight := FrameTrace.append repeated FrameTrace.empty
  assertTrue
    (matchesRepeated emptyLeft.toList && matchesRepeated emptyRight.toList)
    "empty must be a left and right append identity"

  let first := empty.record .entered
  let second := (FrameTrace.empty.record .child).record .child
  let third := FrameTrace.empty.record .finished
  let leftAssociated := (first.append second).append third
  let rightAssociated := first.append (second.append third)
  assertTrue
    (matchesCombined leftAssociated.toList &&
      matchesCombined rightAssociated.toList)
    "three trace fragments must preserve order under either association"

end Tests
