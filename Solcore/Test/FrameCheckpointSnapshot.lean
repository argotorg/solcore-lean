import Solcore.Semantics.FrameCheckpointSnapshot

/-! Definition-only compile regressions for nominal checkpoint snapshots. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Semantics

universe u v

private example
    {RollbackState : Type u} {TraceState : Type v}
    (working : WorldState × FrameEffectJournal RollbackState TraceState) :
    FrameCheckpointSnapshot.fromWorkingPair working =
      (⟨working.1, working.2⟩ :
        FrameCheckpointSnapshot RollbackState TraceState) := by
  rfl

private def address : Address := ⟨0x12, by decide⟩
private def slot : Core.Word := ⟨0x34, by decide⟩
private def value : Core.Word := ⟨0x56, by decide⟩

private def concreteState : WorldState :=
  WorldState.empty.putAccount address
    (Account.empty.storageWrite slot value)

private def concreteEffects : FrameEffectJournal Nat (List Nat) :=
  ⟨37, [2, 3]⟩

private def concreteWorking :
    WorldState × FrameEffectJournal Nat (List Nat) :=
  (concreteState, concreteEffects)

private example :
    (FrameCheckpointSnapshot.fromWorkingPair concreteWorking).state =
      concreteState := by
  rfl

private example :
    (FrameCheckpointSnapshot.fromWorkingPair concreteWorking).effects =
      (⟨37, [2, 3]⟩ : FrameEffectJournal Nat (List Nat)) := by
  rfl

end Tests
