import Solcore.Frontend.SourceTypedRuntime

/-!
Small executable contracts for the phase-7 typed-source runtime.

The phase intentionally prioritizes a complete running language slice over a
large metatheory.  These lemmas nevertheless pin down the public fuel boundary,
the successful-result projection, and representative deep-value validation
rules used at the safe input boundary.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceTypedRuntime

open TypeSystem

theorem unit_hasType (signatures : ProgramSignatures) (plan : Plan)
    (fuel : Nat) :
    Value.hasType signatures plan (fuel + 1) .unit .unit = true := by
  simpa only [Value.hasType, Nat.add_one, Ty.unit] using
    Value.hasTypeFuel.eq_2 signatures plan fuel

theorem bool_hasType (signatures : ProgramSignatures) (plan : Plan)
    (fuel : Nat) (value : Bool) :
    Value.hasType signatures plan (fuel + 1) .bool (.bool value) = true := by
  simpa only [Value.hasType, Nat.add_one, Ty.bool] using
    Value.hasTypeFuel.eq_3 signatures plan fuel value

theorem word_hasType (signatures : ProgramSignatures) (plan : Plan)
    (fuel : Nat) (value : Core.Word) :
    Value.hasType signatures plan (fuel + 1) .word (.word value) = true := by
  simpa only [Value.hasType, Nat.add_one, Ty.word] using
    Value.hasTypeFuel.eq_4 signatures plan fuel value

theorem proxy_hasType (signatures : ProgramSignatures) (plan : Plan)
    (fuel : Nat) (inner : Ty) :
    Value.hasType signatures plan (fuel + 1) (.proxy inner) (.proxy inner) =
      true := by
  unfold Value.hasType
  rw [Nat.add_one, Value.hasTypeFuel.eq_7]
  simp

theorem zero_fuel_runTrusted (plan : Plan) (entry : Key)
    (arguments : List Value) (state : RuntimeState) :
    runTrusted plan entry arguments 0 state = .outOfFuel state := by
  rfl

theorem run?_some_iff (signatures : ProgramSignatures) (plan : Plan)
    (entry : Key) (arguments : List Value) (fuel : Nat)
    (initial finalState : RuntimeState) (value : Value) :
    run? signatures plan entry arguments fuel initial =
        some (value, finalState) ↔
      run signatures plan entry arguments fuel initial =
        .done value finalState := by
  unfold run?
  split <;> simp_all

end Solcore.Frontend.SourceTypedRuntime
