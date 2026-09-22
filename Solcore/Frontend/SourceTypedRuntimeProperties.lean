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

@[simp] theorem Cell.hasShallowType_none (plan : Plan) (type : Ty) :
    ({ type, value := none } : Cell).HasShallowType plan := by
  intro value impossible
  cases impossible

theorem Cell.hasShallowType_some
    (plan : Plan) (type : Ty) (value : Value)
    (typed : value.type? plan = some type) :
    ({ type, value := some value } : Cell).HasShallowType plan := by
  intro selected equal
  cases equal
  exact typed

@[simp] theorem RuntimeState.hasShallowTypes_empty (plan : Plan) :
    ({} : RuntimeState).HasShallowTypes plan := by
  intro cell member
  simp at member

theorem RuntimeState.HasShallowTypes.read
    {plan : Plan} {state : RuntimeState} (typing : state.HasShallowTypes plan)
    {location : Location} {cell : Cell}
    (found : state.read? location = some cell) :
    cell.HasShallowType plan := by
  apply typing cell
  exact List.mem_of_getElem? (by
    simpa [RuntimeState.read?] using found)

/-- Reading an initialized cell from a shallow-typed heap yields a value with
the cell's declared type. -/
theorem RuntimeState.HasShallowTypes.read_value
    {plan : Plan} {state : RuntimeState} (typing : state.HasShallowTypes plan)
    {location : Location} {cell : Cell} {value : Value}
    (found : state.read? location = some cell)
    (initialized : cell.value = some value) :
    value.type? plan = some cell.type :=
  (typing.read found) value initialized

theorem RuntimeState.HasShallowTypes.allocate
    {plan : Plan} {state : RuntimeState} (typing : state.HasShallowTypes plan)
    (type : Ty) (value : Option Value)
    (fresh : ({ type, value } : Cell).HasShallowType plan) :
    (state.allocate type value).2.HasShallowTypes plan := by
  intro selected member
  simp only [RuntimeState.allocate] at member
  rw [List.mem_append] at member
  rcases member with old | appended
  · exact typing selected old
  · simp only [List.mem_singleton] at appended
    subst selected
    exact fresh

theorem RuntimeState.HasShallowTypes.allocate_none
    {plan : Plan} {state : RuntimeState} (typing : state.HasShallowTypes plan)
    (type : Ty) :
    (state.allocate type none).2.HasShallowTypes plan :=
  typing.allocate type none (Cell.hasShallowType_none plan type)

theorem RuntimeState.HasShallowTypes.allocate_some
    {plan : Plan} {state : RuntimeState} (typing : state.HasShallowTypes plan)
    (type : Ty) (value : Value)
    (typed : value.type? plan = some type) :
    (state.allocate type (some value)).2.HasShallowTypes plan :=
  typing.allocate type (some value)
    (Cell.hasShallowType_some plan type value typed)

theorem RuntimeState.HasShallowTypes.write?_none
    {plan : Plan} {state updated : RuntimeState} (typing : state.HasShallowTypes plan)
    {location : Location} {previous : Cell}
    (found : state.read? location = some previous)
    (written : state.write? location none = some updated) :
    updated.HasShallowTypes plan := by
  apply typing.write? found _ written
  intro value impossible
  cases impossible

theorem RuntimeState.HasShallowTypes.write?_some
    {plan : Plan} {state updated : RuntimeState} (typing : state.HasShallowTypes plan)
    {location : Location} {previous : Cell} {value : Value}
    (found : state.read? location = some previous)
    (typed : value.type? plan = some previous.type)
    (written : state.write? location (some value) = some updated) :
    updated.HasShallowTypes plan := by
  apply typing.write? found _ written
  intro selected equal
  cases equal
  exact typed

theorem unit_hasType (signatures : ProgramSignatures) (plan : Plan)
    (fuel : Nat) :
    Value.hasType signatures plan (fuel + 1) .unit .unit = true := by
  unfold Value.hasType Value.hasTypeFuel
  simp only [Ty.unit, Nat.add_one]
  rw [Value.validateTypeFuel.eq_2]
  rfl

theorem bool_hasType (signatures : ProgramSignatures) (plan : Plan)
    (fuel : Nat) (value : Bool) :
    Value.hasType signatures plan (fuel + 1) .bool (.bool value) = true := by
  unfold Value.hasType Value.hasTypeFuel
  simp only [Ty.bool, Nat.add_one]
  rw [Value.validateTypeFuel.eq_3]
  rfl

theorem word_hasType (signatures : ProgramSignatures) (plan : Plan)
    (fuel : Nat) (value : Core.Word) :
    Value.hasType signatures plan (fuel + 1) .word (.word value) = true := by
  unfold Value.hasType Value.hasTypeFuel
  simp only [Ty.word, Nat.add_one]
  rw [Value.validateTypeFuel.eq_4]
  rfl

theorem proxy_hasType (signatures : ProgramSignatures) (plan : Plan)
    (fuel : Nat) (inner : Ty) :
    Value.hasType signatures plan (fuel + 1) (.proxy inner) (.proxy inner) =
      true := by
  unfold Value.hasType Value.hasTypeFuel
  rw [Nat.add_one, Value.validateTypeFuel.eq_7]
  split
  · change true = true
    rfl
  · contradiction

theorem zero_fuel_validateType (signatures : ProgramSignatures) (plan : Plan)
    (expected : Ty) (value : Value) :
    value.validateTypeFuel 0 signatures plan expected = .outOfFuel := by
  rw [Value.validateTypeFuel.eq_1]

theorem zero_fuel_runTrusted (plan : Plan) (entry : Key)
    (arguments : List Value) (state : RuntimeState) :
    runTrusted plan entry arguments 0 state = .outOfFuel state := by
  rfl

theorem run_eq_runWithValidationFuel (signatures : ProgramSignatures)
    (plan : Plan) (entry : Key) (arguments : List Value) (fuel : Nat)
    (state : RuntimeState) :
    run signatures plan entry arguments fuel state =
      runWithValidationFuel signatures plan entry arguments fuel fuel state := by
  rfl

theorem run_done_has_inferredBodyType
    (signatures : ProgramSignatures) (plan : Plan) (entry : Key)
    (arguments : List Value) (fuel : Nat)
    (initial finalState : RuntimeState) (value : Value)
    (specialized : SourceSpecialization.SpecializedFunction)
    (exact : plan.specializations.filter (fun candidate =>
      decide (candidate.key = entry)) = [specialized])
    (done : run signatures plan entry arguments fuel initial =
      .done value finalState) :
    value.type? plan = some specialized.function.inferredBodyType := by
  exact runWithValidationFuel_done_has_inferredBodyType signatures plan entry
    arguments fuel fuel initial finalState value specialized exact done

theorem run?_some_iff (signatures : ProgramSignatures) (plan : Plan)
    (entry : Key) (arguments : List Value) (fuel : Nat)
    (initial finalState : RuntimeState) (value : Value) :
    run? signatures plan entry arguments fuel initial =
        some (value, finalState) ↔
      run signatures plan entry arguments fuel initial =
        .done value finalState := by
  unfold run?
  split <;> simp_all

theorem run?_some_has_inferredBodyType
    (signatures : ProgramSignatures) (plan : Plan) (entry : Key)
    (arguments : List Value) (fuel : Nat)
    (initial finalState : RuntimeState) (value : Value)
    (specialized : SourceSpecialization.SpecializedFunction)
    (exact : plan.specializations.filter (fun candidate =>
      decide (candidate.key = entry)) = [specialized])
    (success : run? signatures plan entry arguments fuel initial =
      some (value, finalState)) :
    value.type? plan = some specialized.function.inferredBodyType := by
  apply run_done_has_inferredBodyType signatures plan entry arguments fuel
    initial finalState value specialized exact
  exact (run?_some_iff signatures plan entry arguments fuel initial finalState
    value).mp success

end Solcore.Frontend.SourceTypedRuntime
