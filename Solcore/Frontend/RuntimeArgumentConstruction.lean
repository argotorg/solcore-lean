import Solcore.Frontend.RuntimeParameters

/-! Construct structural evidence for the literal actual value, without checking
allocation or adding signature/unselected-type well-formedness requirements. -/
set_option autoImplicit false
namespace Solcore.Frontend

mutual
  private def buildValue? (value : Core.Value) : Option (PLift (Core.ValueHasType value value.type)) :=
    match value with
    | .unit => some ⟨.unit⟩
    | .bool _ => some ⟨.bool⟩
    | .word _ => some ⟨.word⟩
    | .integer _ => some ⟨.integer⟩
    | .hostFunction _ | .constructed _ _ => none
    | .pair left right => do
        let leftTyped ← buildValue? left
        let rightTyped ← buildValue? right
        return ⟨.pair leftTyped.down rightTyped.down⟩
    | .inLeft _ payload => do
        let typed ← buildValue? payload
        return ⟨.inLeft typed.down⟩
    | .inRight _ payload => do
        let typed ← buildValue? payload
        return ⟨.inRight typed.down⟩
    | .closure parameterType resultType body captured => do
        let typed ← buildEnvironment? captured
        if inferred : Core.infer? (parameterType :: captured.map Core.Value.type) body = some resultType then
          return ⟨.closure typed.down (Core.infer_sound inferred)⟩
        else none
    | .cellRef _ _ => some ⟨.cellRef⟩
  termination_by sizeOf value

  private def buildEnvironment? (captured : Core.Environment) :
      Option (PLift (Core.EnvironmentHasTypes captured (captured.map Core.Value.type))) :=
    match captured with
    | [] => some ⟨.nil⟩
    | value :: rest => do
        let head ← buildValue? value
        let tail ← buildEnvironment? rest
        return ⟨.cons head.down tail.down⟩
  termination_by sizeOf captured
end

/-- Build an existing typed-argument record without replacing its actual value.
This checks structural typing, not allocation or a supplied runtime world. -/
def buildRuntimeArgument? (value : Core.Value) : Option TypedRuntimeArgument :=
  (buildValue? value).map (fun typed => ⟨value.type,value,typed.down⟩)

private theorem environment_types {definitions : Core.DataEnvironment}
    {environment : Core.Environment} {context : Core.Context}
    (typed : Core.EnvironmentHasTypes environment context definitions) :
    environment.map Core.Value.type = context := by
  induction typed using Core.EnvironmentHasTypes.rec
      (motive_1 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | pair | inLeft | inRight | closure | cellRef | constructed => trivial
  | nil => rfl
  | cons head _ _ ih => simp only [List.map_cons, head.type_eq, ih]

private theorem buildValue?_complete {definitions : Core.DataEnvironment}
    {value : Core.Value} {type : Core.Ty} (typed : Core.ValueHasType value type definitions)
    (empty : definitions = []) : (buildValue? value).isSome = true := by
  revert empty
  induction typed using Core.ValueHasType.rec
      (motive_2 := fun environment _ definitions _ =>
        definitions = [] → (buildEnvironment? environment).isSome = true) with
  | unit | bool | word | integer | cellRef => intro _; simp only [buildValue?, Option.isSome_some]
  | pair _ _ leftIH rightIH =>
      intro empty
      obtain ⟨left,leftChecked⟩ := Option.isSome_iff_exists.mp (leftIH empty)
      obtain ⟨right,rightChecked⟩ := Option.isSome_iff_exists.mp (rightIH empty)
      simp only [buildValue?, leftChecked, rightChecked, bind, Option.bind_some, pure, Option.isSome_some]
  | inLeft _ ih | inRight _ ih =>
      intro empty
      obtain ⟨proof,checked⟩ := Option.isSome_iff_exists.mp (ih empty)
      simp only [buildValue?, checked, bind, Option.bind_some, pure, Option.isSome_some]
  | closure environment body ih =>
      intro empty
      obtain ⟨proof,checked⟩ := Option.isSome_iff_exists.mp (ih empty)
      have inferred := Core.infer_complete body
      rw [empty, ← environment_types environment] at inferred
      simp only [buildValue?, checked, bind, Option.bind_some, dif_pos inferred, pure, Option.isSome_some]
  | constructed found _ _ => intro empty; rw [empty] at found; cases found
  | nil => simp only [buildEnvironment?, Option.isSome_some]
  | cons _ _ headIH tailIH =>
      rename_i empty
      obtain ⟨head,headChecked⟩ := Option.isSome_iff_exists.mp (headIH empty)
      obtain ⟨tail,tailChecked⟩ := Option.isSome_iff_exists.mp (tailIH empty)
      simp only [buildEnvironment?, headChecked, tailChecked, bind, Option.bind_some, pure, Option.isSome_some]

theorem buildRuntimeArgument?_iff {value : Core.Value} {argument : TypedRuntimeArgument} :
    buildRuntimeArgument? value = some argument ↔ argument.value = value := by
  constructor
  · intro built
    cases checked : buildValue? value with
    | none => simp only [buildRuntimeArgument?, checked, Option.map_none] at built; cases built
    | some proof =>
        simp only [buildRuntimeArgument?, checked, Option.map_some, Option.some.injEq] at built
        rw [← built]
  · intro same
    cases argument with
    | mk type original typed =>
        simp only at same
        subst original
        have tag := typed.type_eq
        subst type
        obtain ⟨proof,checked⟩ := Option.isSome_iff_exists.mp (buildValue?_complete typed rfl)
        simp only [buildRuntimeArgument?, checked, Option.map_some]

end Solcore.Frontend
