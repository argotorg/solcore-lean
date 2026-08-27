import Solcore.Core.Renaming
import Solcore.Core.Store

set_option autoImplicit false

namespace Solcore.Core

mutual

  inductive ValuesRelated : Value → Value → Prop where
    | unit : ValuesRelated .unit .unit
    | bool (value : Bool) : ValuesRelated (.bool value) (.bool value)
    | word (value : Word) : ValuesRelated (.word value) (.word value)
    | pair {left left' right right' : Value} :
        ValuesRelated left left' → ValuesRelated right right' →
        ValuesRelated (.pair left right) (.pair left' right')
    | closure
        {parameterType resultType : Ty} {body : Expr}
        {environment environment' : Environment}
        (mapping : Renaming)
        (environments : EnvironmentsRelated mapping environment environment') :
        ValuesRelated
          (.closure parameterType resultType body environment)
          (.closure parameterType resultType
            (body.rename mapping.lift) environment')
    | inLeft {rightType : Ty} {payload payload' : Value} :
        ValuesRelated payload payload' →
        ValuesRelated (.inLeft rightType payload) (.inLeft rightType payload')
    | inRight {leftType : Ty} {payload payload' : Value} :
        ValuesRelated payload payload' →
        ValuesRelated (.inRight leftType payload) (.inRight leftType payload')
    | cellRef {elementType : Ty} {location : Location} :
        ValuesRelated (.cellRef elementType location) (.cellRef elementType location)
    | constructed {constructor : ConstructorId} {payload payload' : Value} :
        ValuesRelated payload payload' →
        ValuesRelated (.constructed constructor payload)
          (.constructed constructor payload')

  inductive EnvironmentsRelated :
      Renaming → Environment → Environment → Prop where
    | intro
        {mapping : Renaming} {source target : Environment}
        (targetBounds : ∀ index, index < source.length →
          mapping index < target.length)
        (values : ∀ (index) (sourceBound : index < source.length),
          ValuesRelated (getElem source index sourceBound)
            (getElem target (mapping index) (targetBounds index sourceBound))) :
        EnvironmentsRelated mapping source target

end

namespace EnvironmentsRelated

theorem lookup
    {mapping : Renaming} {source target : Environment}
    (related : EnvironmentsRelated mapping source target)
    {index : Nat} {value : Value}
    (found : source[index]? = some value) :
    ∃ value', target[mapping index]? = some value' ∧ ValuesRelated value value' := by
  cases related with
  | intro targetBounds values =>
      obtain ⟨sourceBound, valueEquality⟩ :=
        List.getElem?_eq_some_iff.mp found
      subst value
      let targetBound := targetBounds index sourceBound
      exact ⟨target[mapping index],
        List.getElem?_eq_getElem targetBound, values index sourceBound⟩

theorem empty (mapping : Renaming) (target : Environment) :
    EnvironmentsRelated mapping [] target := by
  constructor
  · intro index sourceBound
    simp at sourceBound
  · intro index sourceBound
    simp at sourceBound

theorem extend
    {mapping : Renaming} {source target : Environment}
    (environments : EnvironmentsRelated mapping source target)
    {value value' : Value}
    (values : ValuesRelated value value') :
    EnvironmentsRelated mapping.lift (value :: source) (value' :: target) := by
  cases environments with
  | intro targetBounds relatedValues =>
      constructor
      · intro index sourceBound
        cases index with
        | zero =>
            change ValuesRelated value value'
            exact values
        | succ index =>
            simp [Renaming.lift] at sourceBound ⊢
            exact relatedValues index sourceBound
      · intro index sourceBound
        cases index with
        | zero => simp [Renaming.lift]
        | succ index =>
            simp [Renaming.lift] at sourceBound ⊢
            exact targetBounds index sourceBound

mutual

  theorem ValuesRelated.refl : ∀ value : Value, ValuesRelated value value
    | .unit => .unit
    | .bool value => .bool value
    | .word value => .word value
    | .pair left right =>
        .pair (ValuesRelated.refl left) (ValuesRelated.refl right)
    | .closure parameterType resultType body environment => by
        simpa using ValuesRelated.closure Renaming.id
          (EnvironmentsRelated.refl environment)
    | .inLeft rightType payload => .inLeft (ValuesRelated.refl payload)
    | .inRight leftType payload => .inRight (ValuesRelated.refl payload)
    | .cellRef elementType location => .cellRef
    | .constructed constructor payload =>
        .constructed (ValuesRelated.refl payload)

  theorem EnvironmentsRelated.refl : ∀ environment : Environment,
      EnvironmentsRelated Renaming.id environment environment
    | [] => EnvironmentsRelated.empty Renaming.id []
    | value :: rest => by
        simpa using (EnvironmentsRelated.refl rest).extend (ValuesRelated.refl value)

end

end EnvironmentsRelated

namespace ValuesRelated

theorem unit_iff {target : Value} :
    ValuesRelated .unit target ↔ target = .unit := by
  constructor
  · intro related
    cases related
    rfl
  · rintro rfl
    exact .unit

theorem bool_iff {value : Bool} {target : Value} :
    ValuesRelated (.bool value) target ↔ target = .bool value := by
  constructor
  · intro related
    cases related
    rfl
  · rintro rfl
    exact .bool value

theorem word_iff {value : Word} {target : Value} :
    ValuesRelated (.word value) target ↔ target = .word value := by
  constructor
  · intro related
    cases related
    rfl
  · rintro rfl
    exact .word value

end ValuesRelated

inductive StoresRelated : Store → Store → Prop where
  | nil : StoresRelated [] []
  | cons {value value' : Value} {rest rest' : Store} :
      ValuesRelated value value' → StoresRelated rest rest' →
      StoresRelated (value :: rest) (value' :: rest')

namespace StoresRelated

@[simp] theorem length_eq
    {source target : Store} (related : StoresRelated source target) :
    source.length = target.length := by
  induction related with
  | nil => rfl
  | cons _ _ inductionHypothesis => simp [inductionHypothesis]

theorem lookup
    {source target : Store} (related : StoresRelated source target)
    {location : Location} {value : Value}
    (found : source[location]? = some value) :
    ∃ value', target[location]? = some value' ∧ ValuesRelated value value' := by
  induction related generalizing location value with
  | nil => simp at found
  | cons headRelated tailRelated inductionHypothesis =>
      cases location with
      | zero =>
          simp at found
          subst value
          exact ⟨_, by simp, headRelated⟩
      | succ location =>
          simp at found ⊢
          exact inductionHypothesis found

theorem read
    {source target : Store} (related : StoresRelated source target)
    {location : Location} {value : Value}
    (read : source.read? location = some value) :
    ∃ value', target.read? location = some value' ∧ ValuesRelated value value' :=
  related.lookup read

theorem allocate
    {source target : Store} (stores : StoresRelated source target)
    {value value' : Value} (values : ValuesRelated value value') :
    StoresRelated (source.allocate value).1 (target.allocate value').1 ∧
      (source.allocate value).2 = (target.allocate value').2 := by
  constructor
  · simp only [Store.allocate]
    induction stores with
    | nil => exact .cons values .nil
    | cons headRelated tailRelated inductionHypothesis =>
        exact .cons headRelated inductionHypothesis
  · simp [Store.allocate, stores.length_eq]

theorem set
    {source target : Store} (stores : StoresRelated source target)
    {location : Location} {value value' : Value}
    (values : ValuesRelated value value')
    (inBounds : location < source.length) :
    StoresRelated (source.set location value) (target.set location value') := by
  induction stores generalizing location with
  | nil => simp at inBounds
  | cons headRelated tailRelated inductionHypothesis =>
      cases location with
      | zero => exact .cons values tailRelated
      | succ location =>
          simp at inBounds
          exact .cons headRelated (inductionHypothesis inBounds)

theorem write
    {source target updatedSource : Store}
    (stores : StoresRelated source target)
    {location : Location} {value value' : Value}
    (values : ValuesRelated value value')
    (written : source.write? location value = some updatedSource) :
    ∃ updatedTarget,
      target.write? location value' = some updatedTarget ∧
        StoresRelated updatedSource updatedTarget := by
  obtain ⟨sourceBound, rfl⟩ := Store.write?_eq_some_iff.mp written
  have targetBound : location < target.length := by
    rw [← stores.length_eq]
    exact sourceBound
  exact ⟨target.set location value',
    Store.write?_eq_some_iff.mpr ⟨targetBound, rfl⟩,
    stores.set values sourceBound⟩

end StoresRelated

end Solcore.Core
