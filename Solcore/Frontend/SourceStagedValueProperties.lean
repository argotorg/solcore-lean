import Solcore.Frontend.SourceStagedValue

/-! Structural laws for the closed staged-value carrier. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceStagedValue

/-- Every staged value survives projection after embedding into Semantic Core. -/
@[simp] theorem ofCore?_toCore (value : Value) :
    ofCore? (toCore value) = some value := by
  induction value <;> simp_all [ofCore?, toCore]

/-- Successful projection reflects the complete Core representation. -/
private theorem project_reflect (core : Core.Value) {value : Value}
    (projected : ofCore? core = some value) :
    core = toCore value := by
  cases core with
  | unit | bool | word =>
      simp only [ofCore?, Option.some.injEq] at projected
      subst value
      rfl
  | pair left right =>
      simp only [ofCore?, bind, Option.bind_eq_some_iff] at projected
      obtain ⟨leftValue, leftProjected, rightValue, rightProjected, equality⟩ := projected
      cases Option.some.inj equality
      simp only [toCore]
      rw [project_reflect left leftProjected, project_reflect right rightProjected]
  | hostFunction | closure | inLeft | inRight | cellRef | constructed =>
      simp only [ofCore?, reduceCtorEq] at projected
termination_by sizeOf core
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega

/-- A successful Core projection identifies the original Core value exactly. -/
theorem ofCore?_eq_some_iff {core : Core.Value} {value : Value} :
    ofCore? core = some value ↔ core = toCore value := by
  constructor
  · exact project_reflect core
  · intro equal
    subst core
    exact ofCore?_toCore value

/-- Successful projection preserves the exact structural Core type. -/
theorem ofCore?_eq_some_type {core : Core.Value} {value : Value}
    (projected : ofCore? core = some value) :
    core.type = coreType value := by
  rw [(ofCore?_eq_some_iff.mp projected)]
  exact toCore_type value

/-- Projection of one Core value has at most one staged result. -/
theorem ofCore?_eq_some_unique {core : Core.Value} {left right : Value}
    (leftProjected : ofCore? core = some left)
    (rightProjected : ofCore? core = some right) :
    left = right := by
  rw [leftProjected] at rightProjected
  exact Option.some.inj rightProjected

/-- Embedding into Semantic Core does not identify distinct staged values. -/
theorem toCore_injective : Function.Injective toCore := by
  intro left right equal
  apply Option.some.inj
  simpa only [ofCore?_toCore] using congrArg ofCore? equal

@[simp] theorem toCore_inj {left right : Value} :
    toCore left = toCore right ↔ left = right :=
  toCore_injective.eq_iff

/-- Source typing is also uniquely determined by an embedded Core value. -/
theorem sourceType_eq_of_toCore_eq {left right : Value}
    (equal : toCore left = toCore right) :
    sourceType left = sourceType right := by
  rw [toCore_injective equal]

end Solcore.Frontend.SourceStagedValue
