import Solcore.Frontend.RuntimeValue

/-!
Exact representation laws have no typing, checking, execution or world premises.
Private list proofs preserve every ordered capture; successful projection loses no data.
-/

set_option autoImplicit false

namespace Solcore.Frontend

namespace RuntimeValue

private theorem project_attached (values : List RuntimeValue) :
    values.attach.mapM (fun value => toCore? value.val) = values.mapM toCore? := by
  change values.attach.mapM (toCore? ∘ Subtype.val) = _
  rw [← List.mapM_map, List.attach_map_subtype_val]

private theorem project_embedded_list (values : List Core.Value)
    (roundtrip : ∀ value ∈ values, toCore? (ofCore value) = some value) :
    (values.map ofCore).mapM toCore? = some values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.mapM_cons, roundtrip head (by simp),
        ih (fun value member => roundtrip value (by simp [member])),
        bind, Option.bind_some, pure]

/-- Embedding and then projecting returns the identical original Core value. -/
theorem toCore?_ofCore (value : Core.Value) : toCore? (ofCore value) = some value := by
  cases value with
  | unit | bool | word | hostFunction | cellRef => simp only [ofCore, toCore?]
  | pair left right =>
      simp only [ofCore, toCore?, toCore?_ofCore left, toCore?_ofCore right,
        bind, Option.bind_some, pure]
  | inLeft type payload | inRight type payload | constructed type payload =>
      simp only [ofCore, toCore?, toCore?_ofCore payload, Option.map_some]
  | closure parameterType resultType body captured =>
      simp only [ofCore, toCore?, List.attach_map_val, project_attached]
      rw [project_embedded_list captured (fun value member => toCore?_ofCore value)]
      rfl
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals try omega
  have smaller := List.sizeOf_lt_of_mem member
  omega

private theorem project_list_reflect (values : List RuntimeValue)
    (reflection : ∀ value ∈ values, ∀ core, toCore? value = some core → value = ofCore core)
    {cores : List Core.Value} (projected : values.mapM toCore? = some cores) :
    values = cores.map ofCore := by
  induction values generalizing cores with
  | nil =>
      have equality : [] = cores := Option.some.inj projected
      subst cores
      rfl
  | cons head tail ih =>
      simp only [List.mapM_cons, bind, Option.bind_eq_some_iff] at projected
      obtain ⟨core, headProjected, rest, tailProjected, equality⟩ := projected
      cases Option.some.inj equality
      change head :: tail = ofCore core :: rest.map ofCore
      rw [reflection head (by simp) core headProjected,
        ih (fun value member => reflection value (by simp [member])) tailProjected]

private theorem project_reflect (value : RuntimeValue) {core : Core.Value}
    (projected : toCore? value = some core) : value = ofCore core := by
  cases value with
  | unit | bool | word | hostFunction | cellRef =>
      simp only [toCore?, Option.some.injEq] at projected
      subst core
      simp only [ofCore]
  | pair left right =>
      simp only [toCore?, bind, Option.bind_eq_some_iff] at projected
      obtain ⟨leftCore, leftProjected, rightCore, rightProjected, equality⟩ := projected
      cases Option.some.inj equality
      simp only [ofCore]
      rw [project_reflect left leftProjected, project_reflect right rightProjected]
  | inLeft type payload | inRight type payload | constructed type payload =>
      simp only [toCore?, Option.map_eq_some_iff] at projected
      obtain ⟨payloadCore, payloadProjected, rfl⟩ := projected
      simp only [ofCore]
      congr 1
      exact project_reflect payload payloadProjected
  | coreClosure parameterType resultType body captured =>
      simp only [toCore?, project_attached, Option.map_eq_some_iff] at projected
      obtain ⟨cores, capturesProjected, rfl⟩ := projected
      simp only [ofCore, List.attach_map_val]
      congr 1
      exact project_list_reflect captured
        (fun value member core projected => project_reflect value projected) capturesProjected
  | sourceClosure source owner names captured =>
      simp only [toCore?, reduceCtorEq] at projected
termination_by sizeOf value
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals try omega
  have smaller := List.sizeOf_lt_of_mem member
  omega

/-- Successful structural projection characterizes precisely the embedded Core-value image. -/
theorem toCore?_eq_some_iff {value : RuntimeValue} {core : Core.Value} :
    toCore? value = some core ↔ value = ofCore core := by
  constructor
  · exact project_reflect value
  · intro equality
    subst value
    exact toCore?_ofCore core

/-- Distinct original values remain distinct after embedding. -/
theorem ofCore_injective : Function.Injective ofCore := by
  intro left right equality
  have projected := congrArg toCore? equality
  simpa only [toCore?_ofCore, Option.some.injEq] using projected

end RuntimeValue

end Solcore.Frontend
