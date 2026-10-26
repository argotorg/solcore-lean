import Solcore.Synthesis.Source.ScalarMeaning.Semantics

/-! Lookup, declaration and assignment laws for the lexical scopes of the
scalar source semantics. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

theorem Scope.get?_eq_none_of_not_mem {scope : Scope} {name : String}
    (absent : name ∉ scope.names) : scope.get? name = none := by
  induction scope with
  | nil => rfl
  | cons binding rest ih =>
      obtain ⟨bound, value⟩ := binding
      simp only [Scope.names, List.map_cons, List.mem_cons, not_or] at absent
      simp only [Scope.get?, if_neg (Ne.symm absent.1)]
      exact ih absent.2

theorem Scope.set?_spec {scope : Scope} {name : String} {old : Value} (value : Value)
    (found : scope.get? name = some old) :
    ∃ scope', scope.set? name value = some scope' ∧ scope'.names = scope.names ∧
      ∀ other, scope'.get? other = if name = other then some value else scope.get? other := by
  induction scope with
  | nil => simp [Scope.get?] at found
  | cons binding rest ih =>
      obtain ⟨bound, previous⟩ := binding
      by_cases same : bound = name
      · subst same
        refine ⟨(bound, value) :: rest, by simp [Scope.set?], rfl, ?_⟩
        intro other
        by_cases hit : bound = other <;> simp [Scope.get?, hit]
      · simp only [Scope.get?, if_neg same] at found
        obtain ⟨rest', set, names, lookup⟩ := ih found
        refine ⟨(bound, previous) :: rest', by simp [Scope.set?, same, set], ?_, ?_⟩
        · simp [Scope.names] at names ⊢
          exact names
        · intro other
          by_cases hit : bound = other
          · subst hit
            simp [Scope.get?, Ne.symm same]
          · simp [Scope.get?, hit, lookup other]

theorem Scope.set?_eq_none {scope : Scope} {name : String} (value : Value)
    (absent : scope.get? name = none) : scope.set? name value = none := by
  induction scope with
  | nil => rfl
  | cons binding rest ih =>
      obtain ⟨bound, previous⟩ := binding
      by_cases same : bound = name
      · simp [Scope.get?, same] at absent
      · simp only [Scope.get?, if_neg same] at absent
        simp [Scope.set?, same, ih absent]

theorem Frames.lookup_cons (scope : Scope) (outer : Frames) (name : String) :
    Frames.lookup (scope :: outer) name = (scope.get? name).or (Frames.lookup outer name) := by
  simp only [Frames.lookup]
  cases scope.get? name <;> rfl

theorem Frames.lookup_cons_of_not_mem {scope : Scope} {name : String} (outer : Frames)
    (absent : name ∉ scope.names) :
    Frames.lookup (scope :: outer) name = Frames.lookup outer name := by
  rw [Frames.lookup_cons, Scope.get?_eq_none_of_not_mem absent]
  rfl

@[simp] theorem Frames.lookup_nil_cons (outer : Frames) (name : String) :
    Frames.lookup ([] :: outer) name = Frames.lookup outer name :=
  rfl

theorem Frames.lookup_declared (scope : Scope) (outer : Frames) (declared : String)
    (value : Value) (name : String) :
    Frames.lookup (((declared, value) :: scope) :: outer) name =
      if declared = name then some value else Frames.lookup (scope :: outer) name := by
  by_cases same : declared = name
  · simp [Frames.lookup, Scope.get?, same]
  · simp [Frames.lookup, Scope.get?, same]

theorem Frames.assign_spec {frames : Frames} {name : String} {old : Value} (value : Value)
    (found : frames.lookup name = some old) :
    ∃ frames', frames.assign name value = some frames' ∧ frames'.shape = frames.shape ∧
      ∀ other, frames'.lookup other =
        if name = other then some value else frames.lookup other := by
  induction frames with
  | nil => simp [Frames.lookup] at found
  | cons scope outer ih =>
      cases inScope : scope.get? name with
      | some current =>
          obtain ⟨scope', set, names, lookup⟩ := Scope.set?_spec value inScope
          refine ⟨scope' :: outer, by simp [Frames.assign, set], ?_, ?_⟩
          · simp [Frames.shape, names]
          · intro other
            rw [Frames.lookup_cons, Frames.lookup_cons, lookup other]
            by_cases hit : name = other <;> simp [hit]
      | none =>
          rw [Frames.lookup_cons, inScope] at found
          obtain ⟨outer', assign, shape, lookup⟩ := ih found
          refine ⟨scope :: outer', ?_, ?_, ?_⟩
          · simp [Frames.assign, Scope.set?_eq_none value inScope, assign]
          · simp only [Frames.shape, List.map_cons] at shape ⊢
            rw [shape]
          · intro other
            rw [Frames.lookup_cons, Frames.lookup_cons, lookup other]
            by_cases hit : name = other
            · subst hit
              simp [inScope]
            · simp [hit]

end Solcore.Synthesis.Source.ScalarMeaning
