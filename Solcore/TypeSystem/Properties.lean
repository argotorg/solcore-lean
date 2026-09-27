import Solcore.TypeSystem.Scheme
import Solcore.TypeSystem.SubstitutionProperties
import Solcore.TypeSystem.Unification

set_option autoImplicit false

namespace Solcore.TypeSystem

namespace Substitution

@[simp]
theorem lookup?_empty (metavariable : TypeVarId) :
    empty.lookup? metavariable = none :=
  rfl

@[simp]
theorem lookup?_cons_self (metavariable : TypeVarId) (replacement : Ty)
    (rest : Substitution) :
    lookup? ((metavariable, replacement) :: rest) metavariable = some replacement := by
  simp [lookup?]

theorem lookup?_cons_of_ne {candidate metavariable : TypeVarId} (replacement : Ty)
    (rest : Substitution) (different : candidate ≠ metavariable) :
    lookup? ((candidate, replacement) :: rest) metavariable = lookup? rest metavariable := by
  simp [lookup?, different]

@[simp]
theorem empty_apply (type : Ty) : empty.apply type = type := by
  induction type <;> simp_all [empty, apply, lookup?]

theorem apply_variable_of_lookup?_eq_some {substitution : Substitution}
    {metavariable : TypeVarId} {replacement : Ty}
    (found : substitution.lookup? metavariable = some replacement) :
    substitution.apply (.variable metavariable) = replacement := by
  simp [apply, found]

theorem apply_variable_of_lookup?_eq_none {substitution : Substitution}
    {metavariable : TypeVarId}
    (missing : substitution.lookup? metavariable = none) :
    substitution.apply (.variable metavariable) = .variable metavariable := by
  simp [apply, missing]

private theorem lookup?_filter_ne (substitution : Substitution)
    (erased metavariable : TypeVarId) :
    lookup? (substitution.filter fun entry => entry.1 != erased) metavariable =
      if metavariable = erased then none else substitution.lookup? metavariable := by
  induction substitution with
  | nil => simp [lookup?]
  | cons entry rest ih =>
      rcases entry with ⟨candidate, replacement⟩
      by_cases candidate_erased : candidate = erased
      · subst candidate
        by_cases same : erased = metavariable
        · subst metavariable
          simpa using ih
        · simpa [lookup?, same, Ne.symm same] using ih
      · by_cases same : candidate = metavariable
        · subst candidate
          simp [lookup?, candidate_erased]
        · simp [lookup?, candidate_erased, same, ih]

@[simp]
theorem lookup?_erase_self (substitution : Substitution) (metavariable : TypeVarId) :
    (substitution.erase metavariable).lookup? metavariable = none := by
  rw [erase]
  simpa using lookup?_filter_ne substitution metavariable metavariable

theorem lookup?_erase_of_ne (substitution : Substitution) {erased metavariable : TypeVarId}
    (different : metavariable ≠ erased) :
    (substitution.erase erased).lookup? metavariable =
      substitution.lookup? metavariable := by
  rw [erase]
  simpa [different] using lookup?_filter_ne substitution erased metavariable

theorem lookup?_without_of_lookup?_eq_none (substitution : Substitution)
    (variables : List TypeVarId) {metavariable : TypeVarId}
    (missing : substitution.lookup? metavariable = none) :
    (substitution.without variables).lookup? metavariable = none := by
  induction variables generalizing substitution with
  | nil => simpa [without] using missing
  | cons erasedVariable variables ih =>
      rw [without, List.foldl_cons]
      apply ih
      by_cases same : metavariable = erasedVariable
      · subst erasedVariable
        exact lookup?_erase_self substitution metavariable
      · rw [lookup?_erase_of_ne substitution same]
        exact missing

theorem lookup?_without_of_mem (substitution : Substitution)
    {variables : List TypeVarId} {metavariable : TypeVarId}
    (quantified : metavariable ∈ variables) :
    (substitution.without variables).lookup? metavariable = none := by
  induction variables generalizing substitution with
  | nil => simp at quantified
  | cons erasedVariable variables ih =>
      rw [without, List.foldl_cons]
      rcases List.mem_cons.mp quantified with same | quantified
      · subst erasedVariable
        exact lookup?_without_of_lookup?_eq_none
          (substitution.erase metavariable) variables
          (lookup?_erase_self substitution metavariable)
      · exact ih (substitution := substitution.erase erasedVariable) quantified

end Substitution

namespace Scheme

@[simp]
theorem mono_apply (substitution : Substitution) (type : Ty) :
    (mono type).apply substitution = mono (substitution.apply type) := by
  simp [mono, apply, Substitution.without]

@[simp]
theorem apply_quantified (substitution : Substitution) (scheme : Scheme) :
    (scheme.apply substitution).quantified = scheme.quantified :=
  rfl

theorem quantified_variable_protected (substitution : Substitution)
    {quantified : List TypeVarId} {metavariable : TypeVarId}
    (member : metavariable ∈ quantified) :
    (apply substitution { quantified, body := .variable metavariable }).body =
      .variable metavariable := by
  simp [apply, Substitution.apply,
    Substitution.lookup?_without_of_mem substitution member]

end Scheme

namespace Unification

theorem unifyWithFuel_reflexive_sound {fuel : Nat} {type : Ty}
    {substitution : Substitution}
    (success : unifyWithFuel (fuel + 2) [{ left := type, right := type }] =
      .ok substitution) :
    substitution = [] ∧ substitution.apply type = type := by
  rw [unifyWithFuel_reflexive] at success
  injection success with substitution_empty
  subst substitution
  exact ⟨rfl, Substitution.empty_apply type⟩

theorem unifyWithFuel_variable_constructor_sound {fuel : Nat}
    {metavariable : TypeVarId} {constructor : TypeConstructorId}
    {substitution : Substitution}
    (success : unifyWithFuel (fuel + 2)
      [{ left := .variable metavariable, right := .constructor constructor }] =
        .ok substitution) :
    substitution = [(metavariable, .constructor constructor)] ∧
      substitution.apply (.variable metavariable) =
        substitution.apply (.constructor constructor) := by
  rw [unifyWithFuel_variable_constructor] at success
  injection success with substitution_binding
  subst substitution
  simp [Substitution.apply, Substitution.lookup?]

end Unification

end Solcore.TypeSystem
