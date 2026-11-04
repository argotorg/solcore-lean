import Solcore.TypeSystem.Scheme
import Solcore.TypeSystem.Internal.SubstitutionLaws
import Solcore.TypeSystem.Unification

/-!
# Laws of substitutions and schemes

Small laws of `TypeSystem.Substitution` and `TypeSystem.Scheme`, and correlated rigid instances.
-/

section
-- leanmerge: from Solcore.TypeSystem.Properties
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
end

section
-- leanmerge: from Solcore.TypeSystem.CorrelatedParameterInstances
/-! Recover correlated rigid instances from equal flexible instances of one
original type. Rigid replacement ranges contain no flexible variables. Local
substitutions remain arbitrary and need not be injective. -/
set_option autoImplicit false
namespace Solcore.TypeSystem.CorrelatedParameterInstances
open Solcore.TypeSystem

private theorem congr_two {α β γ : Type} (function : α → β → γ)
    {left first : α} {right second : β}
    (sameLeft : left = first) (sameRight : right = second) :
    function left right = function first second := by
  cases sameLeft
  cases sameRight
  rfl

private theorem parameter_fixed
    (rigid : ParameterSubstitution) (localSubstitution : Substitution)
    (closed : ∀ parameter replacement,
      rigid.lookup? parameter = some replacement → replacement.freeVariables = [])
    (parameter : TypeParameterId) :
    localSubstitution.apply (rigid.apply (.parameter parameter)) =
      rigid.apply (.parameter parameter) := by
  cases found : rigid.lookup? parameter with
  | none =>
    simp only [ParameterSubstitution.apply, found, Option.getD_none,
      Substitution.apply]
  | some replacement =>
    simp only [ParameterSubstitution.apply, found, Option.getD_some]
    apply Ty.apply_eq_self_of_domain_disjoint_freeVariables
    intro metavariable _member occurs
    rw [closed parameter replacement found] at occurs
    cases occurs

/-- Equal local instances of the same original type retain the same rigid
instance. Flexible variables in the original type are allowed: their original
positions coincide before either local substitution is applied. -/
theorem apply_parameters_eq_of_equal_local_instances
    (original : Ty) (left right : ParameterSubstitution)
    (leftLocal rightLocal : Substitution)
    (leftClosed : ∀ parameter replacement,
      left.lookup? parameter = some replacement → replacement.freeVariables = [])
    (rightClosed : ∀ parameter replacement,
      right.lookup? parameter = some replacement → replacement.freeVariables = [])
    (same : leftLocal.apply (left.apply original) =
      rightLocal.apply (right.apply original)) :
    left.apply original = right.apply original := by
  revert same
  induction original with
  | «variable» metavariable =>
    intro _same
    rfl
  | parameter parameter =>
    intro same
    exact (parameter_fixed left leftLocal leftClosed parameter).symm.trans
      (same.trans (parameter_fixed right rightLocal rightClosed parameter))
  | constructor constructorId =>
    intro _same
    rfl
  | application function argument functionIH argumentIH =>
    intro same
    dsimp only [ParameterSubstitution.apply, Substitution.apply] at same ⊢
    obtain ⟨functionSame, argumentSame⟩ := Ty.application.inj same
    exact congr_two Ty.application (functionIH functionSame) (argumentIH argumentSame)
  | function parameter result parameterIH resultIH =>
    intro same
    dsimp only [ParameterSubstitution.apply, Substitution.apply] at same ⊢
    obtain ⟨parameterSame, resultSame⟩ := Ty.function.inj same
    exact congr_two Ty.function (parameterIH parameterSame) (resultIH resultSame)
  | product first second firstIH secondIH =>
    intro same
    dsimp only [ParameterSubstitution.apply, Substitution.apply] at same ⊢
    obtain ⟨firstSame, secondSame⟩ := Ty.product.inj same
    exact congr_two Ty.product (firstIH firstSame) (secondIH secondSame)
  | mapping key value keyIH valueIH =>
    intro same
    dsimp only [ParameterSubstitution.apply, Substitution.apply] at same ⊢
    obtain ⟨keySame, valueSame⟩ := Ty.mapping.inj same
    exact congr_two Ty.mapping (keyIH keySame) (valueIH valueSame)
  | proxy inner innerIH =>
    intro same
    dsimp only [ParameterSubstitution.apply, Substitution.apply] at same ⊢
    exact congrArg Ty.proxy (innerIH (Ty.proxy.inj same))
  | comptime inner innerIH =>
    intro same
    dsimp only [ParameterSubstitution.apply, Substitution.apply] at same ⊢
    exact congrArg Ty.comptime (innerIH (Ty.comptime.inj same))
  | error =>
    intro _same
    rfl

/-- Ordered type fields recover position by position. Repeated fields and
unused rigid arguments are retained; no set of types replaces the list. -/
theorem apply_parameters_list_eq_of_equal_local_instances
    (original : List Ty) (left right : ParameterSubstitution)
    (leftLocal rightLocal : Substitution)
    (leftClosed : ∀ parameter replacement,
      left.lookup? parameter = some replacement → replacement.freeVariables = [])
    (rightClosed : ∀ parameter replacement,
      right.lookup? parameter = some replacement → replacement.freeVariables = [])
    (same : (original.map left.apply).map leftLocal.apply =
      (original.map right.apply).map rightLocal.apply) :
    original.map left.apply = original.map right.apply := by
  revert same
  induction original with
  | nil =>
    intro _same
    rfl
  | cons first rest ih =>
    intro same
    simp only [List.map_cons] at same ⊢
    obtain ⟨firstSame, restSame⟩ := List.cons.inj same
    exact congr_two List.cons
      (apply_parameters_eq_of_equal_local_instances first left right leftLocal
        rightLocal leftClosed rightClosed firstSame)
      (ih restSame)

end Solcore.TypeSystem.CorrelatedParameterInstances
end
