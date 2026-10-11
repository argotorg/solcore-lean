import Solcore.TypeSystem.SubstitutionProperties

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
