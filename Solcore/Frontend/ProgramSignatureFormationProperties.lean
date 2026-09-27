import Solcore.Frontend.ProgramSignatureFormation
import Solcore.TypeSystem.SubstitutionProperties

/-! Structural consequences of executable program-signature formation. -/

set_option autoImplicit false

namespace Solcore.Frontend

open TypeSystem

/-- A frontend-validated signature type contains no flexible metavariables,
so every flexible substitution fixes it. -/
theorem SignatureTypeFormationValidated.apply_eq_self
    {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeParameterId}
    {type : Ty}
    (validated : SignatureTypeFormationValidated signatures owner parameters
      type)
    (substitution : Substitution) :
    substitution.apply type = type := by
  refine SignatureTypeFormationValidated.rec
    (motive_1 := fun type _ => substitution.apply type = type)
    (motive_2 := fun types _ => types.map substitution.apply = types)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ validated
  · intro parameter _ _
    rfl
  · intro builtin
    rfl
  · intro dataType arguments _ _ _ argumentsInduction
    simp only [Ty.nominal, TypeSystem.Substitution.apply_applyMany]
    rw [argumentsInduction]
    rfl
  · intro contract arguments _ _ _ argumentsInduction
    simp only [Ty.nominal, TypeSystem.Substitution.apply_applyMany]
    rw [argumentsInduction]
    rfl
  · intro parameter result _ _ parameterInduction resultInduction
    simp only [Substitution.apply]
    rw [parameterInduction, resultInduction]
  · intro left right _ _ leftInduction rightInduction
    simp only [Substitution.apply]
    rw [leftInduction, rightInduction]
  · intro key value _ _ keyInduction valueInduction
    simp only [Substitution.apply]
    rw [keyInduction, valueInduction]
  · intro inner _ innerInduction
    simp only [Substitution.apply]
    rw [innerInduction]
  · intro inner _ innerInduction
    simp only [Substitution.apply]
    rw [innerInduction]
  · rfl
  · intro head tail _ _ headInduction tailInduction
    simp only [List.map_cons]
    rw [headInduction, tailInduction]

/-- Pointwise executable signature formation makes a whole type row invariant
under flexible substitution. -/
theorem SignatureTypesFormationValidated.apply_eq_self
    {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeParameterId}
    {types : List Ty}
    (validated : SignatureTypesFormationValidated signatures owner parameters
      types)
    (substitution : Substitution) :
    types.map substitution.apply = types := by
  cases validated with
  | nil => rfl
  | cons headValidated tailValidated =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨headValidated.apply_eq_self substitution,
        tailValidated.apply_eq_self substitution⟩

/-- The declared return bundle assembled from a validated signature type row
is invariant under every flexible substitution. -/
theorem SignatureTypesFormationValidated.apply_productMany_eq_self
    {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeParameterId}
    {types : List Ty}
    (validated : SignatureTypesFormationValidated signatures owner parameters
      types)
    (substitution : Substitution) :
    substitution.apply (Ty.productMany types) = Ty.productMany types := by
  rw [TypeSystem.Substitution.apply_productMany,
    validated.apply_eq_self substitution]

end Solcore.Frontend
