import Solcore.Frontend.ProgramSignatureFormation
import Solcore.TypeSystem.SubstitutionProperties

/-! Structural consequences of executable program-signature formation. -/

set_option autoImplicit false

namespace Solcore.Frontend

open TypeSystem

private theorem variablesBelow_applyMany
    {head : Ty} {arguments : List Ty} {next : Nat}
    (headBelow : head.VariablesBelow next)
    (argumentsBelow : ∀ argument, argument ∈ arguments →
      argument.VariablesBelow next) :
    (Ty.applyMany head arguments).VariablesBelow next := by
  induction arguments generalizing head with
  | nil => exact headBelow
  | cons argument arguments induction =>
      apply induction
      · exact (Ty.variablesBelow_application_iff _ _ _).mpr
          ⟨headBelow, argumentsBelow argument (by simp)⟩
      · intro candidate member
        exact argumentsBelow candidate (by simp [member])

/-- A frontend-validated signature type contains only rigid parameters and
closed constructors, so it is below every flexible-metavariable bound. -/
theorem SignatureTypeFormationValidated.variablesBelow
    {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeParameterId}
    {type : Ty}
    (validated : SignatureTypeFormationValidated signatures owner parameters
      type)
    (next : Nat) :
    type.VariablesBelow next := by
  refine SignatureTypeFormationValidated.rec
    (motive_1 := fun type _ => type.VariablesBelow next)
    (motive_2 := fun types _ => ∀ type ∈ types,
      type.VariablesBelow next)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ validated
  · intro parameter _ _
    exact Ty.variablesBelow_parameter next parameter
  · intro builtin
    exact Ty.variablesBelow_constructor next (.builtin builtin)
  · intro dataType arguments _ _ _ argumentsInduction
    exact variablesBelow_applyMany
      (Ty.variablesBelow_constructor next (.declaration dataType.id))
      argumentsInduction
  · intro contract arguments _ _ _ argumentsInduction
    exact variablesBelow_applyMany
      (Ty.variablesBelow_constructor next (.declaration contract.id))
      argumentsInduction
  · intro _ _ _ _ parameterInduction resultInduction
    exact (Ty.variablesBelow_function_iff _ _ _).mpr
      ⟨parameterInduction, resultInduction⟩
  · intro _ _ _ _ leftInduction rightInduction
    exact (Ty.variablesBelow_product_iff _ _ _).mpr
      ⟨leftInduction, rightInduction⟩
  · intro _ _ _ _ keyInduction valueInduction
    exact (Ty.variablesBelow_mapping_iff _ _ _).mpr
      ⟨keyInduction, valueInduction⟩
  · intro _ _ innerInduction
    exact (Ty.variablesBelow_proxy_iff _ _).mpr innerInduction
  · intro _ _ innerInduction
    exact (Ty.variablesBelow_comptime_iff _ _).mpr innerInduction
  · intro type member
    simp at member
  · intro head tail _ _ headInduction tailInduction type member
    rcases List.mem_cons.mp member with rfl | member
    · exact headInduction
    · exact tailInduction type member

/-- Every member of a frontend-validated signature type row is below every
flexible-metavariable bound. -/
theorem SignatureTypesFormationValidated.variablesBelow
    {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeParameterId}
    {types : List Ty}
    (validated : SignatureTypesFormationValidated signatures owner parameters
      types)
    (next : Nat) :
    ∀ type ∈ types, type.VariablesBelow next := by
  cases validated with
  | nil => simp
  | cons headValidated tailValidated =>
      intro type member
      rcases List.mem_cons.mp member with rfl | member
      · exact headValidated.variablesBelow next
      · exact tailValidated.variablesBelow next type member

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
