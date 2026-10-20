import Solcore.SourceSemantics.SubstitutionProperties
import Solcore.TypeSystem.Unification

/-! Formation recovered from the actual domain of a successful unifier. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.UnificationFormation
open Frontend TypeSystem

private def applicationArguments : Ty → List Ty
  | .application head argument => applicationArguments head ++ [argument]
  | _ => []

private theorem arguments_applyMany (head : Ty) (arguments : List Ty) :
    applicationArguments (Ty.applyMany head arguments) = applicationArguments head ++ arguments := by
  induction arguments generalizing head with
  | nil => simp [Ty.applyMany]
  | cons argument rest ih =>
    change applicationArguments (Ty.applyMany (.application head argument) rest) = _
    rw [ih]
    simp [applicationArguments, List.append_assoc]

private theorem arguments_nominal (declaration : Resolved.DeclarationId) (arguments : List Ty) :
    applicationArguments (Ty.nominal declaration arguments) = arguments := by
  simp [Ty.nominal, arguments_applyMany, applicationArguments]

private theorem scoped_arguments {context : Context} {variables : List TypeVarId} {type : Ty}
    (typed : TypeWellScoped context variables type) :
    ∀ argument ∈ applicationArguments type, TypeWellScoped context variables argument := by
  cases typed with
  | nominal declaration arguments member arity typed
  | contractNominal declaration arguments member arity typed =>
    rw [arguments_nominal]
    intro argument member
    exact typed.member member
  | _ => simp [applicationArguments]

private def applicationHead : Ty → Ty
  | .application head _ => applicationHead head
  | other => other

private theorem head_applyMany (head : Ty) (arguments : List Ty) :
    applicationHead (Ty.applyMany head arguments) = applicationHead head := by
  induction arguments generalizing head with
  | nil => rfl
  | cons argument rest ih => exact ih (.application head argument)

private theorem nominal_ne_proxy (declaration : Resolved.DeclarationId) (arguments : List Ty) (inner : Ty) :
    Ty.nominal declaration arguments ≠ .proxy inner := by
  intro same
  have heads := congrArg applicationHead same
  simp [Ty.nominal, head_applyMany, applicationHead] at heads

private theorem nominal_ne_comptime (declaration : Resolved.DeclarationId) (arguments : List Ty) (inner : Ty) :
    Ty.nominal declaration arguments ≠ .comptime inner := by
  intro same
  have heads := congrArg applicationHead same
  simp [Ty.nominal, head_applyMany, applicationHead] at heads

private theorem scoped_proxy {context : Context} {variables : List TypeVarId} {type : Ty}
    (typed : TypeWellScoped context variables type) :
    ∀ inner, type = .proxy inner → TypeWellScoped context variables inner := by
  cases typed with
  | nominal declaration arguments _ _ _ => exact fun inner same => False.elim (nominal_ne_proxy declaration.id arguments inner same)
  | contractNominal declaration arguments _ _ _ => exact fun inner same => False.elim (nominal_ne_proxy declaration.id arguments inner same)
  | proxy inner => intro _ same; cases same; exact inner
  | _ => intro _ same; cases same

private theorem scoped_comptime {context : Context} {variables : List TypeVarId} {type : Ty}
    (typed : TypeWellScoped context variables type) :
    ∀ inner, type = .comptime inner → TypeWellScoped context variables inner := by
  cases typed with
  | nominal declaration arguments _ _ _ => exact fun inner same => False.elim (nominal_ne_comptime declaration.id arguments inner same)
  | contractNominal declaration arguments _ _ _ => exact fun inner same => False.elim (nominal_ne_comptime declaration.id arguments inner same)
  | comptime inner => intro _ same; cases same; exact inner
  | _ => intro _ same; cases same

private theorem mem_freeVariables_foldl_application_iff
    (metavariable : TypeVarId) (head : Ty) (arguments : List Ty) :
    metavariable ∈ (arguments.foldl Ty.application head).freeVariables ↔
      metavariable ∈ head.freeVariables ∨
        ∃ argument, argument ∈ arguments ∧
          metavariable ∈ argument.freeVariables := by
  induction arguments generalizing head with
  | nil => simp
  | cons argument arguments induction =>
      rw [List.foldl_cons, induction,
        SourceSemantics.mem_freeVariables_application_iff]
      simp only [List.mem_cons]
      constructor
      · rintro ((headMember | argumentMember) | tailMember)
        · exact Or.inl headMember
        · exact Or.inr ⟨argument, Or.inl rfl, argumentMember⟩
        · rcases tailMember with ⟨candidate, candidateMember, occurs⟩
          exact Or.inr ⟨candidate, Or.inr candidateMember, occurs⟩
      · rintro (headMember | ⟨candidate, candidateMember, occurs⟩)
        · exact Or.inl (Or.inl headMember)
        · rcases candidateMember with rfl | candidateMember
          · exact Or.inl (Or.inr occurs)
          · exact Or.inr ⟨candidate, candidateMember, occurs⟩

private theorem mem_freeVariables_nominal_iff
    {metavariable : TypeVarId} {declaration : Resolved.DeclarationId}
    {arguments : List Ty} :
    metavariable ∈ (Ty.nominal declaration arguments).freeVariables ↔
      ∃ argument, argument ∈ arguments ∧
        metavariable ∈ argument.freeVariables := by
  rw [Ty.nominal, Ty.applyMany,
    mem_freeVariables_foldl_application_iff]
  simp [Ty.freeVariables]

private theorem scoped_at_occurrence {original target : Context} {originalVariables variables : List TypeVarId}
    (substitution : TypeSystem.Substitution) {type : Ty}
    (originalTyped : TypeWellScoped original originalVariables type) :
    ∀ parameter, parameter ∈ type.freeVariables →
      TypeWellScoped target variables (substitution.apply type) →
      TypeWellScoped target variables ((substitution.lookup? parameter).getD (.variable parameter)) := by
  refine TypeWellScoped.rec
    (motive_1 := fun type _ => ∀ parameter, parameter ∈ type.freeVariables →
      TypeWellScoped target variables (substitution.apply type) →
      TypeWellScoped target variables ((substitution.lookup? parameter).getD (.variable parameter)))
    (motive_2 := fun types _ => ∀ type ∈ types, ∀ parameter, parameter ∈ type.freeVariables →
      TypeWellScoped target variables (substitution.apply type) →
      TypeWellScoped target variables ((substitution.lookup? parameter).getD (.variable parameter)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ originalTyped
  · intro metavariable bound parameter occurs typed
    have same : parameter = metavariable := by simpa [Ty.freeVariables] using occurs
    subst parameter
    exact typed
  · intro actual bound owned parameter occurs typed
    simp [Ty.freeVariables] at occurs
  · intro builtin parameter occurs; simp [Ty.freeVariables] at occurs
  · intro declaration arguments cataloged arity originalTyped ih parameter occurs typed
    obtain ⟨argument, member, occurs⟩ := mem_freeVariables_nominal_iff.mp occurs
    apply ih argument member parameter occurs
    rw [StructuralSubstitution.applyFlexible_nominal] at typed
    exact scoped_arguments typed _ (by rw [arguments_nominal]; exact List.mem_map.mpr ⟨argument, member, rfl⟩)
  · intro declaration arguments cataloged arity originalTyped ih parameter occurs typed
    obtain ⟨argument, member, occurs⟩ := mem_freeVariables_nominal_iff.mp occurs
    apply ih argument member parameter occurs
    rw [StructuralSubstitution.applyFlexible_nominal] at typed
    exact scoped_arguments typed _ (by rw [arguments_nominal]; exact List.mem_map.mpr ⟨argument, member, rfl⟩)
  · intro left right first second leftIH rightIH parameter occurs typed
    rcases (SourceSemantics.mem_freeVariables_function_iff).mp occurs with occurs | occurs
    · exact leftIH parameter occurs (typed.function_components _ _ rfl).1
    · exact rightIH parameter occurs (typed.function_components _ _ rfl).2
  · intro left right first second leftIH rightIH parameter occurs typed
    rcases (SourceSemantics.mem_freeVariables_product_iff).mp occurs with occurs | occurs
    · exact leftIH parameter occurs (typed.product_components _ _ rfl).1
    · exact rightIH parameter occurs (typed.product_components _ _ rfl).2
  · intro left right first second leftIH rightIH parameter occurs typed
    rcases (SourceSemantics.mem_freeVariables_mapping_iff).mp occurs with occurs | occurs
    · exact leftIH parameter occurs (typed.mapping_components _ _ rfl).1
    · exact rightIH parameter occurs (typed.mapping_components _ _ rfl).2
  · intro inner originalTyped ih parameter occurs typed
    exact ih parameter occurs (scoped_proxy typed _ rfl)
  · intro inner originalTyped ih parameter occurs typed
    exact ih parameter occurs (scoped_comptime typed _ rfl)
  · intro type member; cases member
  · intro head tail headTyped tailTyped headIH tailIH type member
    rcases List.mem_cons.mp member with rfl | member
    · exact headIH
    · exact tailIH type member

private theorem admissible_at_occurrence
    {original context : Context} {originalVariables : List TypeVarId}
    (substitution : TypeSystem.Substitution) {type : Ty} {parameter : TypeVarId}
    (originalTyped : TypeWellScoped original originalVariables type)
    (occurs : parameter ∈ type.freeVariables)
    (admitted : TypeAdmissible context (substitution.apply type)) :
    TypeAdmissible context ((substitution.lookup? parameter).getD (.variable parameter)) := by
  have replacementScoped := scoped_at_occurrence substitution originalTyped parameter occurs admitted.typeWellScoped
  cases residual : context.residualTypeVariables with
  | false =>
    exact ⟨admitted.binders, by simpa [admissibleTypeVariables, residual] using replacementScoped⟩
  | true =>
    exact StructuralSubstitution.TypeWellScoped.toAdmissibleOfResidual admitted.binders residual replacementScoped

/-- A successful match that leaves the right-hand type unchanged has only
left-hand variables in its domain. Each real occurrence in the formed pattern
recovers a formed replacement from the admitted matching result. -/
theorem matching_range_admissible
    {context : Context} {left right : Ty} {substitution : TypeSystem.Substitution}
    (leftFormed : TypeAdmissible context left)
    (rightFormed : TypeAdmissible context right)
    (success : Unification.unify [{ left, right }] = .ok substitution)
    (disjoint : ∀ metavariable, metavariable ∈ substitution.domain →
      metavariable ∉ right.freeVariables) :
    SubstitutionRangeAdmissible context substitution := by
  have unchanged : substitution.apply right = right :=
    Ty.apply_eq_self_of_domain_disjoint_freeVariables substitution right
      (fun metavariable member occurs => disjoint metavariable member occurs)
  have matched : substitution.apply left = right :=
    (Unification.unifyTypes_sound success).trans unchanged
  have solved := Unification.unifyTypes_solvedBelow
    ((Ty.variablesBelow_nextVariable left).weaken (Nat.le_max_left _ _))
    ((Ty.variablesBelow_nextVariable right).weaken (Nat.le_max_right _ _)) success
  intro metavariable replacement member
  have inDomain : metavariable ∈ substitution.domain :=
    List.mem_map.mpr ⟨(metavariable, replacement), member, rfl⟩
  obtain ⟨constraint, constraintMember, occurs⟩ :=
    Unification.unify_domain_origin success inDomain
  have same : constraint = { left, right } := by simpa using constraintMember
  subst constraint
  have occursLeft : metavariable ∈ left.freeVariables :=
    occurs.resolve_right (disjoint metavariable inDomain)
  have lookup := StructuralSubstitution.Substitution.lookup?_eq_some_of_mem_of_domain_nodup
    solved.domain_nodup member
  have recovered := admissible_at_occurrence substitution leftFormed.typeWellScoped
    occursLeft (matched.symm ▸ rightFormed)
  simpa only [lookup, Option.getD_some] using recovered

end Solcore.SourceSemantics.UnificationFormation

namespace Solcore.SourceSemantics.UnificationFormation
open Frontend TypeSystem

/-- Directional matching can be checked in the final context directly. Each
matched replacement occurs in the original formed pattern; its final type is
recovered from the actual final normalized source. No intermediate source
formation or whole-expression typing judgment is assumed. -/
theorem matching_normalized_range_admissible
    {context : Context} {left right : Ty}
    {substitution outer : TypeSystem.Substitution}
    (leftFormed : TypeAdmissible context left)
    (rightFormed : TypeAdmissible context (outer.apply right))
    (success : Unification.unify [{ left, right }] = .ok substitution)
    (disjoint : ∀ metavariable, metavariable ∈ substitution.domain →
      metavariable ∉ right.freeVariables) :
    ∀ metavariable replacement, (metavariable, replacement) ∈ substitution →
      TypeAdmissible context (outer.apply replacement) := by
  have unchanged : substitution.apply right = right :=
    Ty.apply_eq_self_of_domain_disjoint_freeVariables substitution right
      (fun metavariable member occurs => disjoint metavariable member occurs)
  have matched : substitution.apply left = right :=
    (Unification.unifyTypes_sound success).trans unchanged
  have solved := Unification.unifyTypes_solvedBelow
    ((Ty.variablesBelow_nextVariable left).weaken (Nat.le_max_left _ _))
    ((Ty.variablesBelow_nextVariable right).weaken (Nat.le_max_right _ _)) success
  intro metavariable replacement member
  have inDomain : metavariable ∈ substitution.domain :=
    List.mem_map.mpr ⟨(metavariable, replacement), member, rfl⟩
  obtain ⟨constraint, constraintMember, occurs⟩ :=
    Unification.unify_domain_origin success inDomain
  have same : constraint = { left, right } := by simpa using constraintMember
  subst constraint
  have occursLeft : metavariable ∈ left.freeVariables :=
    occurs.resolve_right (disjoint metavariable inDomain)
  have lookup := StructuralSubstitution.Substitution.lookup?_eq_some_of_mem_of_domain_nodup
    solved.domain_nodup member
  have composed : (outer.compose substitution).apply left = outer.apply right := by
    rw [Substitution.compose_apply, matched]
  have recovered := admissible_at_occurrence (outer.compose substitution) leftFormed.typeWellScoped
    occursLeft (composed.symm ▸ rightFormed)
  simpa only [Substitution.lookup?_compose, lookup, Option.getD_some] using recovered

end Solcore.SourceSemantics.UnificationFormation
