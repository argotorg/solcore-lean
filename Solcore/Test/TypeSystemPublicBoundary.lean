import Solcore.TypeSystem

set_option autoImplicit false

namespace Tests

example := @Solcore.TypeSystem.Ty.mem_freeVariables_application_iff
example := @Solcore.TypeSystem.Ty.mem_freeVariables_function_iff
example := @Solcore.TypeSystem.Ty.mem_freeVariables_product_iff
example := @Solcore.TypeSystem.Ty.mem_freeVariables_mapping_iff
example := @Solcore.TypeSystem.Substitution.lookup?_eq_none_iff_not_mem_domain
example := @Solcore.TypeSystem.Substitution.lookup?_eq_some_mem
example := @Solcore.TypeSystem.Substitution.domain_compose
example := @Solcore.TypeSystem.Substitution.mem_domain_compose_iff
example := @Solcore.TypeSystem.Substitution.domain_compose_nodup
example := @Solcore.TypeSystem.Substitution.mem_compose_iff
example := @Solcore.TypeSystem.Substitution.RangeAvoidsDomain
example := @Solcore.TypeSystem.Ty.apply_eq_self_of_domain_disjoint_freeVariables
example := @Solcore.TypeSystem.Substitution.SolvedBelow
example := @Solcore.TypeSystem.Substitution.SolvedBelow.empty
example := @Solcore.TypeSystem.Substitution.SolvedBelow.mono
example := @Solcore.TypeSystem.Substitution.SolvedBelow.lookup_range_outside_domain
example := @Solcore.TypeSystem.Substitution.SolvedBelow.apply_variables_below
example := @Solcore.TypeSystem.Substitution.SolvedBelow.apply_variables_outside_domain
example :=
  @Solcore.TypeSystem.Substitution.RangeAvoidsDomain.apply_variables_outside_older_domain
example := @Solcore.TypeSystem.Substitution.SolvedBelow.range_fixed
example := @Solcore.TypeSystem.Substitution.SolvedBelow.apply_idempotent
example := @Solcore.TypeSystem.Substitution.SolvedBelow.compose

private def solvedMetavariable : Solcore.TypeSystem.TypeVarId := ⟨0⟩

private def survivingMetavariable : Solcore.TypeSystem.TypeVarId := ⟨1⟩

private def nonemptySolvedSubstitution : Solcore.TypeSystem.Substitution :=
  [(solvedMetavariable, .variable survivingMetavariable)]

private theorem nonemptySolvedSubstitution_solved :
    Solcore.TypeSystem.Substitution.SolvedBelow
      nonemptySolvedSubstitution 2 := by
  apply Solcore.TypeSystem.Substitution.SolvedBelow.mono
  · decide
  · intro rangeVariable member
    have same : rangeVariable = survivingMetavariable := by
      simpa [Solcore.TypeSystem.Ty.freeVariables] using member
    subst rangeVariable
    decide
  · simp [Solcore.TypeSystem.Ty.freeVariables, solvedMetavariable,
      survivingMetavariable]

/-- A nonempty solved substitution is observationally idempotent on a type
containing both its replaced and surviving variables. -/
example :
    nonemptySolvedSubstitution.apply
        (nonemptySolvedSubstitution.apply
          (.product (.variable solvedMetavariable)
            (.variable survivingMetavariable))) =
      nonemptySolvedSubstitution.apply
        (.product (.variable solvedMetavariable)
          (.variable survivingMetavariable)) := by
  exact nonemptySolvedSubstitution_solved.apply_idempotent _

private def reverseSolvedSubstitution : Solcore.TypeSystem.Substitution :=
  [(survivingMetavariable, .variable solvedMetavariable)]

private theorem reverseSolvedSubstitution_solved :
    Solcore.TypeSystem.Substitution.SolvedBelow
      reverseSolvedSubstitution 2 := by
  apply Solcore.TypeSystem.Substitution.SolvedBelow.mono
  · decide
  · intro rangeVariable member
    have same : rangeVariable = solvedMetavariable := by
      simpa [Solcore.TypeSystem.Ty.freeVariables] using member
    subst rangeVariable
    decide
  · simp [Solcore.TypeSystem.Ty.freeVariables, solvedMetavariable,
      survivingMetavariable]

/-- Each side of the cyclic pair satisfies `SolvedBelow` independently. -/
example :
    Solcore.TypeSystem.Substitution.SolvedBelow reverseSolvedSubstitution 2 ∧
      Solcore.TypeSystem.Substitution.SolvedBelow nonemptySolvedSubstitution 2 :=
  ⟨reverseSolvedSubstitution_solved, nonemptySolvedSubstitution_solved⟩

/-- Two individually solved substitutions can compose to a range which
re-enters the combined domain when the cross invariant is absent. -/
example : reverseSolvedSubstitution.compose nonemptySolvedSubstitution =
    [(solvedMetavariable, .variable solvedMetavariable),
      (survivingMetavariable, .variable solvedMetavariable)] := by
  rfl

/-- The cyclic pair is rejected precisely by the explicit cross invariant. -/
example : ¬ Solcore.TypeSystem.Substitution.RangeAvoidsDomain
    reverseSolvedSubstitution nonemptySolvedSubstitution := by
  intro cross
  have outside := cross
    (metavariable := survivingMetavariable)
    (replacement := .variable solvedMetavariable)
    (by simp [reverseSolvedSubstitution]) solvedMetavariable
    (by simp [Solcore.TypeSystem.Ty.freeVariables])
  apply outside
  simp [nonemptySolvedSubstitution, Solcore.TypeSystem.Substitution.domain]

example := @Solcore.TypeSystem.InferState.fresh_substitution
example := @Solcore.TypeSystem.InferState.fresh_next
example := @Solcore.TypeSystem.InferState.instantiate_substitution
example := @Solcore.TypeSystem.InferState.instantiateDeclaration_substitution
example := @Solcore.TypeSystem.InferState.unify_next
example := @Solcore.TypeSystem.InferState.solve_next

end Tests
